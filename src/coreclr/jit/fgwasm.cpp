// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

#include "jitpch.h"
#ifdef _MSC_VER
#pragma hdrstop
#endif

#include "algorithm.h"

// WasmInterval
//
// Represents a BLOCK/END or LOOP/END
//
class WasmInterval
{
private:

    // m_chain refers to the conflict set member with the lowest m_start.
    // (for "trivial" singlton conflict sets m_chain will be `this`)
    WasmInterval* m_chain;

    // True index of start
    unsigned m_start;

    // True index of end; interval ends just before this block
    unsigned m_end;

    // Largest end index of any chained interval
    unsigned m_chainEnd;

    // true if this is a loop interval (extents cannot change)
    bool m_isLoop;

public:

    WasmInterval(unsigned start, unsigned end, bool isLoop)
        : m_chain(nullptr)
        , m_start(start)
        , m_end(end)
        , m_chainEnd(end)
        , m_isLoop(isLoop)
    {
        m_chain = this;
    }

    unsigned Start() const
    {
        return m_start;
    }

    unsigned End() const
    {
        return m_end;
    }

    unsigned ChainEnd() const
    {
        return m_chainEnd;
    }

    WasmInterval* Chain()
    {
        if (m_chain == this)
        {
            return this;
        }

        WasmInterval* chain = m_chain->Chain();
        m_chain             = chain;
        return chain;
    }

    bool IsLoop() const
    {
        return m_isLoop;
    }

    void SetChain(WasmInterval* c)
    {
        m_chain       = c;
        c->m_chainEnd = max(c->m_chainEnd, m_chainEnd);
    }

    static WasmInterval* NewRoot(Compiler* comp, unsigned numBlocks)
    {
        WasmInterval* root = new (comp, CMK_Wasm) WasmInterval(0, numBlocks, /* isLoop */ false);
        return root;
    }

    static WasmInterval* NewBlock(Compiler* comp, BasicBlock* start, BasicBlock* end)
    {
        WasmInterval* result =
            new (comp, CMK_Wasm) WasmInterval(start->bbPreorderNum, end->bbPreorderNum, /* isLoop */ false);
        return result;
    }

    static WasmInterval* NewLoop(Compiler* comp, BasicBlock* start, BasicBlock* end)
    {
        WasmInterval* result =
            new (comp, CMK_Wasm) WasmInterval(start->bbPreorderNum, end->bbPreorderNum, /* isLoop */ true);
        return result;
    }

    void Dump(bool chainExtent = false)
    {
        printf("[%03u,%03u]%s", m_start, chainExtent ? m_chainEnd : m_end, m_isLoop && !chainExtent ? " L" : "");

        if (m_chain != this)
        {
            printf(" --> ");
            m_chain->Dump(true);
        }
        else
        {
            printf("\n");
        }
    }
};

// Wasm Control Flow: naive algorithim (no if/else)
//
// * We consider only normal flow here, so eg callfinally just proceeds to the callfinally ret
// * Funclets have been identified and separated (though this is not strictly required). With
//   suitable RPO we can model funclet flow disjointly from main method flow
// * A prior pass has removed all irreducible flow.
//
// First we build a (normal flow) loop aware RPO.
//
// Each loop creates a Wasm LOOP/END. Since all loops are reducible and the body is compact the entry
// is the first lexical block and the extent is the lexically last block. The only back-edges are loop back edges.
//
// Each non-contiguous forward branch potentially creates a block. The only trick is figuring out how to
// arrange the block begins so we have proper nesting of Wasm blocks and Wasm loops.
//
// Since we have linear order of basic blocks, each non-contiguous forward branch can be characterized
// by the source and destination basic block indicies in the order. Eg [0, 4]. So an inteval begins at
// the start of the first block and ends at the start of the second.
//
// Each basic block start may be the end of some loops and /or a block. Or both. Note multiple
// blocks that end at the same point are not necessary.
//
// We walk the LaRPO from front to back.
// * If we see a loop head, we record a loop interval [x,y]. This extent cannot be altered.
// * If we see a noncontiguous branch (or switch), we record a block interval [a,b]. Here
//   b must remain fixed but we can increase a as needed to accomplish nesting.
//   For switches we will create multiple [a,b0], [a, b1]...
//
// If a forward interval ends on a block that already has an interval, we can ignore it.
// Because we're walking front to back, we will have already recorded an interval that starts
// earlier.
//
// We then scan the in non-decreasing start order, finding earlier intervals that contain the start
// of the current inteval but not the end. When we find one, the start of the current interval will
// need to increase so the earlier interval can nest inside. That is, if have a:[0, 4] and b:[2,6] we
// will need to emit them as b:[0,6], a[0,4].
//
// To save some time we also create a union-find like setup to identify the first interval in a set of
// conflicting intevals. Say we have a:[0,4] b:[2,6] c:[5,7]. When we see that b conflicts with a,
// we note 'a' as the conflict "chain" for b, and also track the conflict extent in a. Then when
// we scan intervals for c, we see it conflicts with the chain starting at a, and we add it to the chain.
// The net result is a:[0,4(7)], b:[2,6]-->a, c:[5,7]-->a.
//
// Then we order on their conflict chain start and end extent, and so would emit c:[0,7], b:[0,6], a:[0,4]
//
// We then can use the properly ordered and nested intervals to track the control stack depth as we
// traverse the blocks in loop-aware RPO order, and emit the proper Wasm control flow.
//
PhaseStatus Compiler::fgWasmControlFlow()
{
    // -----------------------------------------------
    // (1) Build loop-aware RPO layout
    //
    if (m_dfsTree == nullptr)
    {
        m_dfsTree = fgComputeDfs</* useProfile */ true>();
        m_loops   = FlowGraphNaturalLoops::Find(m_dfsTree);
    }
    else
    {
        assert(m_loops != nullptr);
    }

    // Bail out for now if there is any irreducible flow.
    // TODO: run the irreducible flow fixing before this.

    if (m_loops->ImproperLoopHeaders() > 0)
    {
        JITDUMP("\nThere are irreducible loops here, bailing\n");
        return PhaseStatus::MODIFIED_NOTHING;
    }

    JITDUMP("\nCreating loop-aware RPO\n");
    BasicBlock** const initialLayout = new (this, CMK_Wasm) BasicBlock*[m_dfsTree->GetPostOrderCount()];

    // TODO: extend this to cover all the funclets as well.
    //
    // The "DFS" we run above should skip from CALLFINALLY to CALLFINALLYRET, treat all funclet returns
    // as having no successor, and add each funclet entry as a DFS seed. This will give us a disjoint DFS
    // tree for the main method and each funclet, and the layout below will properly transform them all into
    // Wasm control flow.

    unsigned numHotBlocks  = 0;
    auto     addToSequence = [this, initialLayout, &numHotBlocks](BasicBlock* block) {
        // Skip funclets for now
        //
        if (block->hasHndIndex())
        {
            return;
        }

        JITDUMP("%03u " FMT_BB "\n", numHotBlocks, block->bbNum);

        // Set the block's ordinal.
        block->bbPreorderNum          = numHotBlocks;
        initialLayout[numHotBlocks++] = block;
    };

    fgVisitBlocksInLoopAwareRPO(m_dfsTree, m_loops, addToSequence);

    // -----------------------------------------------
    // (2) Build the intervals
    //
    // Allocate inteval and scratch vectors. We'll use the scratch vectort to keep track of
    // block intervals that end at a certain point.
    //
    jitstd::vector<WasmInterval*> intervals(getAllocator(CMK_Wasm));
    jitstd::vector<WasmInterval*> scratch(numHotBlocks, nullptr, getAllocator(CMK_Wasm));

    // Build the root
    //
    WasmInterval* root = WasmInterval::NewRoot(this, numHotBlocks);
    intervals.push_back(root);

    for (unsigned int cursor = 0; cursor < numHotBlocks; cursor++)
    {
        BasicBlock* const block = initialLayout[cursor];

        // See if we entered any loops
        //
        FlowGraphNaturalLoop* const loop = m_loops->GetLoopByHeader(block);

        if (loop != nullptr)
        {
            // Find the loop's lexical extent given our ordering
            // (maybe memoize this during loop finding...)
            //
            unsigned endCursor = cursor;
            while (loop->ContainsBlock(initialLayout[endCursor]) && (endCursor < numHotBlocks))
            {
                endCursor++;
            }

            // What if loop extends to end of method... hmmm
            //
            WasmInterval* const loopInterval = WasmInterval::NewLoop(this, block, initialLayout[endCursor]);

            // We assume here that a block is only the header of one loop.
            //
            intervals.push_back(loopInterval);
        }

        // Now see where block branches to...
        //

        if (block->isBBCallFinallyPair())
        {
            // We ignore these and treat them as if they fall through to the tail.
            // Since the tail cannot be a join we don't need a block.
            //
            continue;
        }

        for (BasicBlock* const succ : block->Succs())
        {
            unsigned const succNum = succ->bbPreorderNum;

            // We ignore back edges; they don't inspire blocks.
            //
            if (succNum <= cursor)
            {
                JITDUMP("Backedge " FMT_BB "[%u] -> " FMT_BB "[%u]\n", block->bbNum, cursor, succ->bbNum, succNum);

                // The backedge target should be a loop header.
                // (TODO: scan loop stack to verify the loop is on the stack?)
                //
                // Note we currently bail out way above if there are any irreducible loops.
                //
                assert(m_loops->GetLoopByHeader(succ) != nullptr);
                continue;
            }

            // Branch to next needs no block, unless this is a switch
            //
            if ((succNum == (cursor + 1)) && !block->KindIs(BBJ_SWITCH))
            {
                continue;
            }

            // Branch to cold block needs no block (presumably something EH related).
            // Eventually we need to case these out and handle them better.
            //
            if (succNum >= numHotBlocks)
            {
                continue;
            }

            // See if we already have a block that ends at this point and starts before.
            //
            WasmInterval* const existingBlock = scratch[succNum];

            if (existingBlock != nullptr)
            {
                // If so we don't need to track this branch.
                //
                JITDUMP("Subsumed " FMT_BB "[%u] -> " FMT_BB "[%u]\n", block->bbNum, cursor, succ->bbNum, succNum);
                assert(existingBlock->Start() <= cursor);
                continue;
            }

            // Non-contiguous, non-subsumed forward branch
            //
            WasmInterval* const branch = WasmInterval::NewBlock(this, block, initialLayout[succNum]);
            intervals.push_back(branch);

            // Remeber an interval end here
            //
            scratch[succNum] = branch;
        }
    }

    // Display the raw intervals...
    //
    JITDUMP("\n-------------- Initial set of wasm intervals\n");
    for (WasmInterval* iv : intervals)
    {
        JITDUMPEXEC(iv->Dump());
    }
    JITDUMP("--------------\n\n");

    // -----------------------------------------------
    // (3) Find intervals that overlap
    //
    // See if this interval conflicts with any other. If so,
    // add the interval to that intervals conflict set, and return
    // the conflict set for futher resolution.
    //
    auto resolve = [&intervals](WasmInterval* const iv, WasmInterval* const root) {
        for (WasmInterval* ip : intervals)
        {
            // We only need to consider intervals that start at the same point or earlier.
            //
            if (ip == iv)
            {
                break;
            }

            // We should be walking in non-decreasing start order
            //
            assert(ip->Start() <= iv->Start());

            // We may have chained this previous interval to another even earlier.
            // Find the head of that chain.
            //
            WasmInterval* const ic = ip->Chain();

            // See if the current interval starts at or inside
            // the chain interval and ends outside.
            //
            if ((ic->Start() <= iv->Start()) && (iv->Start() < ic->ChainEnd()))
            {
                // This interval starts in the middle of a prior one.
                // Does it end afterwards?
                //
                if (iv->End() > ic->ChainEnd())
                {
                    // Yes, add it to the conflict set
                    //
                    iv->SetChain(ic);
                    break;
                }
            }
        }
    };

    for (WasmInterval* iv : intervals)
    {
        resolve(iv, root);
    }

    JITDUMP("\n-------------- After finding conflicts\n");
    for (WasmInterval* iv : intervals)
    {
        JITDUMPEXEC(iv->Dump());
    }
    JITDUMP("--------------\n\n");

    // (4) Sort to put intervals in proper nesting order
    //
    // Sort by chain start index (ascending) then actual end index (descending) then isLoop
    //
    auto comesBefore = [](WasmInterval* i1, WasmInterval* i2) {
        WasmInterval* const p1 = i1->Chain();
        WasmInterval* const p2 = i2->Chain();

        // Lowest chain start
        //
        if (p1->Start() < p2->Start())
        {
            return true;
        }

        if (p2->Start() < p1->Start())
        {
            return false;
        }

        // Highest end
        //
        if (i1->End() > i2->End())
        {
            return true;
        }

        if (i2->End() > i1->End())
        {
            return false;
        }

        // Tiebreaker
        //
        if (i1->IsLoop())
        {
            return true;
        }

        return false;
    };

    jitstd::sort(intervals.begin(), intervals.end(), comesBefore);

    JITDUMP("\n-------------- After sorting\n");
    for (WasmInterval* iv : intervals)
    {
        JITDUMPEXEC(iv->Dump());
    }
    JITDUMP("--------------\n\n");

    // (5) Create the wasm control flow operations
    //
    // Show (roughly) what the WASM control flow looks like
    //
    ArrayStack<WasmInterval*> activeIntervals(getAllocator(CMK_Wasm));
    unsigned                  wasmCursor = 0;
    activeIntervals.Push(root);

    for (unsigned int cursor = 0; cursor < numHotBlocks; cursor++)
    {
        BasicBlock* const block = initialLayout[cursor];

        // Close intervals that end here (at most two, block and/or loop)
        //
        while (activeIntervals.Top()->End() == cursor)
        {
            JITDUMP("END    (%u)%s\n", activeIntervals.Top()->End(), activeIntervals.Top()->IsLoop() ? " LOOP" : "");
            activeIntervals.Pop();
        }

        // Open intervals that start here or earlier
        //
        if (wasmCursor < intervals.size())
        {
            WasmInterval* interval = intervals[wasmCursor];
            WasmInterval* chain    = interval->Chain();

            while (chain->Start() <= cursor)
            {
                if (interval == root)
                {
                    JITDUMP("ENTER\n");
                }
                else
                {
                    JITDUMP("%s (%u)\n", interval->IsLoop() ? "LOOP " : "BLOCK", interval->End());
                }

                wasmCursor++;
                activeIntervals.Push(interval);

                if (wasmCursor >= intervals.size())
                {
                    break;
                }

                interval = intervals[wasmCursor];
                chain    = interval->Chain();
            }
        }

        JITDUMP("  " FMT_BB "\n", block->bbNum);

        // Compute the depth of the block ending at targetNum
        // or (if isBackege) ths loop starting at targetNum
        //
        auto findDepth = [&activeIntervals](unsigned targetNum, bool isBackedge, unsigned& match) {
            int const h = activeIntervals.Height();

            for (int i = 0; i < h; i++)
            {
                WasmInterval* const ii = activeIntervals.Top(i);
                match                  = 0;

                if (isBackedge)
                {
                    // loops bind to start
                    match = ii->Start();
                }
                else
                {
                    // blocks bind to end
                    match = ii->End();
                }

                if ((match == targetNum) && (isBackedge == ii->IsLoop()))
                {
                    return i;
                }
            }

            JITDUMP("Could not find %u%s in active control stack\n", targetNum, isBackedge ? " (backedge)" : "");
            assert(!"Can't find target in control stack");

            return ~0;
        };

        switch (block->GetKind())
        {
            case BBJ_RETURN:
            case BBJ_EHFINALLYRET:
            case BBJ_EHFAULTRET:
            case BBJ_EHFILTERRET:
            case BBJ_EHCATCHRET:
            {
                JITDUMP("RETURN\n");
                break;
            }

            case BBJ_THROW:
            {
                JITDUMP("THROW\n");
                break;
            }

            case BBJ_CALLFINALLY:
            {
                // no-op (implied fall through to tail, if it exists)
                //
                if (!block->isBBCallFinallyPair())
                {
                    JITDUMP("UNREACHED\n");
                }
                break;
            }

            case BBJ_ALWAYS:
            case BBJ_CALLFINALLYRET:
            {
                unsigned const succNum = block->GetTarget()->bbPreorderNum;

                if (succNum == (cursor + 1))
                {
                    JITDUMP("FALLTHROUGH\n");
                }
                else if (succNum < numHotBlocks)
                {
                    bool const isBackedge = succNum <= cursor;
                    unsigned   blockNum   = 0;
                    unsigned   depth      = findDepth(succNum, isBackedge, blockNum);
                    JITDUMP("BR %d (%u)%s\n", depth, blockNum, isBackedge ? "be" : "");
                }

                break;
            }

            case BBJ_COND:
            {
                const unsigned trueNum  = block->GetTrueTarget()->bbPreorderNum;
                const unsigned falseNum = block->GetFalseTarget()->bbPreorderNum;

                if (trueNum == falseNum)
                {
                    JITDUMP("FALLTHROUGH\n");
                    break;
                }

                // If the true target is the next block, we are in a bind, since
                // we need to branch to it, but may not have induced a block.
                //
                // We could anticipate this above and induce a block like we do for switches.
                //
                // Or we can just invert the branch condition here; I think this should be viable.
                // (eg invoke the core part of optOptimizePostLayout).
                //
                const bool invertCondition = trueNum == (cursor + 1);

                if (invertCondition)
                {
                    // TODO: induce a block and avoid this case, or actually modify the IR
                    //
                    JITDUMP("FALLTHROUGH-inv\n");
                }
                else if (trueNum < numHotBlocks)
                {
                    bool const isBackedge = trueNum <= cursor;
                    unsigned   blockNum   = 0;
                    unsigned   depth      = findDepth(trueNum, isBackedge, blockNum);
                    JITDUMP("BR_IF %d (%u)%s\n", depth, blockNum, isBackedge ? "be" : "");
                }

                if (falseNum == (cursor + 1))
                {
                    JITDUMP("FALLTHROUGH\n");
                }
                else if (falseNum < numHotBlocks)
                {
                    bool const isBackedge = falseNum <= cursor;
                    unsigned   blockNum   = 0;
                    unsigned   depth      = findDepth(falseNum, isBackedge, blockNum);
                    JITDUMP("BR%s %d (%u)%s\n", invertCondition ? "_IF-inv" : "", depth, blockNum,
                            isBackedge ? "be" : "");
                }

                break;
            }

            case BBJ_SWITCH:
            {
                BBswtDesc* const desc      = block->GetSwitchTargets();
                unsigned const   caseCount = desc->GetCaseCount();

                // We expect lower has made the default case check explicit
                assert(!desc->HasDefaultCase());

                if (caseCount == 0)
                {
                    JITDUMP("FALLTHROUGH\n");
                    break;
                }

                JITDUMP("BR_TABLE");

                for (unsigned caseNum = 0; caseNum < caseCount; caseNum++)
                {
                    BasicBlock* const caseTarget    = desc->GetCase(caseNum)->getDestinationBlock();
                    unsigned const    caseTargetNum = caseTarget->bbPreorderNum;

                    // We should have forced a block in this case, see above
                    assert(caseTargetNum != (cursor + 1));

                    if (caseTargetNum < numHotBlocks)
                    {
                        bool const isBackedge = caseTargetNum <= cursor;
                        unsigned   blockNum   = 0;
                        unsigned   depth      = findDepth(caseTargetNum, isBackedge, blockNum);
                        JITDUMP("%s %d (%u)%s\n", caseNum > 0 ? "," : "", depth, blockNum, isBackedge ? "be" : "");
                    }
                }

                JITDUMP("\n");
                break;
            }

            default:
            {
                assert(!"Unexpected block kind");
            }
        }

        JITDUMP("\n");
    }

    // Ditto but in dot markup
    //
    activeIntervals.Reset();
    activeIntervals.Push(root);
    wasmCursor = 0;
    JITDUMP("\ndigraph WASM {\n");

    for (unsigned int cursor = 0; cursor < numHotBlocks; cursor++)
    {
        BasicBlock* const block = initialLayout[cursor];

        // Close intervals that end here (at most two, block and/or loop)
        //
        while (activeIntervals.Top()->End() == cursor)
        {
            JITDUMP("  }\n");
            activeIntervals.Pop();
        }

        // Open intervals that start here
        //
        if (wasmCursor < intervals.size())
        {
            WasmInterval* interval = intervals[wasmCursor];
            WasmInterval* chain    = interval->Chain();

            if (chain->Start() <= cursor)
            {

                if (interval == root)
                {
                    wasmCursor++;
                }
                else
                {
                    while (chain->Start() <= cursor)
                    {
                        JITDUMP("  subgraph cluster_%u_%u%s {\n", chain->Start(), interval->End(),
                                interval->IsLoop() ? "_loop" : "");

                        FlowGraphNaturalLoop* const loop = m_loops->GetLoopByHeader(block);

                        if (loop != nullptr)
                        {
                            JITDUMP("    color=red;\n");
                        }
                        else
                        {
                            JITDUMP("    color=black;\n");
                        }

                        wasmCursor++;
                        activeIntervals.Push(interval);

                        if (wasmCursor >= intervals.size())
                        {
                            break;
                        }

                        interval = intervals[wasmCursor];
                        chain    = interval->Chain();
                    }
                }
            }
        }

        JITDUMP("    " FMT_BB ";\n", block->bbNum);
    }

    // Now list all the branches

    for (unsigned int cursor = 0; cursor < numHotBlocks; cursor++)
    {
        BasicBlock* const block = initialLayout[cursor];

        if (block->KindIs(BBJ_CALLFINALLY))
        {
            if (block->isBBCallFinallyPair())
            {
                JITDUMP("   " FMT_BB " -> " FMT_BB " [style=dotted];\n", block->bbNum, block->Next()->bbNum);
            }
        }
        else
        {
            for (BasicBlock* const succ : block->Succs())
            {
                JITDUMP("   " FMT_BB " -> " FMT_BB ";\n", block->bbNum, succ->bbNum);
            }
        }
    }

    JITDUMP("}\n");

    return PhaseStatus::MODIFIED_NOTHING;
}
