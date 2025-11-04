// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

#include "jitpch.h"
#ifdef _MSC_VER
#pragma hdrstop
#endif

// WasmInterval
//
// Represents a BLOCK/END or LOOP/END
//
class WasmInterval
{
private:

    WasmInterval* m_next;
    WasmInterval* m_prev;

    // m_chain refers to the conflict set member with the lowest m_start.
    // (for "trivial" conflict sets m_chain will be `this`)
    //
    WasmInterval* m_chain;

    // Most nested loop containing this interval, or nullptr.
    //
    FlowGraphNaturalLoop* m_containingLoop;

    // True index of start
    unsigned m_start;

    // True index of end; interval ends just before this block
    unsigned m_end;

    // Smallest start index of any chained interval
    unsigned m_chainStart;

    // Largest end index of any chained interval
    unsigned m_chainEnd;

    // true if this is a loop interval (extents cannot change)
    //
    bool m_isLoop;

public:

    WasmInterval(unsigned start, unsigned end, FlowGraphNaturalLoop* loop, bool isLoop)
        : m_next(nullptr)
        , m_prev(nullptr)
        , m_chain(nullptr)
        , m_containingLoop(loop)
        , m_start(start)
        , m_end(end)
        , m_chainStart(start)
        , m_chainEnd(end)
        , m_isLoop(isLoop)
    {
        m_chain = this;
    }

    unsigned Start()
    {
        return m_start;
    }
    unsigned End()
    {
        return m_end;
    }
    unsigned ChainStart()
    {
        return m_chainStart;
    }
    unsigned ChainEnd()
    {
        return m_chainEnd;
    }

    WasmInterval* Next()
    {
        return m_next;
    }
    WasmInterval* Prev()
    {
        return m_prev;
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

    bool IsLoop()
    {
        return m_isLoop;
    }
    FlowGraphNaturalLoop* ContainingLoop()
    {
        return m_containingLoop;
    }

    void InsertAfter(WasmInterval* i)
    {
        WasmInterval* const iNext = i->Next();
        i->m_next                 = this;
        m_next                    = iNext;

        this->m_prev = i;
        if (iNext != nullptr)
        {
            iNext->m_prev = this;
        }
    }

    void SetChain(WasmInterval* c)
    {
        m_chain         = c;
        c->m_chainStart = min(c->m_chainStart, m_chainStart);
        c->m_chainEnd   = max(c->m_chainEnd, m_chainEnd);
    }

    static WasmInterval* NewRoot(Compiler* comp, unsigned numBlocks)
    {
        WasmInterval* root =
            new (comp, CMK_Wasm) WasmInterval(0, numBlocks, /* containingLoop */ nullptr, /* isLoop */ false);
        return root;
    }

    static WasmInterval* NewBlock(Compiler* comp, BasicBlock* start, BasicBlock* end, FlowGraphNaturalLoop* loop)
    {
        WasmInterval* result =
            new (comp, CMK_Wasm) WasmInterval(start->bbPreorderNum, end->bbPreorderNum, loop, /* isLoop */ false);
        return result;
    }

    static WasmInterval* NewLoop(Compiler* comp, BasicBlock* start, BasicBlock* end, FlowGraphNaturalLoop* loop)
    {
        WasmInterval* result =
            new (comp, CMK_Wasm) WasmInterval(start->bbPreorderNum, end->bbPreorderNum, loop, /* isLoop */ true);
        return result;
    }

    void Dump(bool chainExtent = false)
    {
        printf("[%03u,%03u]%s", chainExtent ? m_chainStart : m_start, chainExtent ? m_chainEnd : m_end,
               m_isLoop && !chainExtent ? " L" : "");

        if (!chainExtent && (m_containingLoop != nullptr))
        {
            printf(" in L%02u", m_containingLoop->GetIndex());
        }

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

// WASM Control Flow
//
// Naive algorithim (no if/else)
//
// Each loop creates a LOOP/END. Since loops are reducible and the body is compact the entry is the first lexical block
// and the extent is the lexically last block (or, the end is at the start of the next block).
// The only back-edges are loop back edges.
//
// Each non-contiguous forward branch creates a block end. The trick is figuring out how to
// arrange the block begins so we have proper nesting of wasm blocks and wasm loops.
//
// Since we have linear order of basic blocks, each non-contiguous forward branch can be characterized
// by the source and destination basic block indicies in the order. Eg [0, 4].
//
// Each basic block (begin) may be the end of some loops and /or a block. Or both. Note multiple
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
// We sort the intervals first by starting offset, then by ending offset. For each adjustable interval [a,b],
// we see if any other interval starts after a and ends after b (say [c,d]). If so, we modify that interval
// to be [a,d], placing it in the ordering as appropriate... repeat until closure.
//
// We then annotate each interval with its nesting depth and associate it with the blocks in question.
// During codegen we use this to emit the right opcodes and depth values.
//
PhaseStatus Compiler::fgWasmControlFlow()
{
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

    JITDUMP("\nCreating loop-aware RPO\n");
    BasicBlock** const initialLayout = new (this, CMK_Wasm) BasicBlock*[m_dfsTree->GetPostOrderCount()];

    unsigned numHotBlocks  = 0;
    auto     addToSequence = [this, initialLayout, &numHotBlocks](BasicBlock* block) {
        // Skip funclets
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

    // (2) Build the intervals
    //
    // Build the root
    //
    WasmInterval* root = WasmInterval::NewRoot(this, numHotBlocks);
    WasmInterval* last = root;
    JITDUMPEXEC(root->Dump());

    // Keep track of containing loops
    //
    FlowGraphNaturalLoop* containingLoop = nullptr;

    // Allocate a scratch vector. Initially we'll use it to keep track of
    // block intervals that end at a certain point.
    //
    jitstd::vector<WasmInterval*> intervals(numHotBlocks, nullptr, getAllocator(CMK_Wasm));

    for (unsigned int cursor = 0; cursor < numHotBlocks; cursor++)
    {
        BasicBlock* const block = initialLayout[cursor];

        // See if we entered or exited any loops
        //
        FlowGraphNaturalLoop* const loop = m_loops->GetLoopByHeader(block);

        if (loop != nullptr)
        {
            // Loop header block. Verify loop nesting is as expected
            //
            assert(containingLoop == loop->GetParent());

            // Find the loop's lexical extent given our ordering
            //
            unsigned endCursor = cursor;
            while (loop->ContainsBlock(initialLayout[endCursor]) && (endCursor < numHotBlocks))
            {
                endCursor++;
            }

            WasmInterval* const loopInterval =
                WasmInterval::NewLoop(this, block, initialLayout[endCursor - 1], containingLoop);
            JITDUMPEXEC(loopInterval->Dump());

            // We assume here that a given block is only the header of one loop.
            //
            loopInterval->InsertAfter(last);
            last           = loopInterval;
            containingLoop = loop;
        }
        else
        {
            // Non-loop header block. We may have exited one or more loops.
            //
            while ((containingLoop != nullptr) && !containingLoop->ContainsBlock(block))
            {
                containingLoop = containingLoop->GetParent();
            }
        }

        // Now see where block branches to...
        //
        for (BasicBlock* const succ : block->Succs())
        {
            unsigned const succNum = succ->bbPreorderNum;

            // We ignore back edges; they don't inspire blocks.
            //
            if (succNum <= cursor)
            {
                JITDUMP("Backedge " FMT_BB "[%u] -> " FMT_BB "[%u]\n", block->bbNum, cursor, succ->bbNum, succNum);

                // The backedge target should be a loop header.
                // (todo: scan loop stack to verify)
                // (Unless we have not yet cleared up irreducible loops).
                //
                assert((m_loops->ImproperLoopHeaders() > 0) || (m_loops->GetLoopByHeader(succ) != nullptr));
                continue;
            }

            // Branch to next needs no block
            //
            if (succNum == (cursor + 1))
            {
                continue;
            }

            // Branch to cold block needs no block (presumably a finally invoke?)
            //
            if (succNum >= numHotBlocks)
            {
                continue;
            }

            // See if we already have a block that ends at this point and starts before.
            //
            WasmInterval* const existingBlock = intervals[succNum];

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
            WasmInterval* const branch = WasmInterval::NewBlock(this, block, initialLayout[succNum], containingLoop);
            JITDUMPEXEC(branch->Dump());

            branch->InsertAfter(last);
            intervals[succNum] = branch;
            last               = branch;
        }
    }

    // Display the raw intervals...
    //
    JITDUMP("\n-------------- Initial set of wasm intervals\n");
    for (WasmInterval* iv = root; iv != nullptr; iv = iv->Next())
    {
        JITDUMPEXEC(iv->Dump());
    }
    JITDUMP("--------------\n\n");

    // See if this interval conflicts with any other. If so,
    // add the interval to that intervals conflict set, and return
    // the conflict set for futher resolution.
    //
    auto resolve = [](WasmInterval* const iv, WasmInterval* const root) {
        JITDUMP("Resolve ");
        JITDUMPEXEC(iv->Dump());

        for (WasmInterval* ip = root; ip != iv; ip = ip->Next())
        {
            // We should be walking in non-decreasing start order
            //
            assert(ip->Start() <= iv->Start());

            // We may have chained the previous interval to another even earlier.
            // Find the head of that chain.
            //
            WasmInterval* const ic = ip->Chain();

            // See if the current (possibly extended) interval starts at or inside
            // the chain interval and ends outside.
            //
            if ((ic->ChainStart() <= iv->Start()) && (iv->Start() < ic->ChainEnd()))
            {
                JITDUMP("Start nested in ");
                JITDUMPEXEC(ic->Dump());

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

        JITDUMP("\n");
    };

    // Find conflict sets... note this is potentially
    // quadratic, but union find should prevent that.
    //
    for (WasmInterval* iv = root; iv != nullptr; iv = iv->Next())
    {
        resolve(iv, root);
    }

    JITDUMP("\n-------------- After finding conflicts\n");
    for (WasmInterval* iv = root; iv != nullptr; iv = iv->Next())
    {
        JITDUMPEXEC(iv->Dump());
    }
    JITDUMP("--------------\n\n");

    return PhaseStatus::MODIFIED_NOTHING;
}
