// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.
// See the LICENSE file in the project root for more information.

#include "jitpch.h"

//------------------------------------------------------------------------------------------
// optForwardSubstitution: propagate definition trees to uses
//
// Notes:
//   If ssa defs pointed at their (only) use, we could streamline the walk we do here.
//
void Compiler::optForwardSubstitution()
{
    // Requires SSA to do anything useful.
    assert(fgSsaPassesCompleted == 1);

    for (BasicBlock* block = fgFirstBB; block != nullptr; block = block->bbNext)
    {
        compCurBB = block;
        for (Statement* stmt = block->firstStmt(); stmt != nullptr;)
        {
            Statement* next      = stmt->GetNextStmt();
            compCurStmt          = stmt;
            bool     madeChanges = false;
            unsigned flags       = 0;
            for (GenTree* tree = stmt->GetTreeList(); tree != nullptr; tree = tree->gtNext)
            {
                GenTree* newTree = optForwardSubstitution(block, stmt, tree, &flags);
                if (newTree != nullptr)
                {
                    flags |= (newTree->gtFlags & GTF_ALL_EFFECT);
                    madeChanges = true;
                }
                else
                {
                    flags |= (tree->gtFlags & GTF_ALL_EFFECT);
                }
            }

            if (madeChanges)
            {
                gtUpdateStmtSideEffects(stmt);

                // Don't remorph JTRUE/SWITCH for now, if they get folded things go wonky,
                // as fgMorphBlockStmt will modify the flow graph.
                //
                if (stmt->GetRootNode()->OperIs(GT_JTRUE, GT_SWITCH))
                {
                    gtSetStmtInfo(stmt);
                    fgSetStmtSeq(stmt);
                }
                else
                {
                    fgMorphBlockStmt(block, stmt DEBUGARG("optForwardSubstitution"));
                }
            }

            stmt = next;
        }
    }
}

//------------------------------------------------------------------------------------------
// optForwardSubstitution: propagate definition trees to uses
//
// Arguments:
//   block - current basic block
//   statement - current statement (belongs to block)
//   tree - current tree (part of statement)
//   flags - cumulative side effects of all tree nodes that evaluate before tree in
//     the current statement
//
// Returns:
//   nullptr if no changes made to tree
//   new/modified tree otherwise.
//
GenTree* Compiler::optForwardSubstitution(BasicBlock* block, Statement* statement, GenTree* tree, unsigned* flags)
{
    // We only modfy GT_LCL_VAR trees.
    if (!tree->OperIs(GT_LCL_VAR))
    {
        return nullptr;
    }

    GenTreeLclVar* const lclTree = tree->AsLclVar();

    // That are in SSA and are uses
    if (!lvaInSsa(lclTree->GetLclNum()) || ((lclTree->gtFlags & GTF_VAR_DEF) != 0) ||
        ((lclTree->gtFlags & GTF_VAR_USEASG) != 0))
    {
        return nullptr;
    }

    // That have an SSA def
    if (lclTree->GetSsaNum() == SsaConfig::RESERVED_SSA_NUM)
    {
        return nullptr;
    }

    LclVarDsc* const    lclDesc    = lvaGetDesc(lclTree);
    LclSsaVarDsc* const lclSsaDesc = lclDesc->lvPerSsaData.GetSsaDef(lclTree->GetSsaNum());

    // Heuristic: where the local has a single use
    if (lclSsaDesc->GetUseCount() != 1)
    {
        return nullptr;
    }

    // Where the definition is a tree
    GenTreeOp* const ssaAsgTree = lclSsaDesc->GetAssignment();

    if (ssaAsgTree == nullptr)
    {
        return nullptr;
    }

    // And the definition writes to the entire local
    if (!ssaAsgTree->gtGetOp1()->OperIs(GT_LCL_VAR))
    {
        return nullptr;
    }

    // Crossgen SPC: about 105K candidates at this point.
    //
    // Heuristic: where the local is defined in the same block
    //
    BasicBlock* const defBlock = lclSsaDesc->GetBlock();

    if (defBlock != block)
    {
        return nullptr;
    }

    GenTree* const defTree = ssaAsgTree->gtGetOp2();

    // Crossgen SPC: about 85K candidates at this point.
    //
    // Heuristic: the definition is not a PHI
    // Legality: catch arg must not be forwarded.
    //
    if (defTree->OperIs(GT_PHI, GT_CATCH_ARG))
    {
        return nullptr;
    }

    // Crossgen SPC: about 70K candidates at this point.
    //
    // Heuristic: only if def is in the immediately preceeding statement.
    // (this lets us bypass potentially costly legality checking, though
    // given the number of opportunities this passes up, we may want to
    // pay for it...)
    //
    Statement* prevStatement = statement->GetPrevStmt();

    if (prevStatement->GetRootNode() != ssaAsgTree)
    {
        return nullptr;
    }

    // Crossgen SPC: about 20K candidates at this point.
    //
    // Workaround: substituting into a return with mismatched
    // types can cause issues in LSRA with BITCAST & containment.
    // System.Numerics.Matrix3x2:get_Translation()
    //
    if (statement->GetRootNode()->OperIs(GT_RETURN))
    {
        if (statement->GetRootNode()->TypeGet() != defTree->TypeGet())
        {
            return nullptr;
        }
    }

    // Workaround: skip SIMD12 for now.
    // System.Numerics.Matrix4x4:CreateConstrainedBillboard
    //
    if (defTree->TypeGet() == TYP_SIMD12)
    {
        return nullptr;
    }

    // Workaround: don't propagate CALLs (probably good heuristic, too)
    // System.Runtime.InteropServices.WindowsRuntime.EventRegistrationTokenTable`1[__Canon][System.__Canon]:RemoveEventHandler(System.__Canon):this
    //
    if (defTree->OperIs(GT_CALL))
    {
        return nullptr;
    }

    // Legality: see if def tree can be moved to use
    // without reordering side effects.
    //
    // Should probably rework driver to walk the statement in
    // evaluation order, and accumulate any side effects/updated
    // locals as we go.
    //
    if ((*flags != 0) && (defTree->gtFlags & GTF_ALL_EFFECT) != 0)
    {
        return false;
    }

    // Workaround: don't propagate struct zeros
    // Microsoft.Diagnostics.Tracing.Extensions.ETWKernelControl:IsWin8orNewer():bool
    //
    if ((ssaAsgTree->TypeGet() == TYP_STRUCT) && (defTree->OperIs(GT_CNS_INT)))
    {
        return false;
    }

    GenTree**      lclTreeUse = nullptr;
    GenTree* const parent     = lclTree->gtGetParent(&lclTreeUse);

    if ((parent == nullptr) || (lclTreeUse == nullptr))
    {
        return nullptr;
    }

    // Workaround: don't propagate address-of-local into an indir unless we
    // are tracking byref and heap memory separately. This check is probably
    // not general enough yet... sigh.
    //
    // Seems to mainly impact small methods where during initial liveness we only see indirs with
    // unknown base addresses.
    //
    // FastSerialization.Deserializer:ReadFloat():float:this
    // System.Linq.Parallel.CancellationState:get_MergedCancellationToken():System.Threading.CancellationToken:this
    //
    if (byrefStatesMatchGcHeapStates && (defTree->IsLocalAddrExpr() != nullptr) && parent->OperIs(GT_IND))
    {
        return nullptr;
    }

    // Workaround: Similar check for assignments that initially looked like they might write to the heap.
    // System.Data.Common.SqlBooleanStorage:Aggregate(System.Int32[],int):System.Object:this
    //
    unsigned memorySsaNum;
    if (GetMemorySsaMap(GcHeap)->Lookup(statement->GetRootNode(), &memorySsaNum) &&
        (defTree->IsLocalAddrExpr() != nullptr))
    {
        return nullptr;
    }

    JITDUMP("Found FWD sub candidate: def [%06u] -> use [%06u]\n", dspTreeID(defTree), dspTreeID(tree));

#ifdef DEBUG
    if (verbose)
    {
        printf("found use of an entire single-use tree:\n");
        printf("---def---\n");
        gtDispTree(ssaAsgTree);
        printf("---in ---\n");
        gtDispTree(statement->GetRootNode());
        printf("\n");
    }
#endif // DEBUG

    // Make the tranformation.
    //
    assert(*lclTreeUse == lclTree);
    *lclTreeUse = defTree;

    // We no longer need the original def assignment, since this was the
    // one and only use.
    fgRemoveStmt(block, prevStatement);

    return defTree;
}
