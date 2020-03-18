// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.
// See the LICENSE file in the project root for more information.

#include "jitpch.h"

//------------------------------------------------------------------------------------------
// optForwardSubstitution: propagate definition trees to uses
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
            Statement* next  = stmt->GetNextStmt();
            compCurStmt      = stmt;
            bool madeChanges = false;
            for (GenTree* tree = stmt->GetTreeList(); tree != nullptr; tree = tree->gtNext)
            {
                GenTree* newTree = optForwardSubstitution(block, stmt, tree);
                if (newTree != nullptr)
                {
                    gtUpdateSideEffects(stmt, newTree);
                    madeChanges = true;
                }
            }

            // Update the evaluation order and the statement info if the stmt has been rewritten.
            if (madeChanges)
            {
                gtSetStmtInfo(stmt);
                fgSetStmtSeq(stmt);
            }

            stmt = next;
        }
    }
}

//------------------------------------------------------------------------------------------
// optForwardSubstitution: propagate definition trees to uses
//
// Consider: key off of ssa, if we link defs & uses, we can avoid a lot of IR walking.
//
GenTree* Compiler::optForwardSubstitution(BasicBlock* block, Statement* statement, GenTree* tree)
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

    // Heuristic: where the local is defined in the same block
    BasicBlock* const defBlock = lclSsaDesc->GetBlock();

    if (defBlock != block)
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

    GenTree* const defTree = ssaAsgTree->gtGetOp2();

    // Heuristic: where the definition is not a PHI
    if (defTree->OperIs(GT_PHI))
    {
        return nullptr;
    }

    JITDUMP("Found FWD sub candidate: def [%06u] -> use [%06u]\n", dspTreeID(defTree), dspTreeID(tree));

    return nullptr;
}
