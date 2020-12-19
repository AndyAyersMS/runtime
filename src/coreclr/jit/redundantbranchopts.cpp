// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

#include "jitpch.h"

//------------------------------------------------------------------------
// optRedundantBranches: try and optimize redundant branches in the method
//
// Returns:
//   PhaseStatus indicating if anything changed.
//
PhaseStatus Compiler::optRedundantBranches()
{
    INDEBUG(if (verbose) fgDispBasicBlocks());

    // We attempt this "bottom up" so walk the flow graph in postorder.
    //
    bool madeChanges = false;

    for (unsigned i = fgDomBBcount; i > 0; --i)
    {
        BasicBlock* const block = fgBBInvPostOrder[i];

        // Upstream phases like optOptimizeBools may remove blocks
        // that are referenced in bbInvPosOrder.
        //
        if ((block->bbFlags & BBF_REMOVED) != 0)
        {
            continue;
        }

        // We currently can optimize some BBJ_CONDs.
        //
        if (block->bbJumpKind == BBJ_COND)
        {
            madeChanges |= optRedundantBranch(block);
        }
    }

    if (madeChanges)
    {
        INDEBUG(if (verbose) fgDispBasicBlocks());
    }

    return madeChanges ? PhaseStatus::MODIFIED_EVERYTHING : PhaseStatus::MODIFIED_NOTHING;
}

//------------------------------------------------------------------------
// optRedundantBranch: try and optimize a possibly redundant branch
//
// Arguments:
//   block - block with branch to optimize
//
// Returns:
//   True if the branch was optimized.
//
bool Compiler::optRedundantBranch(BasicBlock* const block)
{
    Statement* const stmt = block->lastStmt();

    if (stmt == nullptr)
    {
        return false;
    }

    GenTree* const jumpTree = stmt->GetRootNode();

    if (!jumpTree->OperIs(GT_JTRUE))
    {
        return false;
    }

    GenTree* const tree = jumpTree->AsOp()->gtOp1;

    if (!(tree->OperKind() & GTK_RELOP))
    {
        return false;
    }

    // Walk up the dom tree and see if any dominating block has branched on
    // exactly this tree's VN...
    //
    BasicBlock* prevBlock   = block;
    BasicBlock* domBlock    = block->bbIDom;
    int         relopValue  = -1;
    bool        wasThreaded = false;

    if (domBlock == nullptr)
    {
        return false;
    }

    while (domBlock != nullptr)
    {
        if (prevBlock == block)
        {
            JITDUMP("\nChecking " FMT_BB " for redundancy\n", block->bbNum);
        }

        // Check the current dominator
        //
        if (domBlock->bbJumpKind == BBJ_COND)
        {
            Statement* const domJumpStmt = domBlock->lastStmt();
            GenTree* const   domJumpTree = domJumpStmt->GetRootNode();
            assert(domJumpTree->OperIs(GT_JTRUE));
            GenTree* const domCmpTree = domJumpTree->AsOp()->gtGetOp1();

            if (domCmpTree->OperKind() & GTK_RELOP)
            {
                // See if there are paths from the dominating relop that
                // would bring just the true or false value to the dominated relop
                //
                BasicBlock* const trueSuccessor  = domBlock->bbJumpDest;
                BasicBlock* const falseSuccessor = domBlock->bbNext;
                const bool        trueReaches    = fgReachable(trueSuccessor, block);
                const bool        falseReaches   = fgReachable(falseSuccessor, block);

                if (!trueReaches && !falseReaches)
                {
                    // No apparent path from the dominating compare.
                    //
                    // If domBlock or block is in an EH handler we may fail to find a path.
                    // Just ignore those cases.
                    //
                    // No point in looking further up the tree.
                    //
                    break;
                }

                if (trueReaches != falseReaches)
                {
                    // Just one outcome reaches. See if we can deduce the value of tree.
                    //
                    const RelopImplicationResult rir = optRelopImpliesRelop(domCmpTree, trueReaches, tree);

                    if (rir != RelopImplicationResult::RIR_UNKNOWN)
                    {
                        relopValue = (rir == RelopImplicationResult::RIR_TRUE) ? 1 : 0;
                        JITDUMP("%s path from " FMT_BB " reaches " FMT_BB " and so relop must be %s\n",
                                trueReaches ? "jump" : "fall-through", domBlock->bbNum, block->bbNum,
                                relopValue ? "true" : "false");
                        break;
                    }
                }

                if (trueReaches && falseReaches)
                {
                    // Both dominating compare outcomes reach the current block so we can't directly
                    // infer the value of the relop.
                    //
                    // However we may be able to update the flow from block's predecessors so they
                    // bypass block and instead transfer control to jump's successors (aka jump threading).
                    //
                    wasThreaded = optJumpThread(block, domBlock);

                    if (wasThreaded)
                    {
                        return true;
                    }
                }
            }
        }

        // Keep looking higher up in the tree
        //
        prevBlock = domBlock;
        domBlock  = domBlock->bbIDom;
    }

    // Did we determine the relop value via dominance checks? If so, optimize.
    //
    if (relopValue == -1)
    {
        return false;
    }

    // Bail out if tree is has certain side effects
    //
    // Note we really shouldn't get here if the tree has non-exception effects,
    // as they should have impacted the value number.
    //
    // (TODO: preserve side effects like AP does)
    //
    if ((tree->gtFlags & GTF_SIDE_EFFECT) != 0)
    {
        // Bail if there is a non-exception effect.
        //
        if ((tree->gtFlags & GTF_SIDE_EFFECT) != GTF_EXCEPT)
        {
            JITDUMP("Current relop has non-exception side effects, so we won't optimize\n");
            return false;
        }

        // Be conservative if there is an exception effect and we're in an EH region
        // as we might not model the full extent of EH flow.
        //
        if (block->hasTryIndex())
        {
            JITDUMP("Current relop has exception side effect and is in a try, so we won't optimize\n");
            return false;
        }
    }

    JITDUMP("\nRedundant branch opt in " FMT_BB ":\n", block->bbNum);

    tree->ChangeOperConst(GT_CNS_INT);
    tree->AsIntCon()->gtIconVal = relopValue;

    fgMorphBlockStmt(block, stmt DEBUGARG(__FUNCTION__));
    return true;
}

//------------------------------------------------------------------------
// optJumpThread: try and bypass the current block by rerouting
//   flow from predecessors directly to successors.
//
// Arguments:
//   block - block with branch to optimize
//   domBlock - a dominating block that has an equivalent branch
//
// Returns:
//   True if the branch was optimized.
//
// Notes:
//
//    A       B          A     B
//     \     /           |     |
//      \   /            |     |
//      block     ==>    |     |
//      /   \            |     |
//     /     \           |     |
//    C       D          C     D
//
bool Compiler::optJumpThread(BasicBlock* const block, BasicBlock* const domBlock)
{
    assert(block->bbJumpKind == BBJ_COND);
    assert(domBlock->bbJumpKind == BBJ_COND);

    // If the dominating block is not the immediate dominator
    // we would need to duplicate a lot of code to thread
    // the jumps. Pass for now.
    //
    if (domBlock != block->bbIDom)
    {
        return false;
    }

    JITDUMP("Both successors of IDom " FMT_BB " reach " FMT_BB " -- attemting jump threading\n", domBlock->bbNum,
            block->bbNum);

    // Since flow is going to bypass block, make sure there
    // is nothing in block that can cause a side effect.
    //
    // Note we neglect PHI assignments. This reflects a general lack of
    // SSA update abilities in the jit. We really should update any uses
    // of PHIs defined here with the corresponding PHI input operand.
    //
    // TODO: if block has side effects, for those predecessors that are
    // favorable (ones that don't reach block via a critical edge), consider
    // duplicating block's IR into the predecessor. This is the jump threading
    // analog of the optimization we encourage via fgOptimizeUncondBranchToSimpleCond.
    //
    Statement* const lastStmt = block->lastStmt();

    for (Statement* stmt = block->FirstNonPhiDef(); stmt != nullptr; stmt = stmt->GetNextStmt())
    {
        GenTree* const tree = stmt->GetRootNode();

        // We can ignore exception side effects in the jump tree.
        //
        // They are covered by the exception effects in the dominating compare.
        // We know this because the VNs match and they encode exception states.
        //
        if ((tree->gtFlags & GTF_SIDE_EFFECT) != 0)
        {
            if (stmt == lastStmt)
            {
                assert(tree->OperIs(GT_JTRUE));
                if ((tree->gtFlags & GTF_SIDE_EFFECT) == GTF_EXCEPT)
                {
                    // However, be conservative if block is in a try as we might not
                    // have a full picture of EH flow.
                    //
                    if (!block->hasTryIndex())
                    {
                        // We will ignore the side effect on this tree.
                        //
                        continue;
                    }
                }
            }

            JITDUMP(FMT_BB " has side effects; no threading\n", block->bbNum);
            return false;
        }
    }

    // Figure out whether we can infer the value of block's relop if
    // we know the value of the domBlocks' relop.
    //
    GenTree* const               domTree    = domBlock->lastStmt()->GetRootNode()->AsOp()->gtGetOp1();
    GenTree* const               blockTree  = block->lastStmt()->GetRootNode()->AsOp()->gtGetOp1();
    const RelopImplicationResult rirIfTrue  = optRelopImpliesRelop(domTree, true, blockTree);
    const RelopImplicationResult rirIfFalse = optRelopImpliesRelop(domTree, false, blockTree);

    // If we can't infer anything, then no point continuing.
    //
    if ((rirIfTrue == RIR_UNKNOWN) && (rirIfFalse == RIR_UNKNOWN))
    {
        JITDUMP(" Can't infer anything about relop; no threading\n");
        return false;
    }

    // Figure out where control flow from block will end up, given a true/false value
    // for the dominating predicate.
    //
    // Note we may only be able to infer results for one of the paths coming out of
    // dom block, and the inferred value of the second relop along that path may be
    // different than the value of the first relop.
    //
    BasicBlock* trueTarget   = nullptr;
    BasicBlock* falseTarget  = nullptr;
    const char* trueMessage  = "unknown";
    const char* falseMessage = "unknown";

    if (rirIfTrue != RIR_UNKNOWN)
    {
        trueTarget  = (rirIfTrue == RIR_TRUE) ? block->bbJumpDest : block->bbNext;
        trueMessage = (rirIfTrue == RIR_TRUE) ? "true" : "false";
    }

    if (rirIfFalse != RIR_UNKNOWN)
    {
        falseTarget  = (rirIfFalse == RIR_TRUE) ? block->bbJumpDest : block->bbNext;
        falseMessage = (rirIfFalse == RIR_TRUE) ? "true" : "false";
    }

    // I don't think it's possible for both targets to match... we know they can't
    // both be null, and it seems odd that the could both be the same.
    //
    assert(trueTarget != falseTarget);

    // In order to optimize we have to be able to determine which predecessors
    // are correlated exclusively with the rirIfTrue value for block's relop, and which
    // are correlated exclusively with the rirIfFalse value (aka true preds and false preds).
    //
    // Given a successful true inference, a true pred can branch to the trueTarget.
    // Given a successful false inference, a false pred can branch to the falseTarget.
    //
    // To determine if a pred is true or false we try and follow the flow from domBlock
    // to block; any block pred reachable from domBlock's true edge is a true pred, and
    // vice versa.
    //
    // However, there are some exceptions and complications:
    //
    // * It's possible for a pred to be reachable from both paths out of domBlock;
    // if so, we can't jump thread that pred.
    //
    // * It's also possible for us to think a pred is reachable from both paths
    // when it no longer is; we use fgReachable which was computed upstream and
    // is not updated as flow is refined. So it may overstate reachability.
    // To try and mitigate that, we have the main branch loop work in postorder.
    //
    // * It's also possible that a pred can't branch directly to a successor as
    // it might violate EH region constraints. Since this causes the same issues
    // as an ambiguous pred we'll just classify these as ambiguous too.
    //
    // * It's also possible to have preds with implied eh flow to the current
    // block, eg a catch return, and so we won't see either path reachable.
    // We'll handle those as ambiguous as well.
    //
    // * It's also possible that the pred is a switch; we could handle that
    // but don't, currently.
    //
    // * It's also possible that the inference failed for a particular class of
    // pred. We'll handle those as ambiguous as well.
    //
    // For true preds and false preds we can reroute flow. It may turn out that
    // one of the preds falls through to block. We would prefer not to introduce
    // a new block to allow changing that fall through to a jump, so if we have
    // any ambiguous preds and an unambiguous fall through, we defer optimizing
    // the fall through pred as well.
    //
    // This creates an ordering issue, and to resolve it we have to walk the pred
    // list twice. Classification of preds should be cheap so we just rerun the
    // reachability checks twice as well.
    //
    int               numPreds          = 0;
    int               numAmbiguousPreds = 0;
    int               numTruePreds      = 0;
    int               numFalsePreds     = 0;
    BasicBlock*       uniqueTruePred    = nullptr;
    BasicBlock*       uniqueFalsePred   = nullptr;
    BasicBlock*       fallThroughPred   = nullptr;
    BasicBlock* const trueSuccessor     = domBlock->bbJumpDest;
    BasicBlock* const falseSuccessor    = domBlock->bbNext;

    for (flowList* pred = block->bbPreds; pred != nullptr; pred = pred->flNext)
    {
        BasicBlock* const predBlock = pred->flBlock;
        numPreds++;

        // We don't do switch updates, yet.
        //
        if (predBlock->bbJumpKind == BBJ_SWITCH)
        {
            JITDUMP(FMT_BB " has switch pred " FMT_BB ", not optimizing\n", block->bbNum, predBlock->bbNum);
            return false;
        }

        const bool isTruePred =
            ((predBlock == domBlock) && (trueSuccessor == block)) || fgReachable(trueSuccessor, predBlock);
        const bool isFalsePred =
            ((predBlock == domBlock) && (falseSuccessor == block)) || fgReachable(falseSuccessor, predBlock);

        if (isTruePred == isFalsePred)
        {
            // Either both reach, or neither reaches.
            //
            JITDUMP(FMT_BB " is an ambiguous pred\n", predBlock->bbNum);
            numAmbiguousPreds++;
            continue;
        }

        if (isTruePred)
        {
            if (trueTarget == nullptr)
            {
                JITDUMP(FMT_BB " is a true pred, but we could not determine the true target\n", predBlock->bbNum);
                numAmbiguousPreds++;
                continue;
            }

            if (!BasicBlock::sameEHRegion(predBlock, trueTarget))
            {
                JITDUMP(FMT_BB " is an eh constrained true pred\n", predBlock->bbNum);
                numAmbiguousPreds++;
                continue;
            }

            if (numTruePreds == 0)
            {
                uniqueTruePred = predBlock;
            }
            else
            {
                uniqueTruePred = nullptr;
            }

            numTruePreds++;
            JITDUMP(FMT_BB " is a true pred\n", predBlock->bbNum);
        }
        else
        {
            assert(isFalsePred);

            if (falseTarget == nullptr)
            {
                JITDUMP(FMT_BB " is a false pred, but we could not determine false target\n", predBlock->bbNum);
                numAmbiguousPreds++;
                continue;
            }

            if (!BasicBlock::sameEHRegion(predBlock, falseTarget))
            {
                JITDUMP(FMT_BB " is an eh constrained false pred\n", predBlock->bbNum);
                numAmbiguousPreds++;
                continue;
            }

            if (numFalsePreds == 0)
            {
                uniqueFalsePred = predBlock;
            }
            else
            {
                uniqueFalsePred = nullptr;
            }

            numFalsePreds++;
            JITDUMP(FMT_BB " is a false pred and can branch to " FMT_BB "\n", predBlock->bbNum, falseTarget->bbNum);
        }

        if (predBlock->bbNext == block)
        {
            JITDUMP(FMT_BB " is an unambiguous fall-through pred\n", predBlock->bbNum);
            assert(fallThroughPred == nullptr);
            fallThroughPred = predBlock;
        }
    }

    // All preds should have been classified.
    //
    assert(numPreds == numTruePreds + numFalsePreds + numAmbiguousPreds);

    if ((numTruePreds == 0) && (numFalsePreds == 0))
    {
        // This is possible, but should be rare.
        //
        JITDUMP(FMT_BB " only has ambiguous preds, not optimizing\n");
        return false;
    }

    if ((numAmbiguousPreds > 0) && (fallThroughPred != nullptr))
    {
        JITDUMP(FMT_BB " has both ambiguous preds and an unambiguous fall through pred, not optimizing\n");
        return false;
    }

    // We should be good to go
    //
    JITDUMP("Optimizing via jump threading\n");

    // Now reroute the flow from the predecessors.
    //
    // If there is a fall through pred, modify block by deleting the terminal
    // jump statement, and update it to jump or fall through to the appropriate successor.
    // Note this is just a refinement of pre-existing flow so no EH check is needed.
    //
    // All other predecessors must reach block via a jump. So we can update their
    // flow directly by changing their jump targets to the appropriate successor,
    // provided it's a permissable flow in our EH model.
    //
    for (flowList* pred = block->bbPreds; pred != nullptr; pred = pred->flNext)
    {
        BasicBlock* const predBlock = pred->flBlock;

        const bool isTruePred =
            ((predBlock == domBlock) && (trueSuccessor == block)) || fgReachable(trueSuccessor, predBlock);
        const bool isFalsePred =
            ((predBlock == domBlock) && (falseSuccessor == block)) || fgReachable(falseSuccessor, predBlock);

        if (isTruePred == isFalsePred)
        {
            // Skip over ambiguous preds, they will continue to flow to block.
            //
            continue;
        }

        if ((isTruePred && (trueTarget == nullptr)) || (isFalsePred && (falseTarget == nullptr)))
        {
            // Skip over preds where the relop value could not be inferred, they will continue to flow to block.
            //
            continue;
        }

        if (!BasicBlock::sameEHRegion(predBlock, isTruePred ? trueTarget : falseTarget))
        {
            // Skip over eh constrained preds, they will continue to flow to block.
            //
            continue;
        }

        // Is this the one and only unambiguous fall through pred?
        //
        if (predBlock->bbNext == block)
        {
            assert(predBlock == fallThroughPred);

            // No other pred can safely pass control through block.
            //
            assert(numAmbiguousPreds == 0);

            // Clean out the terminal branch statement; we are going to repurpose this block
            //
            Statement* lastStmt = block->lastStmt();
            fgRemoveStmt(block, lastStmt);

            if (isTruePred)
            {
                JITDUMP("Fall through flow from pred " FMT_BB " -> " FMT_BB " implies predicate %s\n", predBlock->bbNum,
                        block->bbNum, trueMessage);
                JITDUMP("  repurposing " FMT_BB " to always jump to " FMT_BB "\n", block->bbNum, trueTarget->bbNum);
                fgRemoveRefPred(block->bbNext, block);
                block->bbJumpKind = BBJ_ALWAYS;
            }
            else
            {
                assert(isFalsePred);
                JITDUMP("Fall through flow from pred " FMT_BB " -> " FMT_BB " implies predicate %s\n", predBlock->bbNum,
                        block->bbNum, falseMessage);
                JITDUMP("  repurposing " FMT_BB " to always fall through to " FMT_BB "\n", block->bbNum,
                        falseTarget->bbNum);
                fgRemoveRefPred(block->bbJumpDest, block);
                block->bbJumpKind = BBJ_NONE;
            }
        }
        else
        {
            assert(predBlock->bbNext != block);
            if (isTruePred)
            {
                assert(!fgReachable(falseSuccessor, predBlock));
                JITDUMP("Jump flow from pred " FMT_BB " -> " FMT_BB
                        " implies predicate %s; we can safely redirect flow to be " FMT_BB " -> " FMT_BB "\n",
                        predBlock->bbNum, block->bbNum, trueMessage, predBlock->bbNum, trueTarget->bbNum);

                fgRemoveRefPred(block, predBlock);
                fgReplaceJumpTarget(predBlock, trueTarget, block);
                fgAddRefPred(trueTarget, predBlock);
                trueTarget->bbFlags |= BBF_JMP_TARGET;
            }
            else
            {
                assert(isFalsePred);

                JITDUMP("Jump flow from pred " FMT_BB " -> " FMT_BB
                        " implies predicate %s; we can safely redirect flow to be " FMT_BB " -> " FMT_BB "\n",
                        predBlock->bbNum, block->bbNum, falseMessage, predBlock->bbNum, falseTarget->bbNum);

                fgRemoveRefPred(block, predBlock);
                fgReplaceJumpTarget(predBlock, falseTarget, block);
                fgAddRefPred(falseTarget, predBlock);
                falseTarget->bbFlags |= BBF_JMP_TARGET;
            }
        }
    }

    // We optimized.
    //
    fgModified = true;
    return true;
}

//-------------------------------------------------------------
// optRelopImpliesRelop: sees if the value of one relop
//    implies the value of another relop.
//
// Arguments:
//    relop1 - the first relop
//    relop1Value - the value of relop1
//    relop2 - the second relop
//
// Returns:
//    RIR_TRUE if relop2 must be true, given the value of relop1
//    RIR_FALSE if relop2 must be false, given the value of relop1
//    RIR_UNKNOWN if true/false can't be determined.
//
Compiler::RelopImplicationResult Compiler::optRelopImpliesRelop(GenTree* const relop1,
                                                                bool           relop1Value,
                                                                GenTree* const relop2)
{
    assert(relop1->OperIsCompare());
    assert(relop2->OperIsCompare());

    // Examine the value numbers of relop1 and relop2.
    //
    ValueNum vn1Normal;
    ValueNum vn1Exception;
    vnStore->VNUnpackExc(relop1->GetVN(VNK_Liberal), &vn1Normal, &vn1Exception);
    ValueNum vn2Normal;
    ValueNum vn2Exception;
    vnStore->VNUnpackExc(relop2->GetVN(VNK_Liberal), &vn2Normal, &vn2Exception);

    // Insist for now that relop2 not have any novel exceptions.
    //
    // If caller is willing to extract and duplicate relop2's side
    // effects, we can relax this.
    //
    if (!vnStore->VNExcIsSubset(vn1Exception, vn2Exception))
    {
        return RIR_UNKNOWN;
    }

    // If the normal value numbers agree, then relop2 is fully redundant.
    //
    if (vn1Normal == vn2Normal)
    {
        JITDUMP("RIR(%s): Value numbers agree, so second relop is %s\n", relop1Value ? "true" : "false",
                relop1Value ? "true" : "false");
        return relop1Value ? RIR_TRUE : RIR_FALSE;
    }

    // If the value numbers differ, check if the left hand sides match.
    //
    GenTree* const op11 = relop1->AsOp()->gtOp1;
    GenTree* const op21 = relop2->AsOp()->gtOp1;

    if (vnStore->VNLiberalNormalValue(op11->gtVNPair) != vnStore->VNLiberalNormalValue(op21->gtVNPair))
    {
        // The relop LHSs don't match, so we can't draw any conclusions.
        // (TODO: verify we've properly canonicalized relops so constants never appear on LHSs).
        //
        return RIR_UNKNOWN;
    }

    // Don't handle byref comparisons until downstream code is prepared to cope.
    //
    // (some interop stubs compare byrefs to nulls)
    //
    if (op11->TypeIs(TYP_BYREF))
    {
        return RIR_UNKNOWN;
    }

    // We currently only handle cases where op2's have the same operator.
    //
    // TODO: allow mixed RHSs, eg constant vs array len. Perhaps not that
    // interesting until/unless we also consider implicit relops in array
    // accesses.
    //
    GenTree* const op12 = relop1->AsOp()->gtOp2;
    GenTree* const op22 = relop2->AsOp()->gtOp2;

    if (op12->OperGet() != op22->OperGet())
    {
        return RIR_UNKNOWN;
    }

    // We have (x RELOP y1) =?=> (x RELOP' y2) where y1 and y2 are the
    // same kind of tree.
    //
    // If y's are constants we can often infer the value of relop2.
    //
    if (op12->OperIsConst())
    {
        const RelopImplicationResult rir = optRelopImpliesRelopRHSConstant(relop1, relop1Value, relop2, op12, op22);
        JITDUMP("RIR(%s)]: inference says second relop value is %s\n", relop1Value ? "true" : "false",
                (rir == RIR_UNKNOWN) ? "unknown" : ((rir == RIR_TRUE) ? "true" : "false"));
        return rir;
    }

    // TODO: handle other interesting RHS cases.
    //
    return RIR_UNKNOWN;
}

//-------------------------------------------------------------
// optRelopImpliesRelopRHSConstant: sees if the value of
//    one relop implies the value of another relop, where LHSs
//    are same integral value, and RHSs are constants.
//
// Arguments:
//    relop1 - the first relop
//    relop1Value - the value of relop1
//    relop2 - the second relop
//    op12 - constant in first relop
//    op22 - constant in second relop
//
// Returns:
//    RIR_TRUE if relop2 must be true, given the value of relop1
//    RIR_FALSE if relop2 must be false, given the value of relop1
//    RIR_UNKNOWN if true/false can't be determined.
//
// Notes:
//    Loosely based on Table 2 in "Avoiding Conditional Branches
//    by Code Replication" by Mueller & Whalley, PLDI '95.
//
Compiler::RelopImplicationResult Compiler::optRelopImpliesRelopRHSConstant(
    GenTree* const relop1, bool relop1Value, GenTree* const relop2, GenTree* const op12, GenTree* const op22)
{
    // Only handle integral constants
    //
    if (!op12->IsIntegralConst() || !op22->IsIntegralConst())
    {
        return RIR_UNKNOWN;
    }

    // If one constant is a handle, the other must be a handle of the same kind.
    //
    if (op12->IsIconHandle())
    {
        if (!op22->IsIconHandle())
        {
            return RIR_UNKNOWN;
        }

        if (!GenTree::SameIconHandleFlag(op12, op22))
        {
            return RIR_UNKNOWN;
        }
    }

    // Now look at the operators.
    //
    GenCondition c1 = GenCondition::FromRelop(relop1);
    GenCondition c2 = GenCondition::FromRelop(relop2);

    // Don't handle float comparisons.
    //
    if (c1.IsFloat() || c2.IsFloat())
    {
        return RIR_UNKNOWN;
    }

    // Don't handle mixed signed / unsigned comparisons.
    // (todo: consider the common BCE idiom)
    //
    if (c1.IsUnsigned() != c2.IsUnsigned())
    {
        return RIR_UNKNOWN;
    }

    // If relop2 was reached because relop1 was false,
    // then reverse the sense of relop1.
    //
    if (!relop1Value)
    {
        c1 = GenCondition::Reverse(c1);
    }

    // Assume we'll fail to establish the implication,
    // and try to prove otherwise.
    //
    RelopImplicationResult result = RIR_UNKNOWN;

    // We're going to reduce (x RELOP k1) => (x RELOP' k2)
    // to (k1 RELOP* k2 +/- 1).
    //
    switch (c1.GetCode())
    {
        case GenCondition::EQ:
        {
            // From upstream equality we know the exact value,
            // so any downstream check versus a constant
            // can be resolved.
            //
            const bool isTrue = optEvaluateRelop(op12, op22, c2, 0, TYP_LONG);
            result            = isTrue ? RIR_TRUE : RIR_FALSE;
            break;
        }

        case GenCondition::NE:
        {
            // We can't learn much from a non-equality test,
            // but there are a few cases we can resolve.
            //
            switch (c2.GetCode())
            {
                case GenCondition::EQ:
                case GenCondition::NE:
                {
                    // (NE x K1) ==>  (NE x K2)  if K1 == K2
                    // (NE x K1) ==> !(EQ x K2)  if K1 == K2
                    //
                    bool isTrue = optEvaluateRelop(op12, op22, GenCondition::EQ, 0, TYP_LONG);
                    if (isTrue)
                    {
                        const bool invertResult = c2.Is(GenCondition::EQ);
                        result                  = invertResult ? RIR_FALSE : RIR_TRUE;
                    }
                    break;
                }

                default:
                    break;
            }
            break;
        }

        case GenCondition::SLE:
        case GenCondition::SGE:
        case GenCondition::SLT:
        case GenCondition::SGT:
        case GenCondition::ULE:
        case GenCondition::UGE:
        case GenCondition::ULT:
        case GenCondition::UGT:
        {
            // We have a leading inequality, and may be able to prove or disprove
            // the second condition.
            //
            // for x < y:
            //
            //     x != z  is true  IF y <= z
            //     x  = z  is false IF y <  z
            //
            //     x <  z  is true  IF y <= z
            //     x >  z  is false IF y <= z + 1
            //
            //     x <= z  is true  IF y <= z + 1
            //     x >= z  is false IF y <= z
            //
            // for x <= y:
            //
            //     x != z  is true  IF y <  z
            //     x  = z  is false IF y <  z
            //
            //     x <= z  is true  IF y <= z
            //     x >= z  is false IF y <= z - 1
            //
            //     x <  z  is true  IF y <= z - 1
            //     x >  z  is false IF y <= z
            //
            // for x > y:
            //
            //     x != z  is true  IF y >= z
            //     x  = z  is false IF y >  z
            //
            //     x >  z  is true  IF y >= z
            //     x <  z  is false IF y >= z - 1
            //
            //     x >= z  is true  IF y >= z - 1
            //     x <= z  is false IF y >= z
            //
            // for x >= y:
            //
            //     x != z  is true  IF y >  z
            //     x  = z  is false IF y >  z
            //
            //     x >= z  is true  IF y >= z
            //     x <= z  is false IF y >= z + 1
            //
            //     x >  z  is true  IF y >= z + 1
            //     x <  z  is false IF y >= z
            //
            GenCondition comparisonOp(GenCondition::NONE);
            int          adjustment = 0;

            if (c2.Is(GenCondition::EQ) || c2.Is(GenCondition::NE))
            {
                if ((c1.IsClass(GenCondition::SLT)) || c1.IsClass(GenCondition::SGT))
                {
                    comparisonOp = GenCondition::AddEquality(c1);
                }
                else
                {
                    comparisonOp = GenCondition::RemoveEquality(c1);
                }
            }
            else
            {
                // Mixed LT/LE/GT/GE always use the "E" forms,
                // and may also require adjustment.
                //
                comparisonOp = GenCondition::AddEquality(c1);

                if (c1.IsClass(GenCondition::SLT))
                {
                    if (c2.IsClass(GenCondition::SGT) || c2.IsClass(GenCondition::SLE))
                    {
                        adjustment = +1;
                    }
                }

                if (c1.IsClass(GenCondition::SLE))
                {
                    if (c2.IsClass(GenCondition::SGE) || c2.IsClass(GenCondition::SLT))
                    {
                        adjustment = -1;
                    }
                }

                if (c1.IsClass(GenCondition::SGT))
                {
                    if (c2.IsClass(GenCondition::SLT) || c2.IsClass(GenCondition::SGE))
                    {
                        adjustment = -1;
                    }
                }

                if (c1.IsClass(GenCondition::SGE))
                {
                    if (c2.IsClass(GenCondition::SLE) || c2.IsClass(GenCondition::SGT))
                    {
                        adjustment = +1;
                    }
                }
            }

            // Verify it's ok to use type of constant here...
            //
            const bool isImplied = optEvaluateRelop(op12, op22, comparisonOp, adjustment, op12->TypeGet());

            // If we proved the implication, map to a result.
            //
            if (isImplied)
            {
                // Check if the result needs to be inverted ("is false") cases above.
                //
                const bool invertResult = c1.IsLess() && (c2.IsGreater() || c2.Is(GenCondition::EQ)) ||
                                          c1.IsGreater() && (c2.IsLess() || c2.Is(GenCondition::EQ));

                result = invertResult ? RIR_FALSE : RIR_TRUE;
            }
            break;
        }

        default:
            break;
    }

    return result;
}

//------------------------------------------------------------------------
// optEvaluateRelop: given a relop and constant values, determine if the
//    relop is true or false
//
// Arguments:
//     c1   - first constant
//     c2   - second constant
//     cond - condition
//     adj  - value to add to c2 (-1, 0, or 1)
//     type - types being compared
//
// Returns:
//     True if "(c1 cond c2 + adj)" is definitely true
//     False if it's false or truth can't be determined
//
bool Compiler::optEvaluateRelop(GenTree* const c1, GenTree* const c2, GenCondition cond, int adj, var_types type)
{
    ssize_t k1  = c1->AsIntConCommon()->IntegralValue();
    ssize_t k2  = c2->AsIntConCommon()->IntegralValue();
    size_t  uk1 = (size_t)k1;
    size_t  uk2 = (size_t)k2;

    if (cond.IsUnsigned())
    {
        JITDUMP(" -- Evaluating (%llu %s %llu + %d) as %s\n", uk1, cond.Name(), uk2, adj, varTypeName(type));
    }
    else
    {
        JITDUMP(" -- Evaluating (%lld %s %lld + %d) as %s\n", k1, cond.Name(), k2, adj, varTypeName(type));
    }

    assert((adj >= -1) && (adj <= 1));

    // We may not be able to adjust if it would cause overflow.
    //
    if (adj == 1)
    {
        ssize_t maxk2 = AssertionDsc::GetUpperBoundForIntegralType(type);
        if (k2 == maxk2)
        {
            return false;
        }
        k2 += 1;
    }
    else if (adj == -1)
    {
        ssize_t mink2 = AssertionDsc::GetLowerBoundForIntegralType(type);
        if (k2 == mink2)
        {
            return false;
        }
        k2 -= 1;
    }

    switch (cond.GetCode())
    {
        case GenCondition::EQ:
        {
            return k1 == k2;
        }

        case GenCondition::NE:
        {
            return k1 != k2;
        }

        case GenCondition::SLT:
        {
            return k1 < k2;
        }

        case GenCondition::SLE:
        {
            return k1 <= k2;
        }

        case GenCondition::SGT:
        {
            return k1 > k2;
        }

        case GenCondition::SGE:
        {
            return k1 >= k2;
        }

        case GenCondition::ULT:
        {
            return uk1 < uk2;
        }

        case GenCondition::ULE:
        {
            return uk1 <= uk2;
        }

        case GenCondition::UGT:
        {
            return uk1 > uk2;
        }

        case GenCondition::UGE:
        {
            return uk1 >= uk2;
        }

        default:
            break;
    }
    return false;
}
