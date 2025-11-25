// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

#include "jitpch.h"
#ifdef _MSC_VER
#pragma hdrstop
#endif

#include "codegen.h"
#include "fgwasm.h"

void CodeGen::genMarkLabelsForCodegen()
{
    // TODO-WASM: serialize fgWasmControlFlow results into codegen-level metadata/labels
    // (or use them directly and leave this empty).
}

void CodeGen::genFnProlog()
{
    ScopedSetVariable<bool> _setGeneratingProlog(&compiler->compGeneratingProlog, true);

    compiler->funSetCurrentFunc(0);

#ifdef DEBUG
    if (verbose)
    {
        printf("*************** In genFnProlog()\n");
    }
#endif

#ifdef DEBUG
    genInterruptibleUsed = true;
#endif

    assert(compiler->lvaDoneFrameLayout == Compiler::FINAL_FRAME_LAYOUT);

    /* Ready to start on the prolog proper */

    GetEmitter()->emitBegProlog();
    // compiler->unwindBegProlog();

    // Do this so we can put the prolog instruction group ahead of
    // other instruction groups
    genIPmappingAddToFront(IPmappingDscKind::Prolog, DebugInfo(), true);

#ifdef DEBUG
    if (compiler->opts.dspCode)
    {
        printf("\n__prolog:\n");
    }
#endif

    if (compiler->opts.compScopeInfo && (compiler->info.compVarScopesCount > 0))
    {
        // Create new scopes for the method-parameters for the prolog-block.
        psiBegProlog();
    }

    // Todo: prolog zeroing, shadow stack maintenance
}

void CodeGen::genFnEpilog(BasicBlock* block)
{
#ifdef DEBUG
    if (verbose)
    {
        printf("*************** In genFnEpilog()\n");
    }
#endif // DEBUG

    // NYI_WASM("genFnEpilog");
}

void CodeGen::genCaptureFuncletPrologEpilogInfo()
{
}

void CodeGen::genFuncletProlog(BasicBlock* block)
{
#ifdef DEBUG
    if (verbose)
    {
        printf("*************** In genFuncletProlog()\n");
    }
#endif

    NYI_WASM("genFuncletProlog");
}

void CodeGen::genFuncletEpilog()
{
#ifdef DEBUG
    if (verbose)
    {
        printf("*************** In genFuncletEpilog()\n");
    }
#endif

    NYI_WASM("genFuncletEpilog");
}

void CodeGen::genCodeForTreeNode(GenTree* treeNode)
{
#ifdef DEBUG
    lastConsumedNode = nullptr;
    if (compiler->verbose)
    {
        compiler->gtDispLIRNode(treeNode, "Generating: ");
    }
#endif // DEBUG

    assert(!treeNode->IsReuseRegVal()); // TODO-WASM-CQ: enable.

    // Contained nodes are part of the parent for codegen purposes.
    if (treeNode->isContained())
    {
        return;
    }

    switch (treeNode->OperGet())
    {
        case GT_ADD:
        case GT_GT:
            genCodeForBinary(treeNode->AsOp());
            break;

        case GT_LCL_VAR:
            genCodeForLclVar(treeNode->AsLclVar());
            break;

        case GT_JTRUE:
            // Do nothing; handled by end of block processing
            break;

        case GT_RETURN:
            genReturn(treeNode);
            break;

        case GT_IL_OFFSET:
            // Do nothing; this node is a marker for debug info.
            break;

        default:
#ifdef DEBUG
            NYIRAW(GenTree::OpName(treeNode->OperGet()));
#else
            NYI_WASM("Opcode not implemented");
#endif
            break;
    }
}

//------------------------------------------------------------------------
// genCodeForBinary: Generate code for a binary arithmetic operator
//
// Arguments:
//    treeNode - The binary operation for which we are generating code.
//
void CodeGen::genCodeForBinary(GenTreeOp* treeNode)
{
    genConsumeOperands(treeNode);

    instruction ins;
    switch (treeNode->OperGet())
    {
        case GT_ADD:
            if (!treeNode->TypeIs(TYP_INT))
            {
                NYI_WASM("genCodeForBinary: non-INT GT_ADD");
            }
            ins = INS_i32_add;
            break;

        case GT_GT:
            if (!treeNode->TypeIs(TYP_INT))
            {
                NYI_WASM("genCodeForBinary: non-INT GT_ADD");
            }
            ins = treeNode->IsUnsigned() ? INS_i32_gt_u : INS_i32_gt_s;
            break;

        default:
            ins = INS_none;
            NYI_WASM("genCodeForBinary");
            break;
    }

    GetEmitter()->emitIns(ins);
    genProduceReg(treeNode);
}

//------------------------------------------------------------------------
// genCodeForLclVar: Produce code for a GT_LCL_VAR node.
//
// Arguments:
//    tree - the GT_LCL_VAR node
//
void CodeGen::genCodeForLclVar(GenTreeLclVar* tree)
{
    assert(tree->OperIs(GT_LCL_VAR) && !tree->IsMultiReg());
    LclVarDsc* varDsc = compiler->lvaGetDesc(tree);

    // Unlike other targets, we can't "reload at the point of use", since that would require inserting instructions
    // into the middle of an already-emitted instruction group. Instead, we order the nodes in a way that obeys the
    // value stack constraints of WASM precisely. However, the liveness tracking is done in the same way as for other
    // targets, hence "genProduceReg" is only called for non-candidates.
    if (!varDsc->lvIsRegCandidate())
    {
        var_types type = varDsc->GetRegisterType(tree);
        // TODO-WASM: actually local.get the frame base local here.
        GetEmitter()->emitIns_S(ins_Load(type), emitTypeSize(tree), tree->GetLclNum(), 0);
        genProduceReg(tree);
    }
    else
    {
        assert(genIsValidReg(varDsc->GetRegNum()));
        unsigned wasmLclIndex = UnpackWasmReg(varDsc->GetRegNum());
        GetEmitter()->emitIns_I(INS_local_get, emitTypeSize(tree), wasmLclIndex);
    }
}

BasicBlock* CodeGen::genCallFinally(BasicBlock* block)
{
    assert(block->KindIs(BBJ_CALLFINALLY));
    NYI_WASM("genCallFinally");
    return nullptr;
}

void CodeGen::genEHCatchRet(BasicBlock* block)
{
    NYI_WASM("genEHCatchRet");
}

void CodeGen::genStructReturn(GenTree* treeNode)
{
    NYI_WASM("genStructReturn");
}

void CodeGen::genEmitGSCookieCheck(bool tailCall)
{
    // TODO-WASM: GS cookie checks have limited utility on WASM since they can only help
    // with detecting linear memory stack corruption. Decide if we want them anyway.
    NYI_WASM("genEmitGSCookieCheck");
}

void CodeGen::genProfilingLeaveCallback(unsigned helper)
{
    NYI_WASM("genProfilingLeaveCallback");
}

void CodeGen::genSpillVar(GenTree* tree)
{
    NYI_WASM("Put all spillng to memory under '#if HAS_FIXED_REGISTER_SET'");
}

//------------------------------------------------------------------------
// inst_JMP: Generate a jump instruction.
//
void CodeGen::inst_JMP(emitJumpKind jmp, unsigned depth)
{
    instruction instr = emitter::emitJumpKindToIns(jmp);
    GetEmitter()->emitIns_I(instr, EA_4BYTE, depth);
}

//------------------------------------------------------------------------
// inst_LABEL: Emit a label index
//
void CodeGen::inst_LABEL(unsigned depth)
{
    NYI_WASM("inst_LABEL");
}

void CodeGen::genCreateAndStoreGCInfo(unsigned codeSize, unsigned prologSize, unsigned epilogSize DEBUGARG(void* code))
{
    // GCInfo not captured/created by codegen.
}

void CodeGen::genReportEH()
{
    // EHInfo not captured/created by codegen.
}

//---------------------------------------------------------------------
// genTotalFrameSize - return the total size of the linear memory stack frame.
//
// Return value:
//    Total linear memory frame size
//
int CodeGenInterface::genTotalFrameSize() const
{
    assert(compiler->compLclFrameSize >= 0);
    return compiler->compLclFrameSize;
}

//---------------------------------------------------------------------
// genSPtoFPdelta - return the offset from SP to the frame pointer.
// This number is going to be positive, since SP must be at the lowest
// address.
//
// There must be a frame pointer to call this function!
int CodeGenInterface::genSPtoFPdelta() const
{
    assert(isFramePointerUsed());
    NYI_WASM("genSPtoFPdelta");
    return 0;
}

//---------------------------------------------------------------------
// genCallerSPtoFPdelta - return the offset from Caller-SP to the frame pointer.
// This number is going to be negative, since the Caller-SP is at a higher
// address than the frame pointer.
//
// There must be a frame pointer to call this function!
int CodeGenInterface::genCallerSPtoFPdelta() const
{
    assert(isFramePointerUsed());
    NYI_WASM("genCallerSPtoFPdelta");
    return 0;
}

//---------------------------------------------------------------------
// genCallerSPtoInitialSPdelta - return the offset from Caller-SP to Initial SP.
//
// This number will be negative.
int CodeGenInterface::genCallerSPtoInitialSPdelta() const
{
    NYI_WASM("genCallerSPtoInitialSPdelta");
    return 0;
}

void CodeGenInterface::genUpdateVarReg(LclVarDsc* varDsc, GenTree* tree, int regIndex)
{
    NYI_WASM("Move genUpdateVarReg from codegenlinear.cpp to codegencommon.cpp shared code");
}

void RegSet::verifyRegUsed(regNumber reg)
{
}

//------------------------------------------------------------------------
// genCodeForBBlist: Generate code for all the blocks in a method
//
// Arguments:
//
// Notes:
//    This is the main method for linear codegen. It calls genCodeForTreeNode
//    to generate the code for each node in each BasicBlock, and handles BasicBlock
//    boundaries and branches.
//
void CodeGen::genCodeForBBlist()
{
#ifdef DEBUG
    genInterruptibleUsed = true;

    // You have to be careful if you create basic blocks from now on
    compiler->fgSafeBasicBlockCreation = false;
#endif // DEBUG

    // Prepare for codegen
    //
    genInitialize();

    assert(genStackLevel == 0);

    // Wasm control flow is stack based.
    //
    // We have pre computed the set of intervals that require stack transitions
    // in compiler->fgWasmIntervals, ordered by starting block index.
    //
    // As we walk the blocks we'll push and pop onto this stack. As we emit control
    // flow labels, we'll consult this stack to figure out the depth of our target label.
    //
    ArrayStack<WasmInterval*> wasmControlFlowStack(compiler->getAllocator(CMK_WasmCfgLowering));
    unsigned                  wasmCursor = 0;

    // Walk the block list, emitting code
    //
    for (BasicBlock* const block : compiler->Blocks())
    {
        // Note the position of this block in the block linear order.
        //
        unsigned const cursor = block->bbPreorderNum;

        JITDUMP("\n=============== Generating ");
        JITDUMPEXEC(block->dspBlockHeader(true, true));
        JITDUMPEXEC(compiler->fgDispBBLiveness(block));

        assert(LIR::AsRange(block).CheckLIR(compiler));

        // Figure out which registers hold variables on entry to this block

        regSet.ClearMaskVars();
        gcInfo.gcRegGCrefSetCur = RBM_NONE;
        gcInfo.gcRegByrefSetCur = RBM_NONE;

        compiler->m_regAlloc->recordVarLocationsAtStartOfBB(block);

        // Updating variable liveness after last instruction of previous block was emitted
        // and before first of the current block is emitted
        //
        genUpdateLife(block->bbLiveIn);

        // WASM-TODO: update register GC info
        //

        // Prepare for codegen in this block
        //
        genLogLabel(block);
        compiler->compCurBB = block;
        block->bbEmitCookie = nullptr;

        // If this block is a jump target or it requires a label then set 'needLabel' to true,
        //
        bool needLabel = block->HasFlag(BBF_HAS_LABEL);

        // We won't do hot/cold splitting for wasm
        assert(!block->IsFirstColdBlock(compiler));

        // We also want to start a new Instruction group by calling emitAddLabel below,
        // when we need accurate bbWeights for this block in the emitter.  We force this
        // whenever our previous block was a BBJ_COND and it has a different weight than us.
        //
        // Note: We need to have set compCurBB before calling emitAddLabel
        //
        if (!block->IsFirst() && block->Prev()->KindIs(BBJ_COND) && (block->bbWeight != block->Prev()->bbWeight))
        {
            JITDUMP("Adding label due to BB weight difference: BBJ_COND " FMT_BB " with weight " FMT_WT
                    " different from " FMT_BB " with weight " FMT_WT "\n",
                    block->Prev()->bbNum, block->Prev()->bbWeight, block->bbNum, block->bbWeight);
            needLabel = true;
        }

        if (needLabel)
        {
            // Mark a label and update the current set of live GC refs

            block->bbEmitCookie = GetEmitter()->emitAddLabel(gcInfo.gcVarPtrSetCur, gcInfo.gcRegGCrefSetCur,
                                                             gcInfo.gcRegByrefSetCur, block->Prev());
        }

        // Pop control flow intervals that end here (at most two, block and/or loop)
        //
        while (!wasmControlFlowStack.Empty() && (wasmControlFlowStack.Top()->End() == cursor))
        {
            instGen(INS_end);
            wasmControlFlowStack.Pop();
        }

        // Push control flow for intervals that start here or earlier
        //
        if (wasmCursor < compiler->fgWasmIntervals->size())
        {
            WasmInterval* interval = compiler->fgWasmIntervals->at(wasmCursor);
            WasmInterval* chain    = interval->Chain();

            while (chain->Start() <= cursor)
            {
                if (interval->IsLoop())
                {
                    instGen(INS_loop);
                }
                else
                {
                    instGen(INS_block);
                }

                wasmCursor++;
                wasmControlFlowStack.Push(interval);

                if (wasmCursor >= compiler->fgWasmIntervals->size())
                {
                    break;
                }

                interval = compiler->fgWasmIntervals->at(wasmCursor);
                chain    = interval->Chain();
            }
        }

        // Needed when jitting debug code
        siBeginBlock(block);

        // BBF_INTERNAL blocks don't correspond to any single IL instruction.
        // Add a NoMapping entry unless this is right after the prolog where it
        // is unnecessary.
        if (compiler->opts.compDbgInfo && block->HasFlag(BBF_INTERNAL) && !block->IsFirst())
        {
            genIPmappingAdd(IPmappingDscKind::NoMapping, DebugInfo(), true);
        }

        if (compiler->bbIsFuncletBeg(block))
        {
            genUpdateCurrentFunclet(block);
            genReserveFuncletProlog(block);
        }

        // Clear compCurStmt and compCurLifeTree.
        compiler->compCurStmt     = nullptr;
        compiler->compCurLifeTree = nullptr;

#if FALSE // Temporarily stub out codegen within blocks

        // Emit poisoning into the init BB that comes right after prolog.
        // We cannot emit this code in the prolog as it might make the prolog too large.
        if (compiler->compShouldPoisonFrame() && block->IsFirst())
        {
            genPoisonFrame(newLiveRegSet);
        }

        // Traverse the block in linear order, generating code for each node as we
        // as we encounter it.

#ifdef DEBUG
        // Set the use-order numbers for each node.
        {
            int useNum = 0;
            for (GenTree* node : LIR::AsRange(block))
            {
                assert((node->gtDebugFlags & GTF_DEBUG_NODE_CG_CONSUMED) == 0);

                node->gtUseNum = -1;
                if (node->isContained() || node->IsCopyOrReload())
                {
                    continue;
                }

                for (GenTree* operand : node->Operands())
                {
                    genNumberOperandUse(operand, useNum);
                }
            }
        }
#endif // DEBUG

#endif // FALSE

        bool producedLabelMapping = false;
        bool addRichMappings      = JitConfig.RichDebugInfo() != 0;

        INDEBUG(addRichMappings |= JitConfig.JitDisasmWithDebugInfo() != 0);
        INDEBUG(addRichMappings |= JitConfig.WriteRichDebugInfoFile() != nullptr);

        DebugInfo currentDI;
        for (GenTree* node : LIR::AsRange(block))
        {
            // Do we have a new IL offset?
            if (node->OperIs(GT_IL_OFFSET))
            {
                GenTreeILOffset* ilOffset = node->AsILOffset();
                DebugInfo        rootDI   = ilOffset->gtStmtDI.GetRoot();
                if (rootDI.IsValid())
                {
                    genEnsureCodeEmitted(currentDI);
                    currentDI = rootDI;

                    // We need a tie breaker when we have multiple IL offsets that map to the same native offset.
                    // Normally we pick the latest, but for block joins we pick the earliest to ensure end up with
                    // a mapping to that IL offset. Async mappings should not participate in this -- they are
                    // internally produced and never fall on the join point in the IL.
                    // See genIPmappingGen for the tiebreaker.
                    bool isLabel = !producedLabelMapping && !currentDI.GetLocation().IsAsync();
                    genIPmappingAdd(IPmappingDscKind::Normal, currentDI, isLabel);
                    producedLabelMapping |= isLabel;
                }

                if (addRichMappings && ilOffset->gtStmtDI.IsValid())
                {
                    genAddRichIPMappingHere(ilOffset->gtStmtDI);
                }

#ifdef DEBUG
                assert(ilOffset->gtStmtLastILoffs <= compiler->info.compILCodeSize ||
                       ilOffset->gtStmtLastILoffs == BAD_IL_OFFSET);

                if (compiler->opts.dspCode && compiler->opts.dspInstrs && ilOffset->gtStmtLastILoffs != BAD_IL_OFFSET)
                {
                    while (genCurDispOffset <= ilOffset->gtStmtLastILoffs)
                    {
                        genCurDispOffset += dumpSingleInstr(compiler->info.compCode, genCurDispOffset, ">    ");
                    }
                }

#endif // DEBUG
            }

            genCodeForTreeNode(node);
            if (node->gtHasReg(compiler) && node->IsUnusedValue())
            {
                genConsumeReg(node);
            }
        } // end for each node in block

#if FALSE

#ifdef DEBUG
        // The following set of register spill checks and GC pointer tracking checks used to be
        // performed at statement boundaries. Now, with LIR, there are no statements, so they are
        // performed at the end of each block.
        // TODO: could these checks be performed more frequently? E.g., at each location where
        // the register allocator says there are no live non-variable registers. Perhaps this could
        // be done by using the map maintained by LSRA (operandToLocationInfoMap) to mark a node
        // somehow when, after the execution of that node, there will be no live non-variable registers.

        regSet.rsSpillChk();

        // Make sure we didn't bungle pointer register tracking

        regMaskTP ptrRegs       = gcInfo.gcRegGCrefSetCur | gcInfo.gcRegByrefSetCur;
        regMaskTP nonVarPtrRegs = ptrRegs & ~regSet.GetMaskVars();

        // If this is a return block then we expect some live GC regs. Clear those.
        if (compiler->compMethodReturnsRetBufAddr())
        {
            nonVarPtrRegs &= ~RBM_INTRET;
        }
        else
        {
            const ReturnTypeDesc& retTypeDesc = compiler->compRetTypeDesc;
            const unsigned        regCount    = retTypeDesc.GetReturnRegCount();

            for (unsigned i = 0; i < regCount; ++i)
            {
                regNumber reg = retTypeDesc.GetABIReturnReg(i, compiler->info.compCallConv);
                nonVarPtrRegs &= ~genRegMask(reg);
            }
        }

        if (compiler->compIsAsync())
        {
            nonVarPtrRegs &= ~RBM_ASYNC_CONTINUATION_RET;
        }

        // For a tailcall arbitrary argument registers may be live into the
        // epilog. Skip validating those.
        if (block->HasFlag(BBF_HAS_JMP))
        {
            nonVarPtrRegs &= ~fullIntArgRegMask(CorInfoCallConvExtension::Managed);
        }

        if (nonVarPtrRegs)
        {
            printf("Regset after " FMT_BB " gcr=", block->bbNum);
            printRegMaskInt(gcInfo.gcRegGCrefSetCur & ~regSet.GetMaskVars());
            compiler->GetEmitter()->emitDispRegSet(gcInfo.gcRegGCrefSetCur & ~regSet.GetMaskVars());
            printf(", byr=");
            printRegMaskInt(gcInfo.gcRegByrefSetCur & ~regSet.GetMaskVars());
            compiler->GetEmitter()->emitDispRegSet(gcInfo.gcRegByrefSetCur & ~regSet.GetMaskVars());
            printf(", regVars=");
            printRegMaskInt(regSet.GetMaskVars());
            compiler->GetEmitter()->emitDispRegSet(regSet.GetMaskVars());
            printf("\n");
        }

        noway_assert(nonVarPtrRegs == RBM_NONE);
#endif // DEBUG

        // It is possible to reach the end of the block without generating code for the current IL offset.
        // For example, if the following IR ends the current block, no code will have been generated for
        // offset 21:
        //
        //          (  0,  0) [000040] ------------                il_offset void   IL offset: 21
        //
        //     N001 (  0,  0) [000039] ------------                nop       void
        //
        // This can lead to problems when debugging the generated code. To prevent these issues, make sure
        // we've generated code for the last IL offset we saw in the block.
        genEnsureCodeEmitted(currentDI);

        /* Is this the last block, and are there any open scopes left ? */

        bool isLastBlockProcessed;
        if (block->isBBCallFinallyPair())
        {
            isLastBlockProcessed = block->Next()->IsLast();
        }
        else
        {
            isLastBlockProcessed = block->IsLast();
        }

        if (compiler->opts.compDbgInfo && isLastBlockProcessed)
        {
            varLiveKeeper->siEndAllVariableLiveRange(compiler->compCurLife);
        }

        if (compiler->opts.compScopeInfo && (compiler->info.compVarScopesCount > 0))
        {
            siEndBlock(block);
        }

#ifdef DEBUG
        // compCurLife should be equal to the liveOut set, except that we don't keep
        // it up to date for vars that are not register candidates
        // (it would be nice to have a xor set function)

        VARSET_TP mismatchLiveVars(VarSetOps::Diff(compiler, block->bbLiveOut, compiler->compCurLife));
        VarSetOps::UnionD(compiler, mismatchLiveVars,
                          VarSetOps::Diff(compiler, compiler->compCurLife, block->bbLiveOut));
        VarSetOps::Iter mismatchLiveVarIter(compiler, mismatchLiveVars);
        unsigned        mismatchLiveVarIndex  = 0;
        bool            foundMismatchedRegVar = false;
        while (mismatchLiveVarIter.NextElem(&mismatchLiveVarIndex))
        {
            LclVarDsc* varDsc = compiler->lvaGetDescByTrackedIndex(mismatchLiveVarIndex);
            if (varDsc->lvIsRegCandidate())
            {
                if (!foundMismatchedRegVar)
                {
                    JITDUMP("Mismatched live reg vars after " FMT_BB ":", block->bbNum);
                    foundMismatchedRegVar = true;
                }
                JITDUMP(" V%02u", compiler->lvaTrackedIndexToLclNum(mismatchLiveVarIndex));
            }
        }
        if (foundMismatchedRegVar)
        {
            JITDUMP("\n");
            assert(!"Found mismatched live reg var(s) after block");
        }
#endif

#endif // FALSE (wasm temp)

        // Compute the depth of the block ending at targetNum
        // or (if isBackedge) the loop starting at targetNum
        // in the wasm control flow stack
        //
        auto findDepth = [&wasmControlFlowStack](unsigned targetNum, bool isBackedge, unsigned& match) {
            int const h = wasmControlFlowStack.Height();

            for (int i = 0; i < h; i++)
            {
                WasmInterval* const ii = wasmControlFlowStack.Top(i);
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

        // Now emit any block-ending control flow
        //
        switch (block->GetKind())
        {
            case BBJ_RETURN:
                instGen(INS_return);
                break;

            case BBJ_THROW:
                instGen(INS_unreachable);
                break;

            case BBJ_CALLFINALLY:
                genCallFinally(block);
                if (!block->isBBCallFinallyPair())
                {
                    instGen(INS_unreachable);
                }
                break;

            case BBJ_EHCATCHRET:
                assert(compiler->UsesFunclets());
                genEHCatchRet(block);
                FALLTHROUGH;

            case BBJ_EHFINALLYRET:
            case BBJ_EHFAULTRET:
            case BBJ_EHFILTERRET:
                if (compiler->UsesFunclets())
                {
                    genReserveFuncletEpilog(block);
                }
                instGen(INS_return);
                break;

            case BBJ_SWITCH:
            {
                BBswtDesc* const desc      = block->GetSwitchTargets();
                unsigned const   caseCount = desc->GetCaseCount();

                assert(!desc->HasDefaultCase());

                if (caseCount == 0)
                {
                    break;
                }

                inst_JMP(EJ_br_table, caseCount);

                for (unsigned caseNum = 0; caseNum < caseCount; caseNum++)
                {
                    BasicBlock* const caseTarget    = desc->GetCase(caseNum)->getDestinationBlock();
                    unsigned const    caseTargetNum = caseTarget->bbPreorderNum;

                    bool const isBackedge = caseTargetNum <= cursor;
                    unsigned   blockNum   = 0;
                    unsigned   depth      = findDepth(caseTargetNum, isBackedge, blockNum);

                    inst_LABEL(depth);
                }

                JITDUMP("\n");
                break;
            }

            case BBJ_CALLFINALLYRET:
            case BBJ_ALWAYS:
            {
#ifdef DEBUG
                GenTree* call = block->lastNode();
                if ((call != nullptr) && call->OperIs(GT_CALL))
                {
                    // At this point, BBJ_ALWAYS should never end with a call that doesn't return.
                    assert(!call->AsCall()->IsNoReturn());
                }
#endif // DEBUG

                unsigned const succNum = block->GetTarget()->bbPreorderNum;

                // If this block jumps to the next one, we might be able to skip emitting the jump
                if (block->CanRemoveJumpToNext(compiler))
                {
                    assert(succNum == (cursor + 1));
                    break;
                }

                bool const     isBackedge = succNum <= cursor;
                unsigned       blockNum   = 0;
                unsigned const depth      = findDepth(succNum, isBackedge, blockNum);
                inst_JMP(EJ_br, depth);
            }

            case BBJ_COND:
            {
                const unsigned trueNum  = block->GetTrueTarget()->bbPreorderNum;
                const unsigned falseNum = block->GetFalseTarget()->bbPreorderNum;

                // We don't expect degenerate BBJ_COND
                //
                assert(trueNum != falseNum);

                // We don't expect the true target to be the next block.
                //
                const bool reverseCondition = trueNum == (cursor + 1);
                assert(!reverseCondition);

                // br_if for true target
                //
                bool const isTrueBackedge = trueNum <= cursor;
                unsigned   blockNum       = 0;
                unsigned   depth          = findDepth(trueNum, isTrueBackedge, blockNum);
                inst_JMP(EJ_br_if, depth);

                // br for false target, if not fallthrough
                //
                const bool fallThrough = falseNum == (cursor + 1);
                if (fallThrough)
                {
                    break;
                }

                bool const isFalseBackedge = falseNum <= cursor;
                blockNum                   = 0;
                depth                      = findDepth(falseNum, isFalseBackedge, blockNum);
                inst_JMP(EJ_br, depth);

                break;
            }

            default:
                noway_assert(!"Unexpected bbKind");
                break;
        }

#ifdef DEBUG
        if (compiler->verbose)
        {
            varLiveKeeper->dumpBlockVariableLiveRanges(block);
        }
        compiler->compCurBB = nullptr;
#endif // DEBUG
    }  //------------------ END-FOR each block of the method -------------------

    // There could be variables alive at this point. For example see lvaKeepAliveAndReportThis.
    // This call is for cleaning the GC refs
    genUpdateLife(VarSetOps::MakeEmpty(compiler));

    // Finalize the spill  tracking logic

    regSet.rsSpillEnd();

    // Finalize the temp   tracking logic

    regSet.tmpEnd();

#ifdef DEBUG
    if (compiler->verbose)
    {
        printf("\n# ");
        printf("compCycleEstimate = %6d, compSizeEstimate = %5d ", compiler->compCycleEstimate,
               compiler->compSizeEstimate);
        printf("%s\n", compiler->info.compFullName);
    }
#endif
}
