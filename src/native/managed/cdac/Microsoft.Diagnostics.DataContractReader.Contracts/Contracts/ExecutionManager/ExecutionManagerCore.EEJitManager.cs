// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using Microsoft.Diagnostics.DataContractReader.ExecutionManagerHelpers;

namespace Microsoft.Diagnostics.DataContractReader.Contracts;

internal partial class ExecutionManagerCore<T> : IExecutionManager
{
    private sealed class EEJitManager : JitManager
    {
        private readonly INibbleMap _nibbleMap;
        private readonly RuntimeFunctionLookup _runtimeFunctions;
        public EEJitManager(Target target, INibbleMap nibbleMap) : base(target)
        {
            _nibbleMap = nibbleMap;
            _runtimeFunctions = RuntimeFunctionLookup.Create(target);
        }

        public override bool GetMethodInfo(RangeSection rangeSection, TargetCodePointer jittedCodeAddress, [NotNullWhen(true)] out CodeBlock? info)
        {
            info = null;
            // EEJitManager::JitCodeToMethodInfo
            if (rangeSection.IsRangeList)
                return false;

            if (rangeSection.Data == null)
                throw new ArgumentException(nameof(rangeSection));

            TargetPointer codeStart = FindMethodCode(rangeSection, jittedCodeAddress);
            if (codeStart == TargetPointer.Null)
                return false;

            Debug.Assert(codeStart.Value <= jittedCodeAddress.Value);
            TargetPointer hotCodeStart = GetCodeHeaderAddress(rangeSection, codeStart) + (ulong)Target.PointerSize;
            TargetPointer instrPointer = CodePointerUtils.AddressFromCodePointer(jittedCodeAddress, Target);
            TargetNUInt relativeOffset = new TargetNUInt(instrPointer.Value - codeStart.Value);

            if (!GetRealCodeHeader(rangeSection, codeStart, out Data.RealCodeHeader? realCodeHeader))
                return false;

            if (codeStart != hotCodeStart)
            {
                if (realCodeHeader.ColdCodeHeader == TargetPointer.Null ||
                    realCodeHeader.NumUnwindInfos <= 1)
                {
                    return false;
                }

                TargetPointer coldStart = realCodeHeader.ColdCodeHeader + (ulong)Target.PointerSize;
                if (codeStart != coldStart)
                    return false;

                uint hotSize = GetHotCodeSize(rangeSection, realCodeHeader, hotCodeStart, coldStart);
                relativeOffset = new TargetNUInt(hotSize + instrPointer.Value - coldStart.Value);
            }

            info = new CodeBlock(hotCodeStart.Value, realCodeHeader.MethodDesc, relativeOffset, rangeSection.Data!.JitManager);
            return true;
        }

        public override TargetPointer GetUnwindInfo(RangeSection rangeSection, TargetCodePointer jittedCodeAddress)
        {
            if (!TryGetRuntimeFunction(
                    rangeSection, jittedCodeAddress, out Data.RealCodeHeader? realCodeHeader, out _, out uint index))
            {
                return TargetPointer.Null;
            }

            return _runtimeFunctions.GetRuntimeFunctionAddress(realCodeHeader.UnwindInfos, index);
        }

        public override TargetPointer GetFuncletStartAddress(RangeSection rangeSection, TargetCodePointer jittedCodeAddress)
        {
            if (Target.Contracts.RuntimeInfo.GetTargetArchitecture() is not RuntimeInfoArchitecture.Arm64)
                return base.GetFuncletStartAddress(rangeSection, jittedCodeAddress);

            if (!TryGetRuntimeFunction(
                    rangeSection, jittedCodeAddress, out Data.RealCodeHeader? realCodeHeader, out TargetPointer imageBase, out uint index))
            {
                return TargetPointer.Null;
            }

            Data.RuntimeFunction function = _runtimeFunctions.GetRuntimeFunction(realCodeHeader.UnwindInfos, index);
            while (index > 0 && IsArm64FunctionFragment(imageBase, function))
            {
                function = _runtimeFunctions.GetRuntimeFunction(realCodeHeader.UnwindInfos, --index);
            }

            return CodePointerUtils.AddressFromCodePointer(
                new TargetCodePointer(imageBase + function.BeginAddress), Target);
        }

        public override void GetGCInfo(RangeSection rangeSection, TargetCodePointer jittedCodeAddress, out TargetPointer gcInfo, out uint gcVersion)
        {
            gcInfo = TargetPointer.Null;
            gcVersion = 0;

            // EEJitManager::GetGCInfoToken
            if (rangeSection.IsRangeList)
                return;

            if (rangeSection.Data == null)
                throw new ArgumentException(nameof(rangeSection));

            TargetPointer codeStart = FindMethodCode(rangeSection, jittedCodeAddress);
            if (codeStart == TargetPointer.Null)
                return;
            Debug.Assert(codeStart.Value <= jittedCodeAddress.Value);

            if (!GetRealCodeHeader(rangeSection, codeStart, out Data.RealCodeHeader? realCodeHeader))
                return;

            gcVersion = Target.ReadGlobal<uint>(Constants.Globals.GCInfoVersion);
            gcInfo = realCodeHeader.GCInfo;
        }

        private TargetPointer FindMethodCode(RangeSection rangeSection, TargetCodePointer jittedCodeAddress)
        {
            // EEJitManager::FindMethodCode
            Debug.Assert(rangeSection.Data != null);

            if (!rangeSection.IsCodeHeap)
                throw new InvalidOperationException("RangeSection is not a code heap");

            TargetPointer heapListAddress = rangeSection.Data.HeapList;
            Data.CodeHeapListNode heapListNode = Target.ProcessedData.GetOrAdd<Data.CodeHeapListNode>(heapListAddress);
            return _nibbleMap.FindMethodCode(heapListNode, jittedCodeAddress);
        }

        private uint GetHotCodeSize(
            RangeSection rangeSection,
            Data.RealCodeHeader realCodeHeader,
            TargetPointer hotCodeStart,
            TargetPointer coldCodeStart)
        {
            TargetPointer imageBase = rangeSection.Data!.RangeBegin;
            uint hotCodeStartOffset = checked((uint)(hotCodeStart - imageBase));
            uint coldCodeStartOffset = checked((uint)(coldCodeStart - imageBase));
            uint hotCodeEndOffset = hotCodeStartOffset;

            for (uint i = 0; i < realCodeHeader.NumUnwindInfos; i++)
            {
                Data.RuntimeFunction function =
                    _runtimeFunctions.GetRuntimeFunction(realCodeHeader.UnwindInfos, i);
                if (function.BeginAddress >= coldCodeStartOffset)
                    continue;

                uint functionEndOffset =
                    checked(function.BeginAddress + _runtimeFunctions.GetFunctionLength(imageBase, function));
                hotCodeEndOffset = Math.Max(hotCodeEndOffset, functionEndOffset);
            }

            Debug.Assert(hotCodeEndOffset > hotCodeStartOffset);
            return checked(hotCodeEndOffset - hotCodeStartOffset);
        }

        private TargetPointer GetCodeHeaderAddress(RangeSection rangeSection, TargetPointer codeStart)
        {
            Debug.Assert(!rangeSection.IsRangeList);
            if (rangeSection.Data == null)
                throw new ArgumentException(nameof(rangeSection));

            TargetPointer codeHeaderAddress = codeStart - (ulong)Target.PointerSize;
            Data.CodeHeapListNode heapListNode =
                Target.ProcessedData.GetOrAdd<Data.CodeHeapListNode>(rangeSection.Data.HeapList);
            if (codeHeaderAddress >= heapListNode.BottomEndAddress)
            {
                // A cold-code header points back to the hot CodeHeader.
                codeHeaderAddress = Target.ReadPointer(codeHeaderAddress);
            }

            return codeHeaderAddress;
        }

        private bool GetRealCodeHeader(RangeSection rangeSection, TargetPointer codeStart, [NotNullWhen(true)] out Data.RealCodeHeader? realCodeHeader)
        {
            realCodeHeader = null;
            TargetPointer codeHeaderAddress = GetCodeHeaderAddress(rangeSection, codeStart);
            TargetPointer realCodeHeaderAddress = Target.ReadPointer(codeHeaderAddress);
            if (RangeSection.IsStubCodeBlock(Target, realCodeHeaderAddress))
            {
                return false;
            }
            realCodeHeader = Target.ProcessedData.GetOrAdd<Data.RealCodeHeader>(realCodeHeaderAddress);
            return true;
        }

        private bool TryGetRuntimeFunction(
            RangeSection rangeSection,
            TargetCodePointer jittedCodeAddress,
            [NotNullWhen(true)] out Data.RealCodeHeader? realCodeHeader,
            out TargetPointer imageBase,
            out uint index)
        {
            realCodeHeader = null;
            imageBase = TargetPointer.Null;
            index = 0;

            Debug.Assert(!rangeSection.IsRangeList);
            if (rangeSection.Data == null)
                throw new ArgumentException(nameof(rangeSection));

            TargetPointer codeStart = FindMethodCode(rangeSection, jittedCodeAddress);
            if (codeStart == TargetPointer.Null)
                return false;
            Debug.Assert(codeStart.Value <= jittedCodeAddress.Value);

            if (!GetRealCodeHeader(rangeSection, codeStart, out realCodeHeader) ||
                realCodeHeader.NumUnwindInfos == 0)
            {
                return false;
            }

            TargetPointer addr = CodePointerUtils.AddressFromCodePointer(jittedCodeAddress, Target);
            imageBase = rangeSection.Data.RangeBegin;
            TargetPointer relativeAddr = addr - imageBase;
            return _runtimeFunctions.TryGetRuntimeFunctionIndexForAddress(
                realCodeHeader.UnwindInfos, realCodeHeader.NumUnwindInfos, relativeAddr, out index);
        }

        private bool IsArm64FunctionFragment(TargetPointer imageBase, Data.RuntimeFunction function)
        {
            if ((function.UnwindData & 3) != 0)
                return false;

            TargetPointer unwindData = imageBase + function.UnwindData;
            uint unwindHeader = Target.Read<uint>(unwindData);
            if (((unwindHeader >> 18) & 3) != 0)
                return false;

            uint epilogCount = (unwindHeader >> 22) & 0x1f;
            uint codeWords = unwindHeader >> 27;
            TargetPointer unwindCodes = unwindData + sizeof(uint);
            if (codeWords == 0 && epilogCount == 0)
            {
                uint extendedHeader = Target.Read<uint>(unwindCodes);
                epilogCount = extendedHeader & 0xffff;
                unwindCodes += sizeof(uint);
            }

            bool hasSingleEpilog = (unwindHeader & (1 << 21)) != 0;
            if (!hasSingleEpilog)
                unwindCodes += epilogCount * sizeof(uint);

            return Target.Read<byte>(unwindCodes) == 0xe5;
        }
    }
}
