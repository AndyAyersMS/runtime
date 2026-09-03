// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using Xunit;

using System.Collections.Generic;
using System.Linq;
using Microsoft.Diagnostics.DataContractReader.Contracts;
using Moq;

namespace Microsoft.Diagnostics.DataContractReader.Tests.ExecutionManager;

public class ExecutionManagerTests
{
    private static Target CreateTarget(
        MockDescriptors.ExecutionManager emBuilder,
        RuntimeInfoArchitecture? targetArchitecture = null,
        params (string Name, ulong Value)[] additionalGlobals)
    {
        var arch = emBuilder.Builder.TargetTestHelpers.Arch;
        TestPlaceholderTarget.ReadFromTargetDelegate reader = emBuilder.Builder.GetMemoryContext().ReadFromTarget;
        var target = new TestPlaceholderTarget(
            arch,
            reader,
            emBuilder.Types,
            emBuilder.Globals.Concat(additionalGlobals).ToArray());
        IContractFactory<IExecutionManager> emfactory = new ExecutionManagerFactory();
        RuntimeInfoArchitecture architecture = targetArchitecture ?? (arch.Is64Bit
            ? RuntimeInfoArchitecture.X64
            : RuntimeInfoArchitecture.X86);
        IRuntimeInfo runtimeInfo = Mock.Of<IRuntimeInfo>(r => r.GetTargetArchitecture() == architecture);
        ContractRegistry reg = Mock.Of<ContractRegistry>(
            c => c.ExecutionManager == emfactory.CreateContract(target, emBuilder.Version)
                && c.PlatformMetadata == new Mock<IPlatformMetadata>().Object
                && c.RuntimeInfo == runtimeInfo);
        target.SetContracts(reg);
        return target;
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetCodeBlockHandle_Null(int version, MockTarget.Architecture arch)
    {
        MockDescriptors.ExecutionManager emBuilder = new (version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var target = CreateTarget(emBuilder);

        var em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);
        var eeInfo = em.GetCodeBlockHandle(TargetCodePointer.Null);
        Assert.Null(eeInfo);
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetCodeBlockHandle_NoRangeSections(int version, MockTarget.Architecture arch)
    {
        MockDescriptors.ExecutionManager emBuilder = new (version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var target = CreateTarget(emBuilder);

        var em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);
        var eeInfo = em.GetCodeBlockHandle(new TargetCodePointer(0x0a0a_0000));
        Assert.Null(eeInfo);
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetMethodDesc_OneRangeOneMethod(int version, MockTarget.Architecture arch)
    {
        const ulong codeRangeStart = 0x0a0a_0000u; // arbitrary
        const uint codeRangeSize = 0xc000u; // arbitrary
        const uint methodSize = 0x450; // arbitrary

        TargetPointer jitManagerAddress = new (0x000b_ff00); // arbitrary

        TargetPointer expectedMethodDescAddress = new TargetPointer(0x0101_aaa0);

        MockDescriptors.ExecutionManager emBuilder = new(version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var jittedCode = emBuilder.AllocateJittedCodeRange(codeRangeStart, codeRangeSize);

        TargetCodePointer methodStart = emBuilder.AddJittedMethod(jittedCode, methodSize, expectedMethodDescAddress);

        NibbleMapTestBuilderBase nibBuilder = emBuilder.CreateNibbleMap(codeRangeStart, codeRangeSize);
        nibBuilder.AllocateCodeChunk(methodStart, methodSize);

        TargetPointer codeHeapListNodeAddress = emBuilder.AddCodeHeapListNode(TargetPointer.Null, codeRangeStart, codeRangeStart + codeRangeSize, codeRangeStart, nibBuilder.NibbleMapFragment.Address);
        TargetPointer rangeSectionAddress = emBuilder.AddRangeSection(jittedCode, jitManagerAddress: jitManagerAddress, codeHeapListNodeAddress: codeHeapListNodeAddress);
        TargetPointer rangeSectionFragmentAddress = emBuilder.AddRangeSectionFragment(jittedCode, rangeSectionAddress);

        var target = CreateTarget(emBuilder);

        var em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);

        // test at method start
        var eeInfo = em.GetCodeBlockHandle(methodStart);
        Assert.NotNull(eeInfo);
        TargetPointer actualMethodDesc = em.GetMethodDesc(eeInfo.Value);
        Assert.Equal(expectedMethodDescAddress, actualMethodDesc);

        // test middle of method
        eeInfo = em.GetCodeBlockHandle(methodStart + methodSize / 2);
        Assert.NotNull(eeInfo);
        actualMethodDesc = em.GetMethodDesc(eeInfo.Value);
        Assert.Equal(expectedMethodDescAddress, actualMethodDesc);

        // test end of method
        eeInfo = em.GetCodeBlockHandle(methodStart + methodSize - 1);
        Assert.NotNull(eeInfo);
        actualMethodDesc = em.GetMethodDesc(eeInfo.Value);
        Assert.Equal(expectedMethodDescAddress, actualMethodDesc);
    }

    [Theory]
    [MemberData(nameof(Arm64AllVersions))]
    public void GetJittedMethodInfo_HotColdArm64(int version, MockTarget.Architecture arch)
    {
        const ulong CodeRangeStart = 0x0a0a_0000;
        const uint CodeRangeSize = 0xc000;
        const uint HotSize = 0x40;
        const uint ColdSize = 0x40;
        const ulong JitManagerAddress = 0x000b_ff00;
        const ulong MethodDescAddress = 0x0101_aaa0;
        const ulong GCInfoAddress = 0x0101_b000;

        MockDescriptors.ExecutionManager emBuilder =
            new(version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        MockDescriptors.ExecutionManager.JittedCodeRange jittedCode =
            emBuilder.AllocateJittedCodeRange(CodeRangeStart, CodeRangeSize);
        MockDescriptors.ExecutionManager.HotColdJittedMethod method = emBuilder.AddHotColdJittedMethod(
            jittedCode, HotSize, ColdSize, MethodDescAddress, CodeRangeStart, GCInfoAddress);

        NibbleMapTestBuilderBase nibBuilder = emBuilder.CreateNibbleMap(CodeRangeStart, CodeRangeSize);
        nibBuilder.AllocateCodeChunk(new TargetCodePointer(method.HotCodeAddress), HotSize);
        nibBuilder.AllocateCodeChunk(new TargetCodePointer(method.ColdCodeAddress), ColdSize);

        TargetPointer codeHeapListNodeAddress = emBuilder.AddCodeHeapListNode(
            TargetPointer.Null,
            CodeRangeStart,
            method.HotCodeAddress + HotSize,
            CodeRangeStart,
            nibBuilder.NibbleMapFragment.Address,
            method.ColdCodeAddress - (ulong)(arch.Is64Bit ? sizeof(ulong) : sizeof(uint)));
        TargetPointer rangeSectionAddress =
            emBuilder.AddRangeSection(jittedCode, JitManagerAddress, codeHeapListNodeAddress);
        _ = emBuilder.AddRangeSectionFragment(jittedCode, rangeSectionAddress);

        Target target = CreateTarget(emBuilder, RuntimeInfoArchitecture.Arm64);
        IExecutionManager em = target.Contracts.ExecutionManager;

        CodeBlockHandle? hotHandleValue =
            em.GetCodeBlockHandle(new TargetCodePointer(method.HotCodeAddress + 4));
        CodeBlockHandle? coldRootHandleValue =
            em.GetCodeBlockHandle(new TargetCodePointer(method.ColdCodeAddress + 4));
        CodeBlockHandle? coldFuncletHandleValue =
            em.GetCodeBlockHandle(new TargetCodePointer(method.ColdFuncletAddress + 4));
        CodeBlockHandle? coldFuncletFragmentHandleValue =
            em.GetCodeBlockHandle(new TargetCodePointer(method.ColdFuncletAddress + 0x14));
        Assert.NotNull(hotHandleValue);
        Assert.NotNull(coldRootHandleValue);
        Assert.NotNull(coldFuncletHandleValue);
        Assert.NotNull(coldFuncletFragmentHandleValue);

        CodeBlockHandle hotHandle = hotHandleValue.Value;
        CodeBlockHandle coldRootHandle = coldRootHandleValue.Value;
        CodeBlockHandle coldFuncletHandle = coldFuncletHandleValue.Value;
        CodeBlockHandle coldFuncletFragmentHandle = coldFuncletFragmentHandleValue.Value;

        foreach (CodeBlockHandle handle in new[] { hotHandle, coldRootHandle, coldFuncletHandle, coldFuncletFragmentHandle })
        {
            Assert.Equal(new TargetPointer(MethodDescAddress), em.GetMethodDesc(handle));
            Assert.Equal(new TargetCodePointer(method.HotCodeAddress), em.GetStartAddress(handle));
        }

        Assert.Equal(new TargetNUInt(4), em.GetRelativeOffset(hotHandle));
        Assert.Equal(new TargetNUInt(HotSize + 4), em.GetRelativeOffset(coldRootHandle));
        Assert.Equal(new TargetNUInt(HotSize + 0x14), em.GetRelativeOffset(coldFuncletHandle));
        Assert.Equal(new TargetCodePointer(method.HotCodeAddress), em.GetFuncletStartAddress(coldRootHandle));
        Assert.Equal(new TargetCodePointer(method.ColdFuncletAddress), em.GetFuncletStartAddress(coldFuncletHandle));
        Assert.Equal(new TargetCodePointer(method.ColdFuncletAddress), em.GetFuncletStartAddress(coldFuncletFragmentHandle));

        Target x64Target = CreateTarget(emBuilder, RuntimeInfoArchitecture.X64);
        IExecutionManager x64Em = x64Target.Contracts.ExecutionManager;
        CodeBlockHandle? x64ColdRootHandleValue =
            x64Em.GetCodeBlockHandle(new TargetCodePointer(method.ColdCodeAddress + 4));
        Assert.NotNull(x64ColdRootHandleValue);
        Assert.Equal(new TargetCodePointer(method.HotCodeAddress), x64Em.GetStartAddress(x64ColdRootHandleValue.Value));
        Assert.Equal(new TargetNUInt(HotSize + 4), x64Em.GetRelativeOffset(x64ColdRootHandleValue.Value));
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetCodeBlockHandle_OneRangeZeroMethod(int version, MockTarget.Architecture arch)
    {
        const ulong codeRangeStart = 0x0a0a_0000u; // arbitrary
        const uint codeRangeSize = 0xc000u; // arbitrary

        TargetPointer jitManagerAddress = new (0x000b_ff00); // arbitrary

        MockDescriptors.ExecutionManager emBuilder = new(version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var jittedCode = emBuilder.AllocateJittedCodeRange(codeRangeStart, codeRangeSize);

        NibbleMapTestBuilderBase nibBuilder = emBuilder.CreateNibbleMap(codeRangeStart, codeRangeSize);

        TargetPointer codeHeapListNodeAddress = emBuilder.AddCodeHeapListNode(TargetPointer.Null, codeRangeStart, codeRangeStart + codeRangeSize, codeRangeStart, nibBuilder.NibbleMapFragment.Address);
        TargetPointer rangeSectionAddress = emBuilder.AddRangeSection(jittedCode, jitManagerAddress: jitManagerAddress, codeHeapListNodeAddress: codeHeapListNodeAddress);
        TargetPointer rangeSectionFragmentAddress = emBuilder.AddRangeSectionFragment(jittedCode, rangeSectionAddress);

        var target = CreateTarget(emBuilder);

        var em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);

        // test at code range start
        var eeInfo = em.GetCodeBlockHandle(codeRangeSize + codeRangeSize);
        Assert.Null(eeInfo);

        // test middle of code range
        eeInfo = em.GetCodeBlockHandle(codeRangeSize + codeRangeSize / 2);
        Assert.Null(eeInfo);

        // test end of code range
        eeInfo = em.GetCodeBlockHandle(codeRangeSize + codeRangeSize - 1);
        Assert.Null(eeInfo);
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetUnwindInfoBaseAddress_OneRangeOneMethod(int version, MockTarget.Architecture arch)
    {
        const ulong codeRangeStart = 0x0a0a_0000u; // arbitrary
        const uint codeRangeSize = 0xc000u; // arbitrary
        const uint methodSize = 0x450; // arbitrary

        TargetPointer jitManagerAddress = new (0x000b_ff00); // arbitrary

        MockDescriptors.ExecutionManager emBuilder = new(version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var jittedCode = emBuilder.AllocateJittedCodeRange(codeRangeStart, codeRangeSize);

        TargetCodePointer methodStart = emBuilder.AddJittedMethod(jittedCode, methodSize, 0x0101_aaa0);

        NibbleMapTestBuilderBase nibBuilder = emBuilder.CreateNibbleMap(codeRangeStart, codeRangeSize);
        nibBuilder.AllocateCodeChunk(methodStart, methodSize);

        TargetPointer codeHeapListNodeAddress = emBuilder.AddCodeHeapListNode(TargetPointer.Null, codeRangeStart, codeRangeStart + codeRangeSize, codeRangeStart, nibBuilder.NibbleMapFragment.Address);
        TargetPointer rangeSectionAddress = emBuilder.AddRangeSection(jittedCode, jitManagerAddress: jitManagerAddress, codeHeapListNodeAddress: codeHeapListNodeAddress);
        TargetPointer rangeSectionFragmentAddress = emBuilder.AddRangeSectionFragment(jittedCode, rangeSectionAddress);

        var target = CreateTarget(emBuilder);

        var em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);

        // Get CodeBlockHandle
        var eeInfo = em.GetCodeBlockHandle(methodStart);
        Assert.NotNull(eeInfo);
        TargetPointer actualBaseAddress = em.GetUnwindInfoBaseAddress(eeInfo.Value);
        Assert.Equal(new TargetPointer(actualBaseAddress), actualBaseAddress);
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetCodeBlockHandle_R2R_NoRuntimeFunctionMatch(int version, MockTarget.Architecture arch)
    {
        const ulong codeRangeStart = 0x0a0a_0000u; // arbitrary
        const uint codeRangeSize = 0xc000u; // arbitrary
        TargetPointer jitManagerAddress = new(0x000b_ff00); // arbitrary

        MockDescriptors.ExecutionManager emBuilder = new(version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var jittedCode = emBuilder.AllocateJittedCodeRange(codeRangeStart, codeRangeSize);

        uint runtimeFunction = 0x100;

        TargetPointer r2rInfo = emBuilder.AddReadyToRunInfo([runtimeFunction], []);
        MockDescriptors.HashMap hashMapBuilder = new(emBuilder.Builder);
        hashMapBuilder.PopulatePtrMap(
            r2rInfo + (uint)emBuilder.Types[DataType.ReadyToRunInfo].Fields[nameof(Data.ReadyToRunInfo.EntryPointToMethodDescMap)].Offset,
            []);

        TargetPointer r2rModule = emBuilder.AddReadyToRunModule(r2rInfo);
        TargetPointer rangeSectionAddress = emBuilder.AddReadyToRunRangeSection(jittedCode, jitManagerAddress, r2rModule);
        _ = emBuilder.AddRangeSectionFragment(jittedCode, rangeSectionAddress);

        Target target = CreateTarget(emBuilder);

        IExecutionManager em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);

        // Before any functions
        var handle = em.GetCodeBlockHandle(codeRangeStart + runtimeFunction - 1);
        Assert.Null(handle);
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetMethodDesc_R2R_OneRuntimeFunction(int version, MockTarget.Architecture arch)
    {
        const ulong codeRangeStart = 0x0a0a_0000u; // arbitrary
        const uint codeRangeSize = 0xc000u; // arbitrary
        TargetPointer jitManagerAddress = new(0x000b_ff00); // arbitrary

        TargetPointer expectedMethodDescAddress = new TargetPointer(0x0101_aaa0);

        MockDescriptors.ExecutionManager emBuilder = new(version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var jittedCode = emBuilder.AllocateJittedCodeRange(codeRangeStart, codeRangeSize);

        uint expectedRuntimeFunction = 0x100;

        TargetPointer r2rInfo = emBuilder.AddReadyToRunInfo([expectedRuntimeFunction], []);
        MockDescriptors.HashMap hashMapBuilder = new(emBuilder.Builder);
        hashMapBuilder.PopulatePtrMap(
            r2rInfo + (uint)emBuilder.Types[DataType.ReadyToRunInfo].Fields[nameof(Data.ReadyToRunInfo.EntryPointToMethodDescMap)].Offset,
            [(jittedCode.RangeStart + expectedRuntimeFunction, expectedMethodDescAddress)]);

        TargetPointer r2rModule = emBuilder.AddReadyToRunModule(r2rInfo);
        TargetPointer rangeSectionAddress = emBuilder.AddReadyToRunRangeSection(jittedCode, jitManagerAddress, r2rModule);
        _ = emBuilder.AddRangeSectionFragment(jittedCode, rangeSectionAddress);

        Target target = CreateTarget(emBuilder);

        IExecutionManager em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);

        {
            // Function start
            var handle = em.GetCodeBlockHandle(codeRangeStart + expectedRuntimeFunction);
            Assert.NotNull(handle);
            TargetPointer actualMethodDesc = em.GetMethodDesc(handle.Value);
            Assert.Equal(expectedMethodDescAddress, actualMethodDesc);
        }
        {
            // Past function start
            var handle = em.GetCodeBlockHandle(codeRangeStart + expectedRuntimeFunction * 2);
            Assert.NotNull(handle);
            TargetPointer actualMethodDesc = em.GetMethodDesc(handle.Value);
            Assert.Equal(expectedMethodDescAddress, actualMethodDesc);
        }
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetMethodDesc_R2R_MultipleRuntimeFunctions(int version, MockTarget.Architecture arch)
    {
        const ulong codeRangeStart = 0x0a0a_0000u; // arbitrary
        const uint codeRangeSize = 0xc000u; // arbitrary
        TargetPointer jitManagerAddress = new(0x000b_ff00); // arbitrary

        TargetPointer[] methodDescAddresses = [ 0x0101_aaa0, 0x0201_aaa0];

        MockDescriptors.ExecutionManager emBuilder = new(version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var jittedCode = emBuilder.AllocateJittedCodeRange(codeRangeStart, codeRangeSize);

        uint[] runtimeFunctions = [ 0x100, 0xc00 ];

        TargetPointer r2rInfo = emBuilder.AddReadyToRunInfo(runtimeFunctions, []);
        MockDescriptors.HashMap hashMapBuilder = new(emBuilder.Builder);
        hashMapBuilder.PopulatePtrMap(
            r2rInfo + (uint)emBuilder.Types[DataType.ReadyToRunInfo].Fields[nameof(Data.ReadyToRunInfo.EntryPointToMethodDescMap)].Offset,
            [
                (jittedCode.RangeStart + runtimeFunctions[0], methodDescAddresses[0]),
                (jittedCode.RangeStart + runtimeFunctions[1], methodDescAddresses[1]),
            ]);

        TargetPointer r2rModule = emBuilder.AddReadyToRunModule(r2rInfo);
        TargetPointer rangeSectionAddress = emBuilder.AddReadyToRunRangeSection(jittedCode, jitManagerAddress, r2rModule);
        _ = emBuilder.AddRangeSectionFragment(jittedCode, rangeSectionAddress);

        Target target = CreateTarget(emBuilder);

        IExecutionManager em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);

        {
            // Match first function
            var handle = em.GetCodeBlockHandle(codeRangeStart + runtimeFunctions[0]);
            Assert.NotNull(handle);
            TargetPointer actualMethodDesc = em.GetMethodDesc(handle.Value);
            Assert.Equal(methodDescAddresses[0], actualMethodDesc);
        }
        {
            // After first function, before second - match first function
            uint betweenFirstAndSecond = runtimeFunctions[0] + (runtimeFunctions[1] - runtimeFunctions[0]) / 2;
            var handle = em.GetCodeBlockHandle(codeRangeStart + betweenFirstAndSecond);
            Assert.NotNull(handle);
            TargetPointer actualMethodDesc = em.GetMethodDesc(handle.Value);
            Assert.Equal(methodDescAddresses[0], actualMethodDesc);
        }
        {
            // Match second function
            var handle = em.GetCodeBlockHandle(codeRangeStart + runtimeFunctions[1]);
            Assert.NotNull(handle);
            TargetPointer actualMethodDesc = em.GetMethodDesc(handle.Value);
            Assert.Equal(methodDescAddresses[1], actualMethodDesc);
        }
        {
            // After second/last function - match second/last function
            var handle = em.GetCodeBlockHandle(codeRangeStart + runtimeFunctions[1] * 2);
            Assert.NotNull(handle);
            TargetPointer actualMethodDesc = em.GetMethodDesc(handle.Value);
            Assert.Equal(methodDescAddresses[1], actualMethodDesc);
        }
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetMethodDesc_R2R_HotColdBlock(int version, MockTarget.Architecture arch)
    {
        const ulong codeRangeStart = 0x0a0a_0000u; // arbitrary
        const uint codeRangeSize = 0xc000u; // arbitrary
        TargetPointer jitManagerAddress = new(0x000b_ff00); // arbitrary

        TargetPointer[] methodDescAddresses = [0x0101_aaa0, 0x0201_aaa0];

        MockDescriptors.ExecutionManager emBuilder = new(version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var jittedCode = emBuilder.AllocateJittedCodeRange(codeRangeStart, codeRangeSize);

        uint[] runtimeFunctions = [0x100, 0x200, 0x300, 0x400, 0x500];
        uint[] hotColdMap = [3, 0, 4, 1];

        TargetPointer r2rInfo = emBuilder.AddReadyToRunInfo(runtimeFunctions, hotColdMap);
        MockDescriptors.HashMap hashMapBuilder = new(emBuilder.Builder);
        hashMapBuilder.PopulatePtrMap(
            r2rInfo + (uint)emBuilder.Types[DataType.ReadyToRunInfo].Fields[nameof(Data.ReadyToRunInfo.EntryPointToMethodDescMap)].Offset,
            [
                (jittedCode.RangeStart + runtimeFunctions[hotColdMap[1]], methodDescAddresses[0]),
                (jittedCode.RangeStart + runtimeFunctions[hotColdMap[3]], methodDescAddresses[1]),
            ]);

        TargetPointer r2rModule = emBuilder.AddReadyToRunModule(r2rInfo);
        TargetPointer rangeSectionAddress = emBuilder.AddReadyToRunRangeSection(jittedCode, jitManagerAddress, r2rModule);
        _ = emBuilder.AddRangeSectionFragment(jittedCode, rangeSectionAddress);

        Target target = CreateTarget(emBuilder);

        IExecutionManager em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);

        // Hot and cold parts should map to the same method desc
        for (int i = 0; i < hotColdMap.Length; i++)
        {
            // Function start
            var handle = em.GetCodeBlockHandle(codeRangeStart + runtimeFunctions[hotColdMap[i]]);
            Assert.NotNull(handle);
            TargetPointer actualMethodDesc = em.GetMethodDesc(handle.Value);
            Assert.Equal(methodDescAddresses[i / 2], actualMethodDesc);

            // Past function start
            handle = em.GetCodeBlockHandle(codeRangeStart + runtimeFunctions[hotColdMap[i]] + 8);
            Assert.NotNull(handle);
            actualMethodDesc = em.GetMethodDesc(handle.Value);
            Assert.Equal(methodDescAddresses[i / 2], actualMethodDesc);
        }
    }

    [Theory]
    [MemberData(nameof(StdArchAllVersions))]
    public void GetUnwindInfoBaseAddress_R2R_ManyRuntimeFunction(int version, MockTarget.Architecture arch)
    {
        const ulong codeRangeStart = 0x0a0a_0000u; // arbitrary
        const uint codeRangeSize = 0xc000u; // arbitrary
        TargetPointer jitManagerAddress = new(0x000b_ff00); // arbitrary

        MockDescriptors.ExecutionManager emBuilder = new(version, arch, MockDescriptors.ExecutionManager.DefaultAllocationRange);
        var jittedCode = emBuilder.AllocateJittedCodeRange(codeRangeStart, codeRangeSize);

        uint runtimeFunction = 0x100;

        TargetPointer r2rInfo = emBuilder.AddReadyToRunInfo([runtimeFunction], []);
        MockDescriptors.HashMap hashMapBuilder = new(emBuilder.Builder);
        hashMapBuilder.PopulatePtrMap(
            r2rInfo + (uint)emBuilder.Types[DataType.ReadyToRunInfo].Fields[nameof(Data.ReadyToRunInfo.EntryPointToMethodDescMap)].Offset,
            [(jittedCode.RangeStart + runtimeFunction, new TargetPointer(0x0101_aaa0))]);

        TargetPointer r2rModule = emBuilder.AddReadyToRunModule(r2rInfo);
        TargetPointer rangeSectionAddress = emBuilder.AddReadyToRunRangeSection(jittedCode, jitManagerAddress, r2rModule);
        _ = emBuilder.AddRangeSectionFragment(jittedCode, rangeSectionAddress);

        Target target = CreateTarget(emBuilder);

        IExecutionManager em = target.Contracts.ExecutionManager;
        Assert.NotNull(em);

        var handle = em.GetCodeBlockHandle(codeRangeStart + runtimeFunction);
        Assert.NotNull(handle);
        TargetPointer actualBaseAddress = em.GetUnwindInfoBaseAddress(handle.Value);
        Assert.Equal(new TargetPointer(codeRangeStart), actualBaseAddress);
    }

    public static IEnumerable<object[]> StdArchAllVersions()
    {
        const int highestVersion = 2;
        foreach(object[] arr in new MockTarget.StdArch())
        {
            MockTarget.Architecture arch = (MockTarget.Architecture)arr[0];
            for(int version = 1; version <= highestVersion; version++){
                yield return new object[] { version, arch };
            }
        }
    }

    public static IEnumerable<object[]> Arm64AllVersions()
    {
        foreach (object[] values in StdArchAllVersions())
        {
            MockTarget.Architecture arch = (MockTarget.Architecture)values[1];
            if (arch.Is64Bit && arch.IsLittleEndian)
                yield return values;
        }
    }
}
