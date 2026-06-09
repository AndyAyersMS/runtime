// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

namespace ILCompiler.ObjectWriter
{
    /// <summary>
    /// Indices of the Wasm globals imported from the <c>webcil</c> host module
    /// into every generated R2R Wasm module.
    /// </summary>
    /// <remarks>
    /// These indices MUST be kept in sync with:
    ///   - <c>WasmObjectWriter._defaultGlobalImports</c> (where the imports are emitted in this order),
    ///   - the JIT-side mirror constants in <c>src/coreclr/jit/targetwasm.h</c>,
    ///   - the host loader that supplies these imports
    ///     (see <c>src/coreclr/hosts/corerun/wasm/libCorerun.js</c>).
    /// </remarks>
    public static class WasmGlobalImports
    {
        /// <summary>Mutable i32, linear-memory stack pointer.</summary>
        public const int StackPointerGlobalIndex = 0;

        /// <summary>Const i32, start of the R2R image in linear memory.</summary>
        public const int ImageBaseGlobalIndex = 1;

        /// <summary>Const i32, start of this module's slice in the shared function table.</summary>
        public const int TableBaseGlobalIndex = 2;

        /// <summary>
        /// Mutable i32, runtime-async continuation return slot. The callee writes the
        /// continuation object reference here on the suspend path (null on the
        /// normal-return path); the caller reads it immediately after the call to
        /// decide whether to suspend or continue. Wasm analogue of the
        /// <c>REG_ASYNC_CONTINUATION_RET</c> fixed return register on other targets.
        ///
        /// The declared type (i32) matches the current wasm32-only pointer width.
        /// If wasm64 is enabled in the future, this global's type must be promoted
        /// to i64 (same as the other pointer-sized imports, e.g.
        /// <see cref="StackPointerGlobalIndex"/>); the JIT already emits the
        /// matching constant via the pointer-sized <c>INS_I_const</c> typedef.
        /// </summary>
        public const int AsyncContinuationGlobalIndex = 3;
    }
}
