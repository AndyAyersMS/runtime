// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

//
// Wasm runtime-async continuation slot accessors.
//
// On targets other than wasm the runtime-async continuation is communicated
// across a call via a fixed register (REG_ASYNC_CONTINUATION_RET). Wasm has
// no fixed register file, so the equivalent slot is a single mutable i32
// WebAssembly.Global shared across the runtime and every R2R webcil module
// (see src/coreclr/tools/Common/Compiler/ObjectWriter/WasmGlobalImports.cs
// for the import-side definition, and src/coreclr/hosts/corerun/wasm/
// libCorerun.js for the host-side allocation).
//
// R2R wasm codegen writes the slot directly with `global.set 3` on the
// suspend path (and `i32.const 0; global.set 3` on the normal-return path),
// and reads it with `global.get 3` immediately after every async call. C++
// runtime code that bridges between the interpreter and R2R (for example
// prestub.cpp ExecuteInterpretedMethod after an InterpExecMethod return, or
// the call-stub generator's HasAsyncContinuation path) cannot use those
// instructions directly because the runtime itself is built into a separate
// wasm module that does not import the webcil global. It uses the JS-side
// accessors declared below instead; both call paths ultimately read/write
// the same shared WebAssembly.Global instance.
//
// Wasm MVP is single-threaded so no synchronization is required. When wasm
// multi-threading is enabled, the slot will need per-thread storage and
// these accessors will need to widen to a thread-id parameter (matching the
// per-thread register save area on other targets).
//

#ifndef _WASM_ASYNC_CONTINUATION_H
#define _WASM_ASYNC_CONTINUATION_H

#ifdef TARGET_WASM

// Load the current value of the shared `asyncContinuation` WebAssembly.Global.
// Supplied by the wasm host (libCorerun.js for the corerun host).
extern "C" int32_t RuntimeAsync_LoadAsyncContinuation();

// Store a new value into the shared `asyncContinuation` WebAssembly.Global.
// Supplied by the wasm host (libCorerun.js for the corerun host).
extern "C" void RuntimeAsync_StoreAsyncContinuation(int32_t value);

#endif // TARGET_WASM

#endif // _WASM_ASYNC_CONTINUATION_H
