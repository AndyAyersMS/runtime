
// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

//////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
//
// #JITEEVersionIdentifier
//
// This GUID represents the version of the JIT/EE interface. Any time the interface between the JIT and
// the EE changes (by adding or removing methods to any interface shared between them), this GUID should
// be changed. This is the identifier verified by ICorJitCompiler::getVersionIdentifier().
//
// You can use "uuidgen.exe -s" to generate this value.
//
// See docs/project/updating-jitinterface.md for details
//
// **** NOTE TO INTEGRATORS:
//
// If there is a merge conflict here, because the version changed in two different places, you must
// create a **NEW** GUID, not simply choose one or the other!
//
// NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE NOTE
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////

constexpr GUID JITEEVersionIdentifier = { /* 130a1a60-49e1-4595-b6c2-7f0317be4168 */
    0x130a1a60,
    0x49e1,
    0x4595,
    {0xb6, 0xc2, 0x7f, 0x03, 0x17, 0xbe, 0x41, 0x68}
};

//////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// END JITEEVersionIdentifier
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////
