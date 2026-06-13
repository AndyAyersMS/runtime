// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

namespace Bzhi_recognition;

using System;
using System.Runtime.CompilerServices;
using Xunit;

// Validates that recognizing `value & ((1 << k) - 1)` as BMI2 BZHI preserves
// CIL shift semantics for every relevant `k`, including values >= the operand
// size where the shift would wrap to 0 and BZHI would return the source
// unchanged. The lowering must mask `k` (or prove it's in range) so the two
// formulations remain equivalent.

public class Bzhi_recognition
{
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static uint Mask32(uint v, int k) => v & ((1u << k) - 1);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static ulong Mask64(ulong v, int k) => v & ((1ul << k) - 1);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static uint Mask32_Premasked(uint v, int k) => v & ((1u << (k & 31)) - 1);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static int Mask32_Signed(int v, int k) => v & ((1 << k) - 1);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static ulong Mask64_LongCount(ulong v, long k) => v & ((1ul << (int)k) - 1);

    private static uint Reference32(uint v, int k) => v & ((1u << k) - 1);
    private static ulong Reference64(ulong v, int k) => v & ((1ul << k) - 1);

    [Fact]
    public static int TestEntryPoint()
    {
        bool ok = true;

        uint[]  values32 = { 0u, ~0u, 0xAA55AA55u, 0x80000000u, 1u };
        ulong[] values64 = { 0UL, ~0UL, 0xAA55AA55AA55AA55UL, 0x8000000000000000UL, 1UL };

        // Sweep around and past the operand-size boundary for 32-bit.
        for (int k = -4; k <= 36; k++)
        {
            foreach (uint v in values32)
            {
                uint reference = Reference32(v, k);
                if (Mask32(v, k) != reference)           { ok = false; }
                if (Mask32_Premasked(v, k) != reference) { ok = false; }
                if ((uint)Mask32_Signed((int)v, k) != reference) { ok = false; }
            }
        }

        // Sweep around and past the operand-size boundary for 64-bit.
        for (int k = -4; k <= 68; k++)
        {
            foreach (ulong v in values64)
            {
                ulong reference = Reference64(v, k);
                if (Mask64(v, k) != reference)                 { ok = false; }
                if (Mask64_LongCount(v, (long)k) != reference) { ok = false; }
            }
        }

        return ok ? 100 : 1;
    }
}
