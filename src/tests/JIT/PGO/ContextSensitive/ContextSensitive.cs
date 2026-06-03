// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Xunit;

// Smoke test for caller-sensitive (context-sensitive) class histograms in
// shared generic methods (DOTNET_TieredPGO_ContextSensitive=1).
//
// Exercises a shared generic method M<T> with an internal virtual call
// where two distinct callers (CallerA, CallerB) drive the method with two
// different receiver types. With the knob enabled, the JIT should observe
// caller-tagged class histograms and, when re-jitting at higher tier, be
// able to specialize by caller. We only assert that the program runs to
// completion without runtime asserts or crashes (the JIT/runtime behavior
// is exercised; behavioral assertions would require disasm inspection).
public class Program
{
    interface IThing
    {
        int Value();
    }

    sealed class ThingA : IThing { public int Value() => 1; }
    sealed class ThingB : IThing { public int Value() => 2; }

    // Shared generic method: code body is shared across instantiations.
    [MethodImpl(MethodImplOptions.NoInlining)]
    static int M<T>(IThing t)
    {
        int sum = 0;
        for (int i = 0; i < 4; i++)
            sum += t.Value();
        return sum;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    static int CallerA()
    {
        int total = 0;
        IThing a = new ThingA();
        for (int i = 0; i < 1000; i++)
            total += M<object>(a);
        return total;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    static int CallerB()
    {
        int total = 0;
        IThing b = new ThingB();
        for (int i = 0; i < 1000; i++)
            total += M<object>(b);
        return total;
    }

    [Fact]
    public static void TestEntryPoint()
    {
        int expectedA = 1 * 4 * 1000;
        int expectedB = 2 * 4 * 1000;

        // Drive several rounds so tiered compilation has time to promote.
        for (int iter = 0; iter < 200; iter++)
        {
            Assert.Equal(expectedA, CallerA());
            Assert.Equal(expectedB, CallerB());
            if ((iter & 0xF) == 0)
                Thread.Sleep(20);
        }
    }
}
