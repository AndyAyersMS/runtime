// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

// Two cast helper call sites with distinct IL offsets carry distinct dynamic
// class profiles. Head/tail merge must not collapse them, or GDV expansion
// will lose one site's profile and fall off the fast path.

namespace Runtime_128659;

using System;
using System.Runtime.CompilerServices;
using Xunit;

public class Foo { public virtual int Tag => 0; }
public class Bar : Foo { public override int Tag => 1; }
public class Baz : Foo { public override int Tag => 2; }

public class Runtime_128659
{
    [MethodImpl(MethodImplOptions.NoInlining | MethodImplOptions.AggressiveOptimization)]
    public static Foo Dispatch(int tag, object o)
    {
        // The side effect prevents Roslyn from deduping the two casts at IL level,
        // so the JIT sees two distinct castclass IL offsets.
        if (tag == 0) { GC.KeepAlive(o); return (Foo)o; }
        return (Foo)o;
    }

    [Fact]
    public static int TestEntryPoint()
    {
        var bar = new Bar();
        var baz = new Baz();

        long sum = 0;
        for (int i = 0; i < 200; i++)
        {
            sum += Dispatch(0, bar).Tag;
            sum += Dispatch(1, baz).Tag;
        }

        return sum == 200 * (1 + 2) ? 100 : -1;
    }
}
