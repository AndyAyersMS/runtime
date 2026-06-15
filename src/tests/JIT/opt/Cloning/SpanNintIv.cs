// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

// Cover loop cloning of `for (nint i = 0; i < span.Length; i++) span[(int)i]`.
//
// The Span<T>.get_Item intrinsic spills the index into a temp before the bounds
// check, so the visitor's "indLcl == iterVar" check has to walk through that
// temp's defining copy to recover the original iter var. Companion to the
// long-IV loop cloning support: tests both that the JIT recognizes the loop
// and that the slow path remains correct for out-of-bounds inputs.

using System;
using System.Runtime.CompilerServices;
using Xunit;

public class SpanNintIv
{
    [MethodImpl(MethodImplOptions.NoInlining | MethodImplOptions.AggressiveOptimization)]
    static int SumNintSpan(Span<int> s)
    {
        int sum = 0;
        for (nint i = 0; i < s.Length; i++)
        {
            sum += s[(int)i];
        }
        return sum;
    }

    [MethodImpl(MethodImplOptions.NoInlining | MethodImplOptions.AggressiveOptimization)]
    static int SumNintROSpan(ReadOnlySpan<int> s)
    {
        int sum = 0;
        for (nint i = 0; i < s.Length; i++)
        {
            sum += s[(int)i];
        }
        return sum;
    }

    [MethodImpl(MethodImplOptions.NoInlining | MethodImplOptions.AggressiveOptimization)]
    static int SumNintSpanUserLimit(Span<int> s, nint limit)
    {
        int sum = 0;
        for (nint i = 0; i < limit; i++)
        {
            sum += s[(int)i];
        }
        return sum;
    }

    static Span<int> MakeSpan(int n)
    {
        var a = new int[n];
        for (int i = 0; i < n; i++)
        {
            a[i] = i + 1;
        }
        return a;
    }

    static int ExpectedSum(int n)
    {
        int sum = 0;
        for (int i = 0; i < n; i++)
        {
            sum += i + 1;
        }
        return sum;
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(10)]
    [InlineData(100)]
    public static void NintSpan(int n)
    {
        int got  = SumNintSpan(MakeSpan(n));
        int want = ExpectedSum(n);
        Assert.Equal(want, got);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(10)]
    [InlineData(100)]
    public static void NintROSpan(int n)
    {
        int got  = SumNintROSpan((ReadOnlySpan<int>)MakeSpan(n));
        int want = ExpectedSum(n);
        Assert.Equal(want, got);
    }

    [Theory]
    [InlineData(10, 10)]
    [InlineData(10, 5)]
    [InlineData(10, 0)]
    public static void NintSpanUserLimit_InBounds(int n, nint limit)
    {
        int got  = SumNintSpanUserLimit(MakeSpan(n), limit);
        int want = ExpectedSum((int)limit);
        Assert.Equal(want, got);
    }

    [Theory]
    [InlineData(10, 11)]
    [InlineData(10, 100)]
    public static void NintSpanUserLimit_OutOfBounds_Throws(int n, nint limit)
    {
        Assert.Throws<IndexOutOfRangeException>(() => SumNintSpanUserLimit(MakeSpan(n), limit));
    }
}
