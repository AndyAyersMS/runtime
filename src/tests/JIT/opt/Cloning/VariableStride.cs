// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Runtime.CompilerServices;
using Xunit;

public class VariableStride
{
    [MethodImpl(MethodImplOptions.NoInlining | MethodImplOptions.AggressiveOptimization)]
    static int SumIncLtArrLen(int[] a, int stride)
    {
        int sum = 0;
        for (int i = 0; i < a.Length; i += stride)
        {
            sum += a[i];
        }
        return sum;
    }

    [MethodImpl(MethodImplOptions.NoInlining | MethodImplOptions.AggressiveOptimization)]
    static int SumIncLeVar(int[] a, int last, int stride)
    {
        int sum = 0;
        for (int i = 0; i <= last; i += stride)
        {
            sum += a[i];
        }
        return sum;
    }

    [MethodImpl(MethodImplOptions.NoInlining | MethodImplOptions.AggressiveOptimization)]
    static int SumIncLtConstLimit(int[] a, int stride)
    {
        int sum = 0;
        for (int i = 0; i < 50; i += stride)
        {
            sum += a[i];
        }
        return sum;
    }

    static int[] MakeArray(int n)
    {
        var a = new int[n];
        for (int i = 0; i < n; i++)
        {
            a[i] = i + 1;
        }
        return a;
    }

    static int ExpectedIncLt(int limit, int stride)
    {
        int sum = 0;
        for (int i = 0; i < limit; i += stride)
        {
            sum += i + 1;
        }
        return sum;
    }

    static int ExpectedIncLe(int last, int stride)
    {
        int sum = 0;
        for (int i = 0; i <= last; i += stride)
        {
            sum += i + 1;
        }
        return sum;
    }

    // Strides 1..57 are inside the runtime cap (fast clone takes the
    // bounds-check-removed path); 58 and above must fall back to the slow
    // clone. Stride must be positive at runtime — the sign guard ensures
    // the fast clone is only entered then.
    [Theory]
    [InlineData(1, 100)]
    [InlineData(2, 100)]
    [InlineData(7, 100)]
    [InlineData(50, 100)]
    [InlineData(57, 100)]
    [InlineData(58, 100)]
    [InlineData(99, 100)]
    [InlineData(200, 100)]
    public static void IncLtArrLen(int stride, int len)
    {
        int[] a = MakeArray(len);
        int got = SumIncLtArrLen(a, stride);
        int want = ExpectedIncLt(len, stride);
        Assert.Equal(want, got);
    }

    [Theory]
    [InlineData(99, 1)]
    [InlineData(99, 3)]
    [InlineData(50, 7)]
    [InlineData(99, 57)]
    [InlineData(99, 58)]
    [InlineData(0, 5)]
    public static void IncLeVar(int last, int stride)
    {
        int[] a = MakeArray(last + 1);
        int got = SumIncLeVar(a, last, stride);
        int want = ExpectedIncLe(last, stride);
        Assert.Equal(want, got);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(5)]
    [InlineData(50)]
    [InlineData(57)]
    [InlineData(58)]
    [InlineData(100)]
    public static void IncLtConstLimit(int stride)
    {
        int[] a = MakeArray(60);
        int got = SumIncLtConstLimit(a, stride);
        int want = ExpectedIncLt(50, stride);
        Assert.Equal(want, got);
    }
}
