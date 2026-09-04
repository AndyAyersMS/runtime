// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Runtime.CompilerServices;
using Xunit;

public class HotColdWriteXorExecute
{
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static double GetValue(int value)
    {
        if (value == 0)
        {
            return 1.25;
        }

        if (value == 2)
        {
            return -3.5;
        }

        if (value == 5)
        {
            return 7.75;
        }

        if (value == 9)
        {
            return 11.125;
        }

        if (value == 14)
        {
            return -17.625;
        }

        if (value == 20)
        {
            return 23.875;
        }

        return -1.0;
    }

    [Fact]
    public static void TestEntryPoint()
    {
        Assert.Equal(1.25, GetValue(0));
        Assert.Equal(-3.5, GetValue(2));
        Assert.Equal(7.75, GetValue(5));
        Assert.Equal(11.125, GetValue(9));
        Assert.Equal(-17.625, GetValue(14));
        Assert.Equal(23.875, GetValue(20));
        Assert.Equal(-1.0, GetValue(-1));
        Assert.Equal(-1.0, GetValue(21));
    }
}
