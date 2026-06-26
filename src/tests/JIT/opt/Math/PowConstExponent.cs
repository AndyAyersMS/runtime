// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Runtime.CompilerServices;
using Xunit;

// Math.Pow(x, c) / MathF.Pow(x, c) with a small constant exponent is expanded inline instead of
// calling the runtime pow helper:
//    Pow(x, 1) == x
//    Pow(x, 2) == x * x   (a single rounding, exact for all IEEE inputs)

namespace CodeGenTests
{
    public static class PowConstExponent
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        static double Pow2_Double(double x)
        {
            // ARM64-FULL-LINE: fmul {{d[0-9]+}}, {{d[0-9]+}}, {{d[0-9]+}}
            // X64-FULL-LINE: {{(v)?mulsd}} {{xmm[0-9]+}},{{.*}}
            return Math.Pow(x, 2.0);
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        static float Pow2_Float(float x)
        {
            // ARM64-FULL-LINE: fmul {{s[0-9]+}}, {{s[0-9]+}}, {{s[0-9]+}}
            // X64-FULL-LINE: {{(v)?mulss}} {{xmm[0-9]+}},{{.*}}
            return MathF.Pow(x, 2.0f);
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        static double Pow1_Double(double x)
        {
            // Pow(x, 1) folds to x, so there must be no call to the pow helper.
            // ARM64-NOT: bl
            // X64-NOT: call
            return Math.Pow(x, 1.0);
        }

        // A non-foldable exponent must still call the pow helper.
        [MethodImpl(MethodImplOptions.NoInlining)]
        static double Pow3_Double(double x)
        {
            return Math.Pow(x, 3.0);
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        static double Pow_Variable(double x, double n)
        {
            return Math.Pow(x, n);
        }

        static int s_sideEffectCount;

        [MethodImpl(MethodImplOptions.NoInlining)]
        static double GetBase()
        {
            s_sideEffectCount++;
            return 3.0;
        }

        // The base must be evaluated exactly once when folding Pow(x, 2).
        [MethodImpl(MethodImplOptions.NoInlining)]
        static double Pow2_SideEffect()
        {
            return Math.Pow(GetBase(), 2.0);
        }

        static bool Same(double a, double b) => (a == b) || (double.IsNaN(a) && double.IsNaN(b));

        [Fact]
        public static int TestEntryPoint()
        {
            int result = 100;

            double[] values =
            {
                3.0, -2.0, 0.0, -0.0, 1.5, -1.5, 1e154, double.NaN,
                double.PositiveInfinity, double.NegativeInfinity
            };

            foreach (double v in values)
            {
                if (!Same(Pow2_Double(v), Math.Pow(v, 2.0)))
                {
                    result = -1;
                }
                if (!Same(Pow1_Double(v), Math.Pow(v, 1.0)))
                {
                    result = -1;
                }
                if (!Same(Pow3_Double(v), Math.Pow(v, 3.0)))
                {
                    result = -1;
                }
                if (!Same(Pow_Variable(v, 2.0), Math.Pow(v, 2.0)))
                {
                    result = -1;
                }
                if (!Same((double)Pow2_Float((float)v), (double)MathF.Pow((float)v, 2.0f)))
                {
                    result = -1;
                }
            }

            // The folded base expression must run exactly once.
            s_sideEffectCount = 0;
            if ((Pow2_SideEffect() != 9.0) || (s_sideEffectCount != 1))
            {
                result = -1;
            }

            return result;
        }
    }
}
