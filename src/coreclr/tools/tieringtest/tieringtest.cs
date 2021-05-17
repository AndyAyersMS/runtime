// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.
//

using System;
using System.Diagnostics;
using System.IO;
using System.Reflection;
using System.Runtime.Loader;
using System.Threading;

class Program
{
    // Repeatedly execute a test case's Main method so that methods jitted
    // by the test can get rejitted at Tier1.
    //
    static int Main(string[] args)
    {
        AssemblyLoadContext alc = AssemblyLoadContext.Default;
        Assembly testAssembly = alc.LoadFromAssemblyPath(args[0]);
        MethodInfo main = testAssembly.EntryPoint;

        if (main == null)
        {
            Console.WriteLine($"Can't find entry point in {Path.GetFileName(args[0])}");
            return -1;
        }

        string[] mainArgs = new string[args.Length - 1];
        Array.Copy(args, 1, mainArgs, 0, mainArgs.Length);

        Console.WriteLine($"Found entry point {main.Name} in {Path.GetFileName(args[0])}");

        // See if main wants any args.
        //
        var mainParams = main.GetParameters();

        int result = 0;

        // Repeatedly invoke main to get things to pass through Tier0 and rejit at Tier1
        //
        int warmup = 40;
        int final = 5;
        int total = warmup + final;
        int i = 0;
        Stopwatch s = new Stopwatch();
        s.Start();

        // We might decide to give up on this test, for reasons.
        //
        // If the test fails at iteration 0, assume it's incompatible with the way we're running it
        // and don't report as a failure.
        //
        // If the test fails at iteration 1, assume it's got some bit of state that carries over
        // from one call to main to the next, and so don't report it as failure.
        //
        // If the test takes too long, just give up on iterating it.
        //
        bool giveUp = false;

        try {

            for (; i < warmup  && !giveUp; i++)
            {
                if (mainParams.Length == 0)
                {
                    result = (int)main.Invoke(null, new object[] { });
                }
                else
                {
                    result = (int)main.Invoke(null, new object[] { mainArgs });
                }
                
                if (result != 100)
                {
                    if (i < 2)
                    {
                        Console.WriteLine($"[tieringtest] test failed at iteration {i} with result {result}. Test is likely incompatible.");
                        result = 100;
                    }
                    else
                    {
                        Console.WriteLine($"[tieringtest] test failed at iteration {i}: {result}");
                    }
                    giveUp = true;
                    break;
                }

                // Don't iterate if test is running long.
                //
                if (s.ElapsedMilliseconds > 10_000)
                {
                    Console.WriteLine($"[tieringtest] test running long ({s.ElapsedMilliseconds / (i + 1)} ms/iteration). Giving up at iteration {i}");
                    giveUp = true;
                    break;
                }

                Thread.Sleep(15);
            }

            for (; i < total && !giveUp; i++)
            {
                if (mainParams.Length == 0)
                {
                    result = (int)main.Invoke(null, new object[] { });
                }
                else
                {
                    result = (int)main.Invoke(null, new object[] { mainArgs });
                }
                
                if (result != 100)
                {
                    Console.WriteLine($"[tieringtest] failed at iteration {i}: {result}");
                    giveUp = true;
                    break;
                }
                
                // Don't iterate if test is running long.
                //
                if (s.ElapsedMilliseconds > 10_000)
                {
                    Console.WriteLine($"[tieringtest] test running long ({s.ElapsedMilliseconds / (i + 1)} ms/iteration). Giving up at iteration {i}");
                    giveUp = true;
                    break;
                }
            }
            
            if (result == 100)
            {
                Console.WriteLine($"[tieringtest] ran {total} test iterations sucessfully");
            }
        }
        catch(Exception e)
        {
            if (i < 2)
            {
                Console.WriteLine($"[tieringtest] test failed at iteration {i} with exception {e.Message}. Test is likely incompatible.");
                result = 100;
            }
            else
            {
                Console.WriteLine($"[tieringtest] test failed at iteration {i} with exception {e.Message}");
                result = -1;
            }
        }
            
        return result;
    }
}

