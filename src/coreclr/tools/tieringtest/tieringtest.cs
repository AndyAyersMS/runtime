// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.
//

using System;
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
        int warmup = 50;
        int final = 50;

        for (int i = 0; i < warmup; i++)
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
                Console.WriteLine($"Failed at warmup iteration {i}: {result}");
                break;
            }
            Thread.Sleep(15);
        }

        for (int i = 0; i < final; i++)
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
                Console.WriteLine($"Failed at final iteration {i}: {result}");
                break;
            }
        }

        if (result == 100)
        {
            Console.WriteLine($"Ran {warmup + final} iterations sucessfully");
        }

        return result;
    }
}

