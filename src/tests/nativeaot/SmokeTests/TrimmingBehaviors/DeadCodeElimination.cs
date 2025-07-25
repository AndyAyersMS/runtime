// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Diagnostics.CodeAnalysis;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

class DeadCodeElimination
{
    public static int Run()
    {
        SanityTest.Run();
        Test110932Regression.Run();
        TestInstanceMethodOptimization.Run();
        TestReflectionInvokeSignatures.Run();
        TestAbstractTypeNeverDerivedVirtualsOptimization.Run();
        TestAbstractNeverDerivedWithDevirtualizedCall.Run();
        TestAbstractDerivedByUnrelatedTypeWithDevirtualizedCall.Run();
        TestUnusedDefaultInterfaceMethod.Run();
        TestInlinedDeadBranchElimination.Run();
        TestComplexInlinedDeadBranchElimination.Run();
        TestArrayElementTypeOperations.Run();
        TestStaticVirtualMethodOptimizations.Run();
        TestTypeIs.Run();
        TestTypeEquals.Run();
        TestTypeEqualityDeadBranchScanRemoval.Run();
        TestTypeIsEnum.Run();
        TestTypeIsValueType.Run();
        TestBranchesInGenericCodeRemoval.Run();
        TestUnmodifiableStaticFieldOptimization.Run();
        TestUnmodifiableInstanceFieldOptimization.Run();
        TestGetMethodOptimization.Run();
        TestTypeOfCodegenBranchElimination.Run();
        TestInvisibleGenericsTrimming.Run();
        TestTypeHandlesInGenericDictionaries.Run();

        return 100;
    }

    class SanityTest
    {
        class PresentType { }

        class NotPresentType { }

        public static void Run()
        {
            typeof(PresentType).ToString();

            if (GetTypeSecretly(typeof(SanityTest), nameof(PresentType)) == null)
                throw new Exception();

            ThrowIfPresent(typeof(SanityTest), nameof(NotPresentType));
        }
    }

    class Test110932Regression
    {
        static bool s_trueConst = true;
        static bool s_falseConst = false;

        interface I
        {
            static virtual bool GetValue() => false;
        }

        class C : I
        {
            static bool I.GetValue() => true;
        }

        public static void Run()
        {
            if (!Call<C>())
                throw new Exception();
        }
        static bool Call<T>() where T : I
        {
            if (T.GetValue())
                return s_trueConst;
            return s_falseConst;
        }
    }

    class TestInstanceMethodOptimization
    {
        class UnreferencedType { }

        class NeverAllocatedType
        {
            public Type DoSomething() => typeof(UnreferencedType);
        }

#if !DEBUG
        static object s_instance = new object[10];
#endif

        public static void Run()
        {
            Console.WriteLine("Testing instance methods on unallocated types");

#if DEBUG
            NeverAllocatedType instance = null;
            if (instance != null)
                instance.DoSomething();
#else
            // In release builds additionally test that the "is" check didn't introduce the constructed type
            if (s_instance is NeverAllocatedType never)
                never.DoSomething();
#endif

            ThrowIfPresent(typeof(TestInstanceMethodOptimization), nameof(UnreferencedType));
        }
    }

    class TestReflectionInvokeSignatures
    {
        public class Never1 { }

        public static void Invoke1(Never1 inst) { }

        public struct Allocated1 { }

        public static void Invoke2(out Allocated1 inst) { inst = default; }

        public static void Run()
        {
            {
                MethodInfo mi = typeof(TestReflectionInvokeSignatures).GetMethod(nameof(Invoke1));
                mi.Invoke(null, new object[1]);
                ThrowIfPresentWithUsableMethodTable(typeof(TestReflectionInvokeSignatures), nameof(Never1));
            }

            {
                MethodInfo mi = typeof(TestReflectionInvokeSignatures).GetMethod(nameof(Invoke2));
                var args = new object[1];
                mi.Invoke(null, args);
                ThrowIfNotPresent(typeof(TestReflectionInvokeSignatures), nameof(Allocated1));
                if (args[0].GetType().Name != nameof(Allocated1))
                    throw new Exception();
                if (!args[0].ToString().Contains(nameof(Allocated1)))
                    throw new Exception();
            }
        }
    }

    class TestAbstractTypeNeverDerivedVirtualsOptimization
    {
        class UnreferencedType1
        {
        }

        class TheBase
        {
            public virtual object Something() => new object();
        }

        abstract class AbstractDerived : TheBase
        {
            // We expect "Something" to be generated as a throwing helper.
            [MethodImpl(MethodImplOptions.NoInlining)]
            public sealed override object Something() => new UnreferencedType1();
            // We expect "callvirt Something" to get devirtualized here.
            [MethodImpl(MethodImplOptions.NoInlining)]
            public object TrySomething() => Something();
        }

        abstract class AbstractDerivedAgain : AbstractDerived
        {
        }

        static TheBase s_b = new TheBase();
        static AbstractDerived s_d = null;

        public static void Run()
        {
            Console.WriteLine("Testing virtual methods on never derived abstract types");

            // Make sure Something is seen virtually used.
            s_b.Something();

            // Force a constructed MethodTable for AbstractDerived and AbstractDerivedAgain into closure
            typeof(AbstractDerivedAgain).ToString();

            if (s_d != null)
            {
                s_d.TrySomething();
            }

            ThrowIfPresent(typeof(TestAbstractTypeNeverDerivedVirtualsOptimization), nameof(UnreferencedType1));
        }
    }

    class TestAbstractNeverDerivedWithDevirtualizedCall
    {
        static void DoIt(Derived d) => d?.DoSomething();

        abstract class Base
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            public virtual void DoSomething() => new UnreferencedType1().ToString();
        }

        sealed class Derived : Base { }

        class UnreferencedType1 { }

        public static void Run()
        {
            Console.WriteLine("Testing abstract classes that might have methods reachable through devirtualization");

            // Force a vtable for Base
            typeof(Base).ToString();

            // Do a devirtualizable virtual call to something that was never allocated
            // and uses a virtual method implementation from Base.
            DoIt(null);

            ThrowIfPresent(typeof(TestAbstractNeverDerivedWithDevirtualizedCall), nameof(UnreferencedType1));
        }
    }

    class TestAbstractDerivedByUnrelatedTypeWithDevirtualizedCall
    {
        static void DoIt(Derived1 d) => d?.DoSomething();

        abstract class Base
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            public virtual void DoSomething() => new UnreferencedType1().ToString();
        }

        sealed class Derived1 : Base { }

        sealed class Derived2 : Base
        {
            public override void DoSomething() { }
        }

        class UnreferencedType1 { }

        public static void Run()
        {
            Console.WriteLine("Testing more abstract classes that might have methods reachable through devirtualization");

            // Force a vtable for Base
            typeof(Base).ToString();

            // Do a devirtualizable virtual call to something that was never allocated
            // and uses a virtual method implementation from Base.
            DoIt(null);

            new Derived2().DoSomething();

            ThrowIfPresent(typeof(TestAbstractDerivedByUnrelatedTypeWithDevirtualizedCall), nameof(UnreferencedType1));
        }
    }

    class TestUnusedDefaultInterfaceMethod
    {
        interface IFoo<T>
        {
            void DoSomething();
        }

        interface IBar<T> : IFoo<T>
        {
            void IFoo<T>.DoSomething()
            {
                Activator.CreateInstance(typeof(NeverReferenced));
            }
        }

        class NeverReferenced { }

        class SomeInstance : IBar<object>
        {
            void IFoo<object>.DoSomething() { }
        }

        static IFoo<object> s_instance = new SomeInstance();

        public static void Run()
        {
            s_instance.DoSomething();

            ThrowIfPresent(typeof(TestUnusedDefaultInterfaceMethod), nameof(NeverReferenced));
        }
    }

    class TestInlinedDeadBranchElimination
    {
        static int GetIntConstant() => 42;
        static int GetIntConstantWrapper() => GetIntConstant();

        class NeverReferenced1 { }

        enum MyEnum { One, Two }

        static MyEnum GetEnumConstant() => MyEnum.Two;

        class NeverReferenced2 { }

        public static void Run()
        {
            if (GetIntConstantWrapper() == 1)
            {
                Activator.CreateInstance(typeof(NeverReferenced1));
            }

            ThrowIfPresent(typeof(TestInlinedDeadBranchElimination), nameof(NeverReferenced1));

            if (GetEnumConstant() == MyEnum.One)
            {
                Activator.CreateInstance(typeof(NeverReferenced2));
            }

            ThrowIfPresent(typeof(TestInlinedDeadBranchElimination), nameof(NeverReferenced2));
        }
    }

    class TestComplexInlinedDeadBranchElimination
    {
        class Log
        {
            public static Log Instance;

            public bool IsEnabled => false;
        }

        class OperatingSystem
        {
            public static bool IsInterix => false;
        }

        public static bool CombinedCheck() => Log.Instance.IsEnabled || OperatingSystem.IsInterix;

        class NeverReferenced1 { }

        public static void Run()
        {
            bool didThrow = false;

            // CombinedCheck is going to throw a NullRef but we still should have been able to deadcode
            // the Log.Instance.IsEnabled call (this pattern is common in EventSources).
            try
            {
                if (CombinedCheck())
                {
                    Activator.CreateInstance(typeof(NeverReferenced1));
                }
            }
            catch (NullReferenceException)
            {
                didThrow = true;
            }

            if (!didThrow)
                throw new Exception();

            ThrowIfPresent(typeof(TestComplexInlinedDeadBranchElimination), nameof(NeverReferenced1));
        }
    }

    class TestArrayElementTypeOperations
    {
        public static void Run()
        {
            Console.WriteLine("Testing array element type optimizations");

            // We consider valuetype elements of arrays constructed...
            {
                Array arr = new NeverAllocated1[1];
                ThrowIfNotPresent(typeof(TestArrayElementTypeOperations), nameof(Marker1));

                // The reason they're considered constructed is runtime magic here
                // Make sure that works too.
                object o = arr.GetValue(0);
                if (!o.ToString().Contains(nameof(Marker1)))
                    throw new Exception();
            }

            // ...but not reference type element types
            {
                Array arr = new NeverAllocated3[1];
                arr.GetValue(0);
                ThrowIfPresent(typeof(TestArrayElementTypeOperations), nameof(Marker3));
            }
        }

        class Marker1 { }
        struct NeverAllocated1
        {
            public override string ToString() => typeof(Marker1).ToString();
        }

        class Marker2 { }
        struct NeverAllocated2
        {
            public override string ToString() => typeof(Marker2).ToString();
        }

        class Marker3 { }
        class NeverAllocated3
        {
            public override string ToString() => typeof(Marker3).ToString();
        }
    }

    class TestStaticVirtualMethodOptimizations
    {
        interface IFoo
        {
            static abstract Type Frob();
        }

        struct StructWithReachableStaticVirtual : IFoo
        {
            public static Type Frob() => typeof(Marker1);
        }

        class ClassWithUnreachableStaticVirtual : IFoo
        {
            public static Type Frob() => typeof(Marker2);
        }

        class Marker1 { }
        class Marker2 { }

        static Type Call<T>() where T : IFoo => T.Frob();

        public static void Run()
        {
            Console.WriteLine("Testing unused static virtual method optimization");

            // No shared generic code - we should not see IFoo.Frob as "virtually used"
            Call<StructWithReachableStaticVirtual>();

            // Implements IFoo.Frob, but there's no consumption place, so won't be generated.
            new ClassWithUnreachableStaticVirtual().ToString();

            ThrowIfNotPresent(typeof(TestStaticVirtualMethodOptimizations), nameof(Marker1));
            ThrowIfPresent(typeof(TestStaticVirtualMethodOptimizations), nameof(Marker2));
        }
    }


    class TestTypeIs
    {
        class Never1 { }
        class Canary1 { }

        class Maybe1<T, U> { }

        [MethodImpl(MethodImplOptions.NoInlining)]
        static object GetTheObject() => new object();

        static volatile object s_sink;

        public static void Run()
        {
#if !DEBUG
            {
                RunCheck(GetTheObject());

                static void RunCheck(object t)
                {
                    if (t is Never1)
                    {
                        s_sink = new Canary1();
                    }
                }

                ThrowIfPresent(typeof(TestTypeIs), nameof(Canary1));
            }

            {
                RunCheck<object>(new Maybe1<object, string>());

                [MethodImpl(MethodImplOptions.NoInlining)]
                static void RunCheck<T>(object t)
                {
                    if (t is Maybe1<T, string>)
                    {
                        return;
                    }
                    throw new Exception();
                }
            }
#endif
        }
    }

    class TestTypeEquals
    {
        sealed class Gen<T> { }

        sealed class Never { }

        class Never2 { }
        class Canary2 { }
        class Never3 { }
        class Canary3 { }
        class Never4 { }
        class Canary4 { }

        class Maybe1<T, U> { }

        [MethodImpl(MethodImplOptions.NoInlining)]
        static Type GetTheType() => null;

        [MethodImpl(MethodImplOptions.NoInlining)]
        static Type GetThePointerType() => typeof(void*);

        [MethodImpl(MethodImplOptions.NoInlining)]
        static object GetTheObject() => new object();

        static volatile object s_sink;

        public static void Run()
        {
            // This was asserting the BCL because Never would not have reflection metadata
            // despite the typeof
            Console.WriteLine(GetTheType() == typeof(Never));

            // This was a compiler crash
            Console.WriteLine(typeof(object) == typeof(Gen<>));

#if !DEBUG
            ThrowIfPresent(typeof(TestTypeEquals), nameof(Never));

            {
                RunCheck(GetTheType());

                static void RunCheck(Type t)
                {
                    if (t == typeof(Never2))
                    {
                        s_sink = new Canary2();
                    }
                }

                ThrowIfPresent(typeof(TestTypeEquals), nameof(Canary2));
            }

            {

                RunCheck(GetTheObject());

                static void RunCheck(object o)
                {
                    if (o.GetType() == typeof(Never3))
                    {
                        s_sink = new Canary3();
                    }
                }

                ThrowIfPresent(typeof(TestTypeEquals), nameof(Canary3));
            }

            {

                RunCheck(GetTheObject());

                static void RunCheck(object o)
                {
                    if (typeof(Never4) == o.GetType())
                    {
                        s_sink = new Canary4();
                    }
                }

                ThrowIfPresent(typeof(TestTypeEquals), nameof(Canary4));
            }

            {
                RunCheck(GetThePointerType());

                static void RunCheck(Type t)
                {
                    if (t == typeof(void*))
                    {
                        return;
                    }
                    throw new Exception();
                }
            }

            {
                RunCheck<object>(typeof(Maybe1<object, string>));

                [MethodImpl(MethodImplOptions.NoInlining)]
                static void RunCheck<T>(Type t)
                {
                    if (t == typeof(Maybe1<T, string>))
                    {
                        return;
                    }
                    throw new Exception();
                }
            }
#endif
        }
    }

    class TestTypeEqualityDeadBranchScanRemoval
    {
        class NeverAllocated1 { }
        class NeverAllocated2 { }
        class NeverAllocated3 { }

        class PossiblyAllocated1 { }
        class PossiblyAllocated2 { }

        class MyAttribute : Attribute
        {
            public Type TheType;

            public MyAttribute(Type t) => TheType = t;
        }

        [My(typeof(NeverAllocated3))]
        class AttributeHolder { }

        [MethodImpl(MethodImplOptions.NoInlining)]
        static Type GetNeverObject() => null;

        [MethodImpl(MethodImplOptions.NoInlining)]
        static Type GetNeverAllocated3Type() => typeof(AttributeHolder).GetCustomAttribute<MyAttribute>().TheType;

        static volatile Type s_sink;

        public static void Run()
        {
            if (GetNeverObject() == typeof(NeverAllocated1))
            {
                Console.WriteLine(new NeverAllocated1().ToString());
                Console.WriteLine(new NeverAllocated2().ToString());
            }
#if !DEBUG
            ThrowIfPresentWithUsableMethodTable(typeof(TestTypeEqualityDeadBranchScanRemoval), nameof(NeverAllocated1));
            ThrowIfPresent(typeof(TestTypeEqualityDeadBranchScanRemoval), nameof(NeverAllocated2));
#endif

            if (GetNeverObject() == typeof(PossiblyAllocated1))
            {
                Console.WriteLine(new PossiblyAllocated1().ToString());
                Console.WriteLine(new PossiblyAllocated2().ToString());
            }
            if (Environment.GetEnvironmentVariable("SURETHING") != null)
                s_sink = typeof(PossiblyAllocated1);

            if (GetNeverAllocated3Type() == typeof(NeverAllocated3))
            {
                Console.WriteLine($"{nameof(NeverAllocated3)} check succeeded");
            }
            else
            {
                throw new Exception();
            }
        }
    }


    class TestTypeIsEnum
    {
        class Never { }

        class Ever { }

        static void Generic<T>()
        {
            if (typeof(T).IsEnum)
            {
                Activator.CreateInstance(typeof(Never));
            }

            Activator.CreateInstance(typeof(Ever));
        }

        public static void Run()
        {
            Generic<object>();

            ThrowIfPresent(typeof(TestTypeIsEnum), nameof(Never));
            ThrowIfNotPresent(typeof(TestTypeIsEnum), nameof(Ever));
        }
    }

    class TestTypeIsValueType
    {
        class Never { }

        class Ever { }

        static void Generic<T>()
        {
            if (typeof(T).IsValueType)
            {
                Activator.CreateInstance(typeof(Never));
            }

            Activator.CreateInstance(typeof(Ever));
        }

        public static void Run()
        {
            Generic<object>();

            ThrowIfPresent(typeof(TestTypeIsValueType), nameof(Never));
            ThrowIfNotPresent(typeof(TestTypeIsValueType), nameof(Ever));
        }
    }

    class TestBranchesInGenericCodeRemoval
    {
        class ClassWithUnusedVirtual
        {
            public virtual string MyUnusedVirtualMethod() => typeof(UnusedFromVirtual).ToString();
            public virtual string MyUsedVirtualMethod() => typeof(UsedFromVirtual).ToString();
        }

        class UnusedFromVirtual { }
        class UsedFromVirtual { }

        struct Unused { public byte Val; }
        struct Used { public byte Val; }

        [MethodImpl(MethodImplOptions.NoInlining)]
        static T Cast<T>(byte o, ClassWithUnusedVirtual inst)
        {
            if (typeof(T) == typeof(Unused))
            {
                // Expect this not to be scanned. The virtual slot should not be created.
                inst.MyUnusedVirtualMethod();

                Unused result = new Unused { Val = o };
                return (T)(object)result;
            }
            else if (typeof(T) == typeof(Used))
            {
                // This will introduce a virtual slot.
                inst.MyUsedVirtualMethod();

                Used result = new Used { Val = o };
                return (T)(object)result;
            }
            return default;
        }

        public static void Run()
        {
            Console.WriteLine("Testing dead branches guarded by typeof in generic code removal");

            Cast<Used>(12, new ClassWithUnusedVirtual());

            // We only expect to be able to get rid of it when optimizing
#if !DEBUG
            ThrowIfPresent(typeof(TestBranchesInGenericCodeRemoval), nameof(Unused));
#endif
            ThrowIfNotPresent(typeof(TestBranchesInGenericCodeRemoval), nameof(Used));

            ThrowIfPresent(typeof(TestBranchesInGenericCodeRemoval), nameof(UnusedFromVirtual));
            ThrowIfNotPresent(typeof(TestBranchesInGenericCodeRemoval), nameof(UsedFromVirtual));
        }
    }

    class TestUnmodifiableStaticFieldOptimization
    {
        static class ClassWithNotReadOnlyField
        {
            public static int SomeValue = 42;
        }

        class Canary
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            public int GrabNotReadOnlyField() => ClassWithNotReadOnlyField.SomeValue;
        }

        class ClassThatShouldBePreinited
        {
            public static int Value = new Canary().GrabNotReadOnlyField();
        }

        public static void Run()
        {
            // This test is using a pretty roundabout way to test the following thing:
            // * The compiler should be able to figure out ClassWithNotReadOnlyField.SomeValue
            //   is effectively readonly (even though it wasn't annotated as such in source code).
            // * Therefore, it should be able to preinitialize ClassThatShouldBePreinited.
            // * Because ClassThatShouldBePreinited was preinitialized at compile time, we don't
            //   actually have a MethodTable for it in the program.
            // * It is therefore not reflection visible.
            // We're testing the optimizations mentioned above work by inspecting the side effect
            // (that is only visible to trim-unsafe code).
            Console.WriteLine($"Testing we were able to make non-readonly field read-only: {ClassThatShouldBePreinited.Value}");
#if !DEBUG
            ThrowIfPresentWithUsableMethodTable(typeof(TestUnmodifiableStaticFieldOptimization), nameof(Canary));
#endif
        }
    }

    class TestUnmodifiableInstanceFieldOptimization
    {
        class Canary1
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            public void Make() { }
        }

        class Canary2
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            public void Make() { }
        }

        class Canary3
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            public void Make() { }
        }

        class Canary4
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            public void Make() { }
        }

        class Canary5
        {
            [MethodImpl(MethodImplOptions.NoInlining)]
            public void Make() { }
        }

        class CanBeMadeReadOnly
        {
            public object Field;
            public static CanBeMadeReadOnly Instance = new CanBeMadeReadOnly();
            static CanBeMadeReadOnly() => new Canary1().Make();
        }

        class IsReflectedOn
        {
            public object Field;
            public static IsReflectedOn Instance = new IsReflectedOn();
            static IsReflectedOn() => new Canary2().Make();
        }

        class IsModified
        {
            public object Field;
            public static IsModified Instance = new IsModified();
            static IsModified() => new Canary3().Make();
        }

        class CanBeMadeReadOnlyProperty
        {
            public object Field { get; }
            public static CanBeMadeReadOnlyProperty Instance = new CanBeMadeReadOnlyProperty();
            static CanBeMadeReadOnlyProperty() => new Canary4().Make();
        }

        class WithInitOnlyPropertyWrite
        {
            public object Field { get; init; }
            public static WithInitOnlyPropertyWrite Instance = new WithInitOnlyPropertyWrite();
            static WithInitOnlyPropertyWrite() => new Canary5().Make();
        }

        public static void Run()
        {
            Console.WriteLine(CanBeMadeReadOnly.Instance);
            Console.WriteLine(IsReflectedOn.Instance);
            Console.WriteLine(IsModified.Instance);
            Console.WriteLine(CanBeMadeReadOnlyProperty.Instance);
            Console.WriteLine(WithInitOnlyPropertyWrite.Instance);

            IsModified.Instance.Field = new object();
            typeof(IsReflectedOn).GetFields();
            new WithInitOnlyPropertyWrite() { Field = new object() };

            // Types that got preinitialized at compile time will not bring the canary class
            // instance into the program.
            // On the other hand types that should not have been preinitialized for correctness
            // need the canary in the cctor.

#if !DEBUG
            ThrowIfPresentWithUsableMethodTable(typeof(TestUnmodifiableInstanceFieldOptimization), nameof(Canary1));
#endif
            ThrowIfNotPresent(typeof(TestUnmodifiableInstanceFieldOptimization), nameof(Canary2));
            ThrowIfNotPresent(typeof(TestUnmodifiableInstanceFieldOptimization), nameof(Canary3));
#if !DEBUG
            ThrowIfPresentWithUsableMethodTable(typeof(TestUnmodifiableInstanceFieldOptimization), nameof(Canary4));
#endif
            ThrowIfNotPresent(typeof(TestUnmodifiableInstanceFieldOptimization), nameof(Canary5));
        }
    }

    class TestGetMethodOptimization
    {
        delegate void ReflectedOnDelegate();
        delegate void NotReflectedOnDelegate();
        delegate void ReflectedOnGenericDelegate<T>();
        delegate void NotReflectedOnGenericDelegate<T>();
        delegate void AnotherReflectedOnDelegate();

        static class Delegates
        {
            public static void Method1() { }
            public static ReflectedOnDelegate GetReflectedOnDelegate() => Method1;

            public static void Method2() { }
            public static NotReflectedOnDelegate GetNotReflectedOnDelegate() => Method2;

            public static void Method3() { }
            public static ReflectedOnGenericDelegate<T> GetReflectedOnGenericDelegate<T>() => Method3;

            public static void Method4() { }
            public static NotReflectedOnGenericDelegate<T> GetNotReflectedOnGenericDelegate<T>() => Method4;

            public static void Method5() { }
            public static AnotherReflectedOnDelegate GetAnotherReflectedOnDelegate() => Method5;
        }

        static MethodInfo GetReflectedOnGenericDelegate<T>() => Delegates.GetReflectedOnGenericDelegate<T>().Method;

        static NotReflectedOnGenericDelegate<T> GetNotReflectedOnGenericDelegate<T>() => Delegates.GetNotReflectedOnGenericDelegate<T>();

        [UnconditionalSuppressMessage("ReflectionAnalysis", "IL2075:UnrecognizedReflectionPattern",
            Justification = "That's the point")]
        public static void Run()
        {
            Type t = GetTypeSecretly(typeof(TestGetMethodOptimization), nameof(Delegates));

            {
                ReflectedOnDelegate del = Delegates.GetReflectedOnDelegate();
                MethodInfo mi = t.GetMethod(nameof(Delegates.Method1));
                if (del.Method != mi)
                    throw new Exception();
            }

            {
                NotReflectedOnDelegate del = Delegates.GetNotReflectedOnDelegate();
                MethodInfo mi = t.GetMethod(nameof(Delegates.Method2));
                if (mi != null)
                    throw new Exception();
            }

            {
                MethodInfo m = GetReflectedOnGenericDelegate<string>();
                MethodInfo mi = t.GetMethod(nameof(Delegates.Method3));
                if (m != mi)
                    throw new Exception();
            }

            {
                NotReflectedOnGenericDelegate<string> del = GetNotReflectedOnGenericDelegate<string>();
                MethodInfo mi = t.GetMethod(nameof(Delegates.Method4));
                if (mi != null)
                    throw new Exception();
            }

            {
                AnotherReflectedOnDelegate del = Delegates.GetAnotherReflectedOnDelegate();
                MethodInfo mi = t.GetMethod(nameof(Delegates.Method5));
                if (del.GetMethodInfo() != mi)
                    throw new Exception();
            }
        }
    }

    class TestTypeOfCodegenBranchElimination
    {
        class Never1 { }
        class Never2 { }
        class Never3 { }
        class Never4<T> { }
        class Never5<T> { }
        class Never6<T> { }

        class Canary1 { }
        class Canary2 { }
        class Canary3 { }
        class Canary4 { }
        class Canary5 { }
        class Canary6 { }

        class Maybe1<T> { }

        class Marker1 { }

        class Atom1 { }

        interface IDynamicCastableImplemented { void A(); }
        [DynamicInterfaceCastableImplementation]
        interface IDynamicCastableImplementedImpl : IDynamicCastableImplemented { void IDynamicCastableImplemented.A() { } }
        class DynamicInterfaceCastable : IDynamicInterfaceCastable
        {
            RuntimeTypeHandle IDynamicInterfaceCastable.GetInterfaceImplementation(RuntimeTypeHandle interfaceType) => typeof(IDynamicCastableImplementedImpl).TypeHandle;
            bool IDynamicInterfaceCastable.IsInterfaceImplemented(RuntimeTypeHandle interfaceType, bool throwIfNotImplemented) => true;
        }

        [UnconditionalSuppressMessage("AotAnalysis", "IL3050:UnrecognizedAotPattern",
            Justification = "That's the point")]
        public static void Run()
        {
            if (GetUnknownType().GetType() == typeof(Never1))
            {
                Consume(new Canary1());
            }
#if !DEBUG
            ThrowIfPresentWithUsableMethodTable(typeof(TestTypeOfCodegenBranchElimination), nameof(Canary1));
#endif

            if (GetUnknownType() is Never2)
            {
                Consume(new Canary2());
            }
#if !DEBUG
            ThrowIfPresentWithUsableMethodTable(typeof(TestTypeOfCodegenBranchElimination), nameof(Canary2));
#endif

            IsNever3<object>(new object());
            [MethodImpl(MethodImplOptions.NoInlining)]
            static void IsNever3<T>(object o)
            {
                if (typeof(T) == typeof(Never3))
                {
                    Consume(new Canary3());
                }
            }
#if false // This optimization is disabled for now, don't check.
            ThrowIfPresentWithUsableMethodTable(typeof(TestTypeOfCodegenBranchElimination), nameof(Canary3));
#endif

            // *********

            if (GetUnknownType().GetType() == typeof(Never4<object>))
            {
                Consume(new Canary4());
            }
#if !DEBUG
            ThrowIfPresentWithUsableMethodTable(typeof(TestTypeOfCodegenBranchElimination), nameof(Canary4));
#endif

            if (GetUnknownType() is Never5<object>)
            {
                Consume(new Canary5());
            }
#if !DEBUG
            ThrowIfPresentWithUsableMethodTable(typeof(TestTypeOfCodegenBranchElimination), nameof(Canary5));
#endif

            IsNever6<object>(new object());
            [MethodImpl(MethodImplOptions.NoInlining)]
            static void IsNever6<T>(object o)
            {
                if (typeof(T) == typeof(Never6<object>))
                {
                    Consume(new Canary6());
                }
            }
#if false // This optimization is disabled for now, don't check.
            ThrowIfPresentWithUsableMethodTable(typeof(TestTypeOfCodegenBranchElimination), nameof(Canary6));
#endif

            // ************

            Activator.CreateInstance(typeof(Maybe1<>).MakeGenericType(GetAtom1()));

            if (GetUnknownType().GetType() == typeof(Maybe1<object>))
            {
                // This should not be optimized away because Maybe1<object> is possible
                // with the type loader template for MakeGeneric above.
                Consume(new Marker1());
            }
            ThrowIfNotPresent(typeof(TestTypeOfCodegenBranchElimination), nameof(Marker1));

            // ************

            if (GetDynamicInterfaceCastableType() is not IDynamicCastableImplemented)
               throw new Exception();

            [MethodImpl(MethodImplOptions.NoInlining)]
            static object GetDynamicInterfaceCastableType() => new DynamicInterfaceCastable();

            [MethodImpl(MethodImplOptions.NoInlining)]
            static void Consume(object o) { }

            [MethodImpl(MethodImplOptions.NoInlining)]
            static object GetUnknownType() => new object();

            [MethodImpl(MethodImplOptions.NoInlining)]
            static Type GetAtom1() => typeof(Atom1);
        }
    }

    class TestInvisibleGenericsTrimming
    {
        class NotPresentType1<T>;
        class NotPresentType2<T>;

        class PresentType<T>;

        [MethodImpl(MethodImplOptions.NoInlining)]
        static bool IsNotPresentType1(object o) => o is NotPresentType1<object>;

        [MethodImpl(MethodImplOptions.NoInlining)]
        static bool IsNotPresentType2(object o) => o.GetType() == typeof(NotPresentType2<object>);

        [MethodImpl(MethodImplOptions.NoInlining)]
        static bool IsPresentType(object o) => o.GetType() == typeof(PresentType<object>);

        public static void Run()
        {
            IsNotPresentType1(new object());
#if !DEBUG
            ThrowIfPresent(typeof(TestInvisibleGenericsTrimming), "NotPresentType1`1");
#endif

            IsNotPresentType2(new object());
#if !DEBUG
            ThrowIfPresent(typeof(TestInvisibleGenericsTrimming), "NotPresentType2`1");
#endif

            IsPresentType(new PresentType<object>());
            ThrowIfNotPresent(typeof(TestInvisibleGenericsTrimming), "PresentType`1");
        }
    }

    class TestTypeHandlesInGenericDictionaries
    {
        class InvisibleType1;
        class InvisibleType2;
        class VisibleType1;

        [MethodImpl(MethodImplOptions.NoInlining)]
        static void GenericMethod<T, U, V>(object o, string expectedNameOfV)
        {
            if (o is T)
                Console.WriteLine("Yes");

            if (o.GetType() == typeof(U))
                Console.WriteLine("Yes");

            if (typeof(V).Name != expectedNameOfV)
                throw new Exception();
        }

        public static void Run()
        {
            GenericMethod<InvisibleType1, InvisibleType2, VisibleType1>(new object(), nameof(VisibleType1));

            ThrowIfPresent(typeof(TestTypeHandlesInGenericDictionaries), nameof(InvisibleType1));
#if !DEBUG
            ThrowIfPresent(typeof(TestTypeHandlesInGenericDictionaries), nameof(InvisibleType2));
#endif
        }
    }

    [UnconditionalSuppressMessage("ReflectionAnalysis", "IL2070:UnrecognizedReflectionPattern",
        Justification = "That's the point")]
    private static Type GetTypeSecretly(Type testType, string typeName) => testType.GetNestedType(typeName, BindingFlags.NonPublic | BindingFlags.Public);

    private static void ThrowIfPresent(Type testType, string typeName)
    {
        if (GetTypeSecretly(testType, typeName) != null)
        {
            throw new Exception(typeName);
        }
    }

    [UnconditionalSuppressMessage("ReflectionAnalysis", "IL2072:UnrecognizedReflectionPattern",
        Justification = "That's the point")]
    private static void ThrowIfPresentWithUsableMethodTable(Type testType, string typeName)
    {
        Type t = GetTypeSecretly(testType, typeName);
        if (t == null)
            return;

        try
        {
            RuntimeHelpers.GetUninitializedObject(t);

            // Should have thrown NotSupported above.
            throw new Exception();
        }
        catch (NotSupportedException) { }
    }

    private static void ThrowIfNotPresent(Type testType, string typeName)
    {
        if (GetTypeSecretly(testType, typeName) == null)
        {
            throw new Exception(typeName);
        }
    }
}
