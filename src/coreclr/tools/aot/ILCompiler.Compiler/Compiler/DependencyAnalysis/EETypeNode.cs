// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;
using System.Collections.Generic;

using Internal.IL;
using Internal.IL.Stubs;
using Internal.Runtime;
using Internal.Text;
using Internal.TypeSystem;

using Debug = System.Diagnostics.Debug;
using GenericVariance = Internal.Runtime.GenericVariance;

namespace ILCompiler.DependencyAnalysis
{
    /// <summary>
    /// Given a type, EETypeNode writes an MethodTable data structure in the format expected by the runtime.
    ///
    /// Format of an MethodTable:
    ///
    /// Field Size      | Contents
    /// ----------------+-----------------------------------
    /// UInt32          | Flags field
    ///                 | Flags for: IsValueType, IsCrossModule, HasPointers, IsInterface, IsGeneric, etc ...
    ///                 | EETypeKind (Normal, Array, Pointer type)
    ///                 |
    ///                 | 5 bits near the top are used for enum EETypeElementType to record whether it's back by an Int32, Int16 etc
    ///                 |
    ///                 | The highest/sign bit indicates whether the lower Uint16 contains a number, which represents:
    ///                 | - element type size for arrays,
    ///                 | - char size for strings (normally 2, since .NET uses UTF16 character encoding),
    ///                 | - for generic type definitions it is the number of generic parameters,
    ///                 |
    ///                 | If the sign bit is not set, then the lower Uint16 is used for additional ExtendedFlags
    ///                 |
    /// Uint32          | Base size.
    ///                 |
    /// [Pointer Size]  | Related type. Base type for regular types. Element type for arrays / pointer types.
    ///                 |
    /// UInt16          | Number of VTable slots (X)
    ///                 |
    /// UInt16          | Number of interfaces implemented by type (Y)
    ///                 |
    /// UInt32          | Hash code
    ///                 |
    /// X * [Ptr Size]  | VTable entries (optional)
    ///                 |
    /// Y * [Ptr Size]  | Pointers to interface map data structures (optional)
    ///                 |
    /// [Relative ptr]  | Pointer to containing TypeManager indirection cell
    ///                 |
    /// [Relative ptr]  | Pointer to writable data
    ///                 |
    /// [Relative ptr]  | Pointer to finalizer method (optional)
    ///                 |
    /// [Relative ptr]  | Pointer to optional fields (optional)
    ///                 |
    /// [Relative ptr]  | Pointer to the generic type definition MethodTable (optional)
    ///                 |
    /// [Relative ptr]  | Pointer to the generic argument and variance info (optional)
    /// </summary>
    public partial class EETypeNode : DehydratableObjectNode, IEETypeNode, ISymbolDefinitionNode, ISymbolNodeWithLinkage
    {
        protected readonly TypeDesc _type;
        private readonly WritableDataNode _writableDataNode;
        protected bool? _mightHaveInterfaceDispatchMap;
        private bool _hasConditionalDependenciesFromMetadataManager;

        protected readonly VirtualMethodAnalysisFlags _virtualMethodAnalysisFlags;

        [Flags]
        protected enum VirtualMethodAnalysisFlags
        {
            None = 0,

            NeedsGvmEntries = 0x0001,
            InterestingForDynamicDependencies = 0x0002,

            AllFlags = NeedsGvmEntries
                | InterestingForDynamicDependencies,
        }

        public EETypeNode(NodeFactory factory, TypeDesc type)
        {
            Debug.Assert(!type.IsCanonicalSubtype(CanonicalFormKind.Any) || type == type.ConvertToCanonForm(CanonicalFormKind.Specific));
            Debug.Assert(!type.IsCanonicalSubtype(CanonicalFormKind.Any) || !type.IsMdArray); // MDArray doesn't have type loader templates
            Debug.Assert(!type.IsGenericParameter);
            Debug.Assert(!type.IsRuntimeDeterminedSubtype);
            _type = type;
            _writableDataNode = !_type.IsCanonicalSubtype(CanonicalFormKind.Any) ? new WritableDataNode(this) : null;
            _hasConditionalDependenciesFromMetadataManager = factory.MetadataManager.HasConditionalDependenciesDueToEETypePresence(type);

            if (EmitVirtualSlots)
                _virtualMethodAnalysisFlags = AnalyzeVirtualMethods(type);

            factory.TypeSystemContext.EnsureLoadableType(type);
        }

        private static VirtualMethodAnalysisFlags AnalyzeVirtualMethods(TypeDesc type)
        {
            var result = VirtualMethodAnalysisFlags.None;

            // Interface EETypes not relevant to virtual method analysis at this time.
            if (type.IsInterface)
                return result;

            DefType defType = type.GetClosestDefType();

            foreach (MethodDesc method in defType.GetAllVirtualMethods())
            {
                // First, check if this type has any GVM that overrides a GVM on a parent type. If that's the case, this makes
                // the current type interesting for GVM analysis (i.e. instantiate its overriding GVMs for existing GVMDependenciesNodes
                // of the instantiated GVM on the parent types).
                if (method.HasInstantiation)
                {
                    result |= VirtualMethodAnalysisFlags.NeedsGvmEntries;

                    MethodDesc slotDecl = MetadataVirtualMethodAlgorithm.FindSlotDefiningMethodForVirtualMethod(method);
                    if (slotDecl != method)
                        result |= VirtualMethodAnalysisFlags.InterestingForDynamicDependencies;
                }

                // Early out if we set all the flags we could have set
                if ((result & VirtualMethodAnalysisFlags.AllFlags) == VirtualMethodAnalysisFlags.AllFlags)
                    return result;
            }

            //
            // Check if the type implements any interface, where the method implementations could be on
            // base types.
            // Example:
            //      interface IFace {
            //          void IFaceGVMethod<U>();
            //      }
            //      class BaseClass {
            //          public virtual void IFaceGVMethod<U>() { ... }
            //      }
            //      public class DerivedClass : BaseClass, IFace { }
            //
            foreach (DefType interfaceImpl in defType.RuntimeInterfaces)
            {
                foreach (MethodDesc method in interfaceImpl.GetAllVirtualMethods())
                {
                    if (!method.HasInstantiation)
                        continue;

                    // We found a GVM on one of the implemented interfaces. Find if the type implements this method.
                    // (Note, do this comparison against the generic definition of the method, not the specific method instantiation
                    MethodDesc slotDecl = method.Signature.IsStatic ?
                        defType.ResolveInterfaceMethodToStaticVirtualMethodOnType(method)
                        : defType.ResolveInterfaceMethodTarget(method);
                    if (slotDecl != null)
                    {
                        // If the type doesn't introduce this interface method implementation (i.e. the same implementation
                        // already exists in the base type), do not consider this type interesting for GVM analysis just yet.
                        //
                        // We need to limit the number of types that are interesting for GVM analysis at all costs since
                        // these all will be looked at for every unique generic virtual method call in the program.
                        // Having a long list of interesting types affects the compilation throughput heavily.
                        if (slotDecl.OwningType == defType ||
                            defType.BaseType.ResolveInterfaceMethodTarget(method) != slotDecl)
                        {
                            result |= VirtualMethodAnalysisFlags.InterestingForDynamicDependencies
                                | VirtualMethodAnalysisFlags.NeedsGvmEntries;
                        }
                    }
                    else
                    {
                        // The method could be implemented by a default interface method
                        var resolution = defType.ResolveInterfaceMethodToDefaultImplementationOnType(method, out _);
                        if (resolution == DefaultInterfaceMethodResolution.DefaultImplementation)
                        {
                            result |= VirtualMethodAnalysisFlags.InterestingForDynamicDependencies
                                | VirtualMethodAnalysisFlags.NeedsGvmEntries;
                        }
                    }

                    // Early out if we set all the flags we could have set
                    if ((result & VirtualMethodAnalysisFlags.AllFlags) == VirtualMethodAnalysisFlags.AllFlags)
                        return result;
                }
            }

            return result;
        }

        protected bool MightHaveInterfaceDispatchMap(NodeFactory factory)
        {
            if (!_mightHaveInterfaceDispatchMap.HasValue)
            {
                _mightHaveInterfaceDispatchMap = EmitVirtualSlots && InterfaceDispatchMapNode.MightHaveInterfaceDispatchMap(_type, factory);
            }

            return _mightHaveInterfaceDispatchMap.Value;
        }

        protected override string GetName(NodeFactory factory) => this.GetMangledName(factory.NameMangler);

        public override bool ShouldSkipEmittingObjectNode(NodeFactory factory)
        {
            // If there is a constructed version of this node in the graph, emit that instead
            if (ConstructedEETypeNode.CreationAllowed(_type))
                return factory.ConstructedTypeSymbol(_type).Marked;

            return false;
        }

        public virtual ISymbolNode NodeForLinkage(NodeFactory factory)
        {
            return factory.NecessaryTypeSymbol(_type);
        }

        public TypeDesc Type => _type;

        protected override ObjectNodeSection GetDehydratedSection(NodeFactory factory)
        {
            if (factory.Target.IsWindows)
                return ObjectNodeSection.ReadOnlyDataSection;
            else
                return ObjectNodeSection.DataSection;
        }

        public int MinimumObjectSize => EETypeBuilderHelpers.GetMinimumObjectSize(_type.Context);

        protected virtual bool EmitVirtualSlots => false;

        public override bool InterestingForDynamicDependencyAnalysis
            => (_virtualMethodAnalysisFlags & VirtualMethodAnalysisFlags.InterestingForDynamicDependencies) != 0;

        public override bool StaticDependenciesAreComputed => true;

        public static string GetMangledName(TypeDesc type, NameMangler nameMangler)
        {
            return nameMangler.NodeMangler.MethodTable(type);
        }

        public virtual void AppendMangledName(NameMangler nameMangler, Utf8StringBuilder sb)
        {
            sb.Append(nameMangler.NodeMangler.MethodTable(_type));
        }

        int ISymbolNode.Offset => 0;
        int ISymbolDefinitionNode.Offset => GCDescSize;

        public override bool IsShareable => IsTypeNodeShareable(_type);

        private bool CanonFormTypeMayExist
        {
            get
            {
                if (_type.IsArrayTypeWithoutGenericInterfaces())
                    return false;

                if (!_type.Context.SupportsCanon)
                    return false;

                // If type is already in canon form, a canonically equivalent type cannot exist
                if (_type.IsCanonicalSubtype(CanonicalFormKind.Any))
                    return false;

                // Attempt to convert to canon. If the type changes, then the CanonForm exists
                return (_type.ConvertToCanonForm(CanonicalFormKind.Specific) != _type);
            }
        }

        public override bool HasConditionalStaticDependencies
        {
            get
            {
                // If the type is can be converted to some interesting canon type, and this is the non-constructed variant of an MethodTable
                // we may need to trigger the fully constructed type to exist to make the behavior of the type consistent
                // in reflection and generic template expansion scenarios
                if (CanonFormTypeMayExist)
                {
                    return true;
                }

                // If the type implements at least one interface, calls against that interface could result in this type's
                // implementation being used.
                // It might also be necessary for casting purposes.
                if (_type.RuntimeInterfaces.Length > 0)
                    return true;

                if (!EmitVirtualSlots)
                    return false;

                // Since the vtable is dependency driven, generate conditional static dependencies for
                // all possible vtable entries.
                //
                // The conditional dependencies conditionally add the implementation of the virtual method
                // if the virtual method is used.
                //
                // We walk the inheritance chain because abstract bases would only add a "tentative"
                // method body of the implementation that can be trimmed away if no other type uses it.
                DefType currentType = _type.GetClosestDefType();
                while (currentType != null)
                {
                    if (currentType == _type || (currentType is MetadataType mdType && mdType.IsAbstract))
                    {
                        foreach (var method in currentType.GetAllVirtualMethods())
                        {
                            // Abstract methods don't have a body associated with it so there's no conditional
                            // dependency to add.
                            // Generic virtual methods are tracked by an orthogonal mechanism.
                            if (!method.IsAbstract && !method.HasInstantiation)
                                return true;
                        }
                    }

                    currentType = currentType.BaseType;
                }

                return _hasConditionalDependenciesFromMetadataManager;
            }
        }

        public override IEnumerable<CombinedDependencyListEntry> GetConditionalStaticDependencies(NodeFactory factory)
        {
            List<CombinedDependencyListEntry> result = new List<CombinedDependencyListEntry>();

            IEETypeNode maximallyConstructableType = factory.MaximallyConstructableType(_type);

            if (maximallyConstructableType != this)
            {
                // MethodTable upgrading from necessary to constructed if some template instantiation exists that matches up
                // This ensures we don't end up having two EETypes in the system (one is this necessary type, and another one
                // that was dynamically created at runtime).
                if (CanonFormTypeMayExist)
                {
                    result.Add(new CombinedDependencyListEntry(maximallyConstructableType, factory.MaximallyConstructableType(_type.ConvertToCanonForm(CanonicalFormKind.Specific)), "Trigger full type generation if canonical form exists"));
                }
                return result;
            }

            TypeDesc canonOwningType = _type.ConvertToCanonForm(CanonicalFormKind.Specific);
            if (_type.IsDefType && _type != canonOwningType)
            {
                result.Add(new CombinedDependencyListEntry(
                    factory.GenericStaticBaseInfo((MetadataType)_type),
                    factory.NativeLayout.TemplateTypeLayout(canonOwningType),
                    "Information about static bases for type with template"));
            }

            if (!_type.IsCanonicalSubtype(CanonicalFormKind.Any))
            {
                foreach (DefType iface in _type.RuntimeInterfaces)
                {
                    var ifaceDefinition = (DefType)iface.GetTypeDefinition();
                    result.Add(new CombinedDependencyListEntry(
                        GetInterfaceTypeNode(factory, iface),
                        factory.InterfaceUse(ifaceDefinition),
                        "Interface definition was visible"));
                }
            }

            if (!EmitVirtualSlots)
                return result;

            DefType defType = _type.GetClosestDefType();

            // If we're producing a full vtable, none of the dependencies are conditional.
            if (!factory.VTable(defType).HasKnownVirtualMethodUse)
            {
                bool isNonInterfaceAbstractType = !defType.IsInterface && ((MetadataType)defType).IsAbstract;

                foreach (MethodDesc decl in defType.EnumAllVirtualSlots())
                {
                    // Generic virtual methods are tracked by an orthogonal mechanism.
                    if (decl.HasInstantiation)
                        continue;

                    MethodDesc impl = defType.FindVirtualFunctionTargetMethodOnObjectType(decl);
                    bool implOwnerIsAbstract = ((MetadataType)impl.OwningType).IsAbstract;

                    // We add a conditional dependency in two situations:
                    // 1. The implementation is on this type. This is pretty obvious.
                    // 2. The implementation comes from an abstract base type. We do this
                    //    because abstract types only request a TentativeMethodEntrypoint of the implementation.
                    //    The actual method body of this entrypoint might still be trimmed away.
                    //    We don't need to do this for implementations from non-abstract bases since
                    //    non-abstract types will create a hard conditional reference to their virtual
                    //    method implementations.
                    //
                    // We also skip abstract methods since they don't have a body to refer to.
                    if ((impl.OwningType == defType || implOwnerIsAbstract) && !impl.IsAbstract)
                    {
                        MethodDesc canonImpl = impl.GetCanonMethodTarget(CanonicalFormKind.Specific);

                        // If this is an abstract type, only request a tentative entrypoint (whose body
                        // might just be stubbed out). This lets us avoid generating method bodies for
                        // virtual method on abstract types that are overridden in all their children.
                        //
                        // We don't do this if the method can be placed in the sealed vtable since
                        // those can never be overridden by children anyway.
                        bool canUseTentativeMethod = isNonInterfaceAbstractType
                            && !decl.CanMethodBeInSealedVTable(factory)
                            && factory.CompilationModuleGroup.AllowVirtualMethodOnAbstractTypeOptimization(canonImpl);
                        IMethodNode implNode = canUseTentativeMethod ?
                            factory.TentativeMethodEntrypoint(canonImpl, impl.OwningType.IsValueType) :
                            factory.MethodEntrypoint(canonImpl, impl.OwningType.IsValueType);
                        result.Add(new CombinedDependencyListEntry(implNode, factory.VirtualMethodUse(decl), "Virtual method"));

                        result.Add(new CombinedDependencyListEntry(
                            factory.AddressTakenMethodEntrypoint(canonImpl, impl.OwningType.IsValueType),
                            factory.DelegateTargetVirtualMethod(decl.GetCanonMethodTarget(CanonicalFormKind.Specific)), "Slot is a delegate target"));
                    }

                    if (impl.OwningType == defType)
                    {
                        factory.MetadataManager.NoteOverridingMethod(decl, impl);
                    }

                    factory.MetadataManager.GetDependenciesForOverridingMethod(ref result, factory, decl, impl);
                }

                Debug.Assert(
                    _type == defType ||
                    ((System.Collections.IStructuralEquatable)defType.RuntimeInterfaces).Equals(_type.RuntimeInterfaces,
                    EqualityComparer<DefType>.Default));

                // Interfaces don't have vtables and we don't need to track their instance method slot use.
                // The only exception are those interfaces that provide IDynamicInterfaceCastable implementations;
                // those have slots and we dispatch on them.
                bool needsDependenciesForInstanceInterfaceMethodImpls = !defType.IsInterface
                    || ((MetadataType)defType).IsDynamicInterfaceCastableImplementation();

                // Add conditional dependencies for interface methods the type implements. For example, if the type T implements
                // interface IFoo which has a method M1, add a dependency on T.M1 dependent on IFoo.M1 being called, since it's
                // possible for any IFoo object to actually be an instance of T.
                DefType defTypeDefinition = (DefType)defType.GetTypeDefinition();
                DefType[] defTypeRuntimeInterfaces = defType.RuntimeInterfaces;
                DefType[] defTypeDefinitionRuntimeInterfaces = defTypeDefinition.RuntimeInterfaces;
                Debug.Assert(defTypeDefinitionRuntimeInterfaces.Length == defTypeRuntimeInterfaces.Length);
                for (int interfaceIndex = 0; interfaceIndex < defTypeRuntimeInterfaces.Length; interfaceIndex++)
                {
                    DefType interfaceType = defTypeRuntimeInterfaces[interfaceIndex];
                    DefType definitionInterfaceType = defTypeDefinitionRuntimeInterfaces[interfaceIndex];

                    Debug.Assert(interfaceType.IsInterface);

                    bool isVariantInterfaceImpl = VariantInterfaceMethodUseNode.IsVariantInterfaceImplementation(factory, _type, interfaceType);

                    foreach (MethodDesc interfaceMethod in interfaceType.GetAllVirtualMethods())
                    {
                        // Generic virtual methods are tracked by an orthogonal mechanism.
                        if (interfaceMethod.HasInstantiation)
                            continue;

                        bool isStaticInterfaceMethod = interfaceMethod.Signature.IsStatic;

                        if (!isStaticInterfaceMethod && !needsDependenciesForInstanceInterfaceMethodImpls)
                            continue;

                        MethodDesc interfaceMethodDefinition = interfaceMethod;
                        if (interfaceType != definitionInterfaceType)
                            interfaceMethodDefinition = factory.TypeSystemContext.GetMethodForInstantiatedType(interfaceMethodDefinition.GetTypicalMethodDefinition(), (InstantiatedType)definitionInterfaceType);

                        MethodDesc implMethod = isStaticInterfaceMethod ?
                            defTypeDefinition.ResolveInterfaceMethodToStaticVirtualMethodOnType(interfaceMethodDefinition) :
                            defTypeDefinition.ResolveInterfaceMethodToVirtualMethodOnType(interfaceMethodDefinition);
                        if (implMethod != null)
                        {
                            TypeDesc implType = defType;
                            while (!implType.HasSameTypeDefinition(implMethod.OwningType))
                                implType = implType.BaseType;

                            if (!implType.IsTypeDefinition)
                                implMethod = factory.TypeSystemContext.GetMethodForInstantiatedType(implMethod.GetTypicalMethodDefinition(), (InstantiatedType)implType);

                            if (isStaticInterfaceMethod)
                            {
                                Debug.Assert(!implMethod.IsVirtual);

                                MethodDesc defaultIntfMethod = implMethod.GetCanonMethodTarget(CanonicalFormKind.Specific);

                                // If the interface method is used virtually, the implementation body is used
                                result.Add(new CombinedDependencyListEntry(factory.MethodEntrypoint(defaultIntfMethod), factory.VirtualMethodUse(interfaceMethod), "Interface method"));

                                // If the interface method is virtual delegate target, the implementation is address taken
                                result.Add(new CombinedDependencyListEntry(
                                    factory.AddressTakenMethodEntrypoint(defaultIntfMethod),
                                    factory.DelegateTargetVirtualMethod(interfaceMethod.GetCanonMethodTarget(CanonicalFormKind.Specific)), "Interface slot is delegate target"));
                            }
                            else
                            {
                                // If the interface method is used virtually, the slot is used virtually
                                result.Add(new CombinedDependencyListEntry(factory.VirtualMethodUse(implMethod), factory.VirtualMethodUse(interfaceMethod), "Interface method"));

                                // If the interface method is virtual delegate target, the slot is virtual delegate target
                                result.Add(new CombinedDependencyListEntry(
                                    factory.DelegateTargetVirtualMethod(implMethod.GetCanonMethodTarget(CanonicalFormKind.Specific)),
                                    factory.DelegateTargetVirtualMethod(interfaceMethod.GetCanonMethodTarget(CanonicalFormKind.Specific)),
                                    "Interface slot is delegate target"));
                            }

                            // If any of the implemented interfaces have variance, calls against compatible interface methods
                            // could result in interface methods of this type being used (e.g. IEnumerable<object>.GetEnumerator()
                            // can dispatch to an implementation of IEnumerable<string>.GetEnumerator()).
                            if (isVariantInterfaceImpl)
                            {
                                MethodDesc typicalInterfaceMethod = interfaceMethod.GetTypicalMethodDefinition();

                                object implMethodUseNode = isStaticInterfaceMethod ?
                                    factory.CanonicalEntrypoint(implMethod) : factory.VirtualMethodUse(implMethod);

                                result.Add(new CombinedDependencyListEntry(implMethodUseNode, factory.VariantInterfaceMethodUse(typicalInterfaceMethod), "Interface method"));
                                result.Add(new CombinedDependencyListEntry(factory.VirtualMethodUse(interfaceMethod), factory.VariantInterfaceMethodUse(typicalInterfaceMethod), "Interface method"));
                            }

                            TypeSystemEntity origin = (implMethod.OwningType != defType) ? defType : null;
                            factory.MetadataManager.NoteOverridingMethod(interfaceMethod, implMethod, origin);

                            factory.MetadataManager.GetDependenciesForOverridingMethod(ref result, factory, interfaceMethod, implMethod);
                        }
                        else
                        {
                            // Is the implementation provided by a default interface method?
                            // If so, add a dependency on the entrypoint directly since nobody else is going to do that
                            // (interface types have an empty vtable, modulo their generic dictionary).
                            var resolution = defTypeDefinition.ResolveInterfaceMethodToDefaultImplementationOnType(interfaceMethodDefinition, out implMethod);
                            if (resolution == DefaultInterfaceMethodResolution.DefaultImplementation)
                            {
                                DefType providingInterfaceDefinitionType = (DefType)implMethod.OwningType;
                                implMethod = implMethod.InstantiateSignature(defType.Instantiation, Instantiation.Empty);

                                MethodDesc defaultIntfMethod = implMethod.GetCanonMethodTarget(CanonicalFormKind.Specific);
                                if (!isStaticInterfaceMethod && defaultIntfMethod.IsCanonicalMethod(CanonicalFormKind.Any))
                                {
                                    // Canonical instance default methods need to go through a thunk that adds the right generic context
                                    defaultIntfMethod = factory.TypeSystemContext.GetDefaultInterfaceMethodImplementationThunk(defaultIntfMethod, defType.ConvertToCanonForm(CanonicalFormKind.Specific), providingInterfaceDefinitionType, out int providingInterfaceIndex);

                                    // The above thunk will index into interface list to find the right context. Make sure to keep all interfaces prior to this one
                                    for (int i = 0; i <= providingInterfaceIndex; i++)
                                    {
                                        result.Add(new CombinedDependencyListEntry(
                                            factory.InterfaceUse(defTypeRuntimeInterfaces[i].GetTypeDefinition()),
                                            factory.VirtualMethodUse(interfaceMethod), "Interface with shared default methods folows this"));
                                    }
                                }
                                result.Add(new CombinedDependencyListEntry(factory.MethodEntrypoint(defaultIntfMethod), factory.VirtualMethodUse(interfaceMethod), "Interface method"));

                                result.Add(new CombinedDependencyListEntry(
                                    factory.AddressTakenMethodEntrypoint(defaultIntfMethod),
                                    factory.DelegateTargetVirtualMethod(interfaceMethod.GetCanonMethodTarget(CanonicalFormKind.Specific)),
                                    "Slot is delegate target"));

                                factory.MetadataManager.NoteOverridingMethod(interfaceMethod, implMethod);

                                factory.MetadataManager.GetDependenciesForOverridingMethod(ref result, factory, interfaceMethod, implMethod);
                            }
                        }
                    }
                }
            }

            factory.MetadataManager.GetConditionalDependenciesDueToEETypePresence(ref result, factory, _type);

            return result;
        }

        public static bool IsTypeNodeShareable(TypeDesc type)
        {
            return type.IsParameterizedType || type.IsFunctionPointer || type is InstantiatedType;
        }

        internal static bool MethodHasNonGenericILMethodBody(MethodDesc method)
        {
            // Generic methods have their own generic dictionaries
            if (method.HasInstantiation)
                return false;

            // Abstract methods don't have a body
            if (method.IsAbstract)
                return false;

            // PInvoke methods are not permitted on generic types,
            // but let's not crash the compilation because of that.
            if (method.IsPInvoke)
                return false;

            // NativeAOT can generate method bodies for these no matter what (worst case
            // they'll be throwing). We don't want to take the "return false" code path because
            // delegate methods fall into the runtime implemented category on NativeAOT, but we
            // just treat them like regular method bodies.
            return true;
        }

        protected override DependencyList ComputeNonRelocationBasedDependencies(NodeFactory factory)
        {
            DependencyList dependencies = new DependencyList();

            if (_type.IsInterface)
                dependencies.Add(factory.InterfaceUse(_type.GetTypeDefinition()), "Interface is used");

            // Array types that don't have generic interface methods can be created out of thin air
            // at runtime by the type loader. We should never emit non-constructed forms of these MethodTables.
            // There's similar logic for generic types, but that one is a conditional dependency conditioned
            // on the presence of the type loader template for the canonical form of the type.
            if (_type.IsArrayTypeWithoutGenericInterfaces())
            {
                IEETypeNode maximallyConstructableType = factory.MaximallyConstructableType(_type);
                if (maximallyConstructableType != this)
                {
                    dependencies.Add(maximallyConstructableType, "Type is template-loadable");
                }
            }

            if (EmitVirtualSlots)
            {
                if (!_type.IsArrayTypeWithoutGenericInterfaces())
                {
                    // Sealed vtables have relative pointers, so to minimize size, we build sealed vtables for the canonical types
                    dependencies.Add(new DependencyListEntry(factory.SealedVTable(_type.ConvertToCanonForm(CanonicalFormKind.Specific)), "Sealed Vtable"));
                }

                // Also add the un-normalized vtable slices of implemented interfaces.
                // This is important to do in the scanning phase so that the compilation phase can find
                // vtable information for things like IEnumerator<List<__Canon>>.
                foreach (TypeDesc intface in _type.RuntimeInterfaces)
                    dependencies.Add(factory.VTable(intface), "Interface vtable slice");

                // Generated type contains generic virtual methods that will get added to the GVM tables
                if ((_virtualMethodAnalysisFlags & VirtualMethodAnalysisFlags.NeedsGvmEntries) != 0)
                {
                    dependencies.Add(new DependencyListEntry(factory.TypeGVMEntries(_type.GetTypeDefinition()), "Type with generic virtual methods"));

                    TypeDesc canonicalType = _type.ConvertToCanonForm(CanonicalFormKind.Specific);
                    if (canonicalType != _type)
                        dependencies.Add(factory.ConstructedTypeSymbol(canonicalType), "Type with generic virtual methods");
                }
            }

            if (factory.CompilationModuleGroup.PresenceOfEETypeImpliesAllMethodsOnType(_type))
            {
                if (_type.IsArray || _type.IsDefType)
                {
                    // If the compilation group wants this type to be fully promoted, ensure that all non-generic methods of the
                    // type are generated.
                    // This may be done for several reasons:
                    //   - The MethodTable may be going to be COMDAT folded with other EETypes generated in a different object file
                    //     This means their generic dictionaries need to have identical contents. The only way to achieve that is
                    //     by generating the entries for all methods that contribute to the dictionary, and sorting the dictionaries.
                    //   - The generic type may be imported into another module, in which case the generic dictionary imported
                    //     must represent all of the methods, as the set of used methods cannot be known at compile time
                    //   - As a matter of policy, the type and its methods may be exported for use in another module. The policy
                    //     may wish to specify that if a type is to be placed into a shared module, all of the methods associated with
                    //     it should be also be exported.
                    foreach (var method in _type.GetClosestDefType().ConvertToCanonForm(CanonicalFormKind.Specific).GetAllMethods())
                    {
                        if (!MethodHasNonGenericILMethodBody(method))
                            continue;

                        dependencies.Add(factory.MethodEntrypoint(method.GetCanonMethodTarget(CanonicalFormKind.Specific)),
                            "Ensure all methods on type due to CompilationModuleGroup policy");
                    }
                }
            }

            if (!ConstructedEETypeNode.CreationAllowed(_type))
            {
                // If necessary MethodTable is the highest load level for this type, ask the metadata manager
                // if we have any dependencies due to presence of the EEType.
                factory.MetadataManager.GetDependenciesDueToEETypePresence(ref dependencies, factory, _type);

                // If necessary MethodTable is the highest load level, consider this a module use
                if (_type is MetadataType mdType)
                    ModuleUseBasedDependencyAlgorithm.AddDependenciesDueToModuleUse(ref dependencies, factory, mdType.Module);
            }

            if (_type.IsFunctionPointer)
                FunctionPointerMapNode.GetHashtableDependencies(ref dependencies, factory, (FunctionPointerType)_type);

            return dependencies;
        }

        protected override ObjectData GetDehydratableData(NodeFactory factory, bool relocsOnly)
        {
            ObjectDataBuilder objData = new ObjectDataBuilder(factory, relocsOnly);
            objData.RequireInitialPointerAlignment();
            objData.AddSymbol(this);

            OutputGCDesc(ref objData);
            OutputFlags(factory, ref objData, relocsOnly);
            objData.EmitInt(BaseSize);
            OutputRelatedType(factory, ref objData);

            // Number of vtable slots will be only known later. Reseve the bytes for it.
            var vtableSlotCountReservation = objData.ReserveShort();

            // Number of interfaces will only be known later. Reserve the bytes for it.
            var interfaceCountReservation = objData.ReserveShort();

            objData.EmitInt(_type.GetHashCode());

            if (EmitVirtualSlots)
            {
                // Emit VTable
                Debug.Assert(objData.CountBytes - ((ISymbolDefinitionNode)this).Offset == GetVTableOffset(objData.TargetPointerSize));
                SlotCounter virtualSlotCounter = SlotCounter.BeginCounting(ref /* readonly */ objData);
                OutputVirtualSlots(factory, ref objData, _type, _type, _type, relocsOnly);

                // Update slot count
                int numberOfVtableSlots = virtualSlotCounter.CountSlots(ref /* readonly */ objData);
                objData.EmitShort(vtableSlotCountReservation, checked((short)numberOfVtableSlots));
            }
            else
            {
                // If we're not emitting any slots, the number of slots is zero.
                objData.EmitShort(vtableSlotCountReservation, 0);
            }

            // Emit interface map
            SlotCounter interfaceSlotCounter = SlotCounter.BeginCounting(ref /* readonly */ objData);

            if (!relocsOnly)
            {
                OutputInterfaceMap(factory, ref objData);
            }

            // Update slot count
            int numberOfInterfaceSlots = interfaceSlotCounter.CountSlots(ref /* readonly */ objData);
            objData.EmitShort(interfaceCountReservation, checked((short)numberOfInterfaceSlots));

            OutputTypeManagerIndirection(factory, ref objData);
            OutputWritableData(factory, ref objData);
            OutputDispatchMap(factory, ref objData);
            OutputFinalizerMethod(factory, ref objData);
            OutputSealedVTable(factory, relocsOnly, ref objData);
            OutputGenericInstantiationDetails(factory, ref objData);
            OutputFunctionPointerParameters(factory, ref objData);

            return objData.ToObjectData();
        }

        /// <summary>
        /// Returns the offset within an MethodTable of the beginning of VTable entries
        /// </summary>
        /// <param name="pointerSize">The size of a pointer in bytes in the target architecture</param>
        public static int GetVTableOffset(int pointerSize)
        {
            return 16 + pointerSize;
        }

        protected virtual int GCDescSize => 0;

        protected virtual void OutputGCDesc(ref ObjectDataBuilder builder)
        {
            // Non-constructed EETypeNodes get no GC Desc
            Debug.Assert(GCDescSize == 0);
        }

        private void OutputFlags(NodeFactory factory, ref ObjectDataBuilder objData, bool relocsOnly)
        {
            uint flags = EETypeBuilderHelpers.ComputeFlags(_type);

            if (_type.GetTypeDefinition() == factory.TypeSystemContext.ArrayOfTEnumeratorType)
            {
                // Generic array enumerators use special variance rules recognized by the runtime
                flags |= (uint)EETypeFlags.GenericVarianceFlag;
            }

            if (factory.TypeSystemContext.IsGenericArrayInterfaceType(_type))
            {
                // Runtime casting logic relies on all interface types implemented on arrays
                // to have the variant flag set (even if all the arguments are non-variant).
                // This supports e.g. casting uint[] to ICollection<int>
                flags |= (uint)EETypeFlags.GenericVarianceFlag;
            }

            if (EmitVirtualSlots && !_type.IsArrayTypeWithoutGenericInterfaces())
            {
                SealedVTableNode sealedVTable = factory.SealedVTable(_type.ConvertToCanonForm(CanonicalFormKind.Specific));
                if (sealedVTable.BuildSealedVTableSlots(factory, relocsOnly) && sealedVTable.NumSealedVTableEntries > 0)
                    flags |= (uint)EETypeFlags.HasSealedVTableEntriesFlag;
            }

            if (MightHaveInterfaceDispatchMap(factory))
            {
                flags |= (uint)EETypeFlags.HasDispatchMap;
            }

            if (_type.IsArray || _type.IsString)
            {
                flags |= (uint)EETypeFlags.HasComponentSizeFlag;
            }

            //
            // output ComponentSize or FlagsEx
            //

            if (_type.IsArray)
            {
                TypeDesc elementType = ((ArrayType)_type).ElementType;
                int elementSize = elementType.GetElementSize().AsInt;
                // We validated that this will fit the short when the node was constructed. No need for nice messages.
                flags |= (uint)checked((ushort)elementSize);
            }
            else if (_type.IsString)
            {
                flags |= StringComponentSize.Value;
            }
            else
            {
                ushort flagsEx = EETypeBuilderHelpers.ComputeFlagsEx(_type);
                flags |= flagsEx;
            }

            objData.EmitUInt(flags);
        }

        protected virtual int BaseSize
        {
            get
            {
                return EETypeBuilderHelpers.ComputeBaseSize(_type);
            }
        }

        protected virtual ISymbolNode GetBaseTypeNode(NodeFactory factory)
        {
            return _type.BaseType != null ? factory.NecessaryTypeSymbol(_type.BaseType.NormalizeInstantiation()) : null;
        }

        protected virtual FrozenRuntimeTypeNode GetFrozenRuntimeTypeNode(NodeFactory factory)
        {
            Debug.Assert(!_type.IsCanonicalSubtype(CanonicalFormKind.Any));
            return factory.SerializedNecessaryRuntimeTypeObject(_type);
        }

        protected virtual ISymbolNode GetNonNullableValueTypeArrayElementTypeNode(NodeFactory factory)
        {
            return factory.NecessaryTypeSymbol(((ArrayType)_type).ElementType);
        }

        private ISymbolNode GetRelatedTypeNode(NodeFactory factory)
        {
            ISymbolNode relatedTypeNode = null;

            if (_type.IsParameterizedType)
            {
                var parameterType = ((ParameterizedType)_type).ParameterType;
                if (_type.IsArray && parameterType.IsValueType && !parameterType.IsNullable)
                {
                    // This might be a constructed type symbol. There are APIs on Array that allow allocating element
                    // types through runtime magic ("((Array)new NeverAllocated[1]).GetValue(0)" or IEnumerable) and we don't have
                    // visibility into that. Conservatively assume element types of constructed arrays are also constructed.
                    relatedTypeNode = GetNonNullableValueTypeArrayElementTypeNode(factory);
                }
                else
                {
                    relatedTypeNode = factory.NecessaryTypeSymbol(parameterType);
                }
            }
            else if (_type.IsFunctionPointer)
            {
                relatedTypeNode = factory.NecessaryTypeSymbol(((FunctionPointerType)_type).Signature.ReturnType);
            }
            else
            {
                TypeDesc baseType = _type.BaseType;
                if (baseType != null)
                {
                    relatedTypeNode = GetBaseTypeNode(factory);
                }
            }

            return relatedTypeNode;
        }

        protected virtual void OutputRelatedType(NodeFactory factory, ref ObjectDataBuilder objData)
        {
            ISymbolNode relatedTypeNode = GetRelatedTypeNode(factory);

            if (relatedTypeNode != null)
            {
                objData.EmitPointerReloc(relatedTypeNode);
            }
            else
            {
                objData.EmitZeroPointer();
            }
        }

        private void OutputVirtualSlots(NodeFactory factory, ref ObjectDataBuilder objData, TypeDesc implType, TypeDesc declType, TypeDesc templateType, bool relocsOnly)
        {
            Debug.Assert(EmitVirtualSlots);

            declType = declType.GetClosestDefType();
            templateType = templateType.ConvertToCanonForm(CanonicalFormKind.Specific);

            var baseType = declType.BaseType;
            if (baseType != null)
            {
                Debug.Assert(templateType.BaseType != null);
                OutputVirtualSlots(factory, ref objData, implType, baseType, templateType.BaseType, relocsOnly);
            }

            //
            // In the universal canonical types case, we could have base types in the hierarchy that are partial universal canonical types.
            // The presence of these types could cause incorrect vtable layouts, so we need to fully canonicalize them and walk the
            // hierarchy of the template type of the original input type to detect these cases.
            //
            // Exmaple: we begin with Derived<__UniversalCanon> and walk the template hierarchy:
            //
            //    class Derived<T> : Middle<T, MyStruct> { }    // -> Template is Derived<__UniversalCanon> and needs a dictionary slot
            //                                                  // -> Basetype tempalte is Middle<__UniversalCanon, MyStruct>. It's a partial
            //                                                        Universal canonical type, so we need to fully canonicalize it.
            //
            //    class Middle<T, U> : Base<U> { }              // -> Template is Middle<__UniversalCanon, __UniversalCanon> and needs a dictionary slot
            //                                                  // -> Basetype template is Base<__UniversalCanon>
            //
            //    class Base<T> { }                             // -> Template is Base<__UniversalCanon> and needs a dictionary slot.
            //
            // If we had not fully canonicalized the Middle class template, we would have ended up with Base<MyStruct>, which does not need
            // a dictionary slot, meaning we would have created a vtable layout that the runtime does not expect.
            //

            // The generic dictionary pointer occupies the first slot of each type vtable slice
            if (declType.HasGenericDictionarySlot() || templateType.HasGenericDictionarySlot())
            {
                // All generic interface types have a dictionary slot, but only some of them have an actual dictionary.
                bool isInterfaceWithAnEmptySlot = declType.IsInterface &&
                    declType.ConvertToCanonForm(CanonicalFormKind.Specific) == declType;

                // Note: Canonical type instantiations always have a generic dictionary vtable slot, but it's empty
                if (declType.IsCanonicalSubtype(CanonicalFormKind.Any)
                    || factory.LazyGenericsPolicy.UsesLazyGenerics(declType)
                    || isInterfaceWithAnEmptySlot)
                {
                    objData.EmitZeroPointer();
                }
                else
                {
                    TypeGenericDictionaryNode dictionaryNode = factory.TypeGenericDictionary(declType);
                    DictionaryLayoutNode layoutNode = dictionaryNode.GetDictionaryLayout(factory);

                    // Don't bother emitting a reloc to an empty dictionary. We'll only know whether the dictionary is
                    // empty at final object emission time, so don't ask if we're not emitting yet.
                    if (!relocsOnly && layoutNode.IsEmpty)
                        objData.EmitZeroPointer();
                    else
                        objData.EmitPointerReloc(dictionaryNode);
                }
            }

            VTableSliceNode declVTable = factory.VTable(declType);

            // It's only okay to touch the actual list of slots if we're in the final emission phase
            // or the vtable is not built lazily.
            if (relocsOnly && !declVTable.HasKnownVirtualMethodUse)
                return;

            // Interface types don't place anything else in their physical vtable.
            // Interfaces have logical slots for their methods but since they're all abstract, they would be zero.
            // We place default implementations of interface methods into the vtable of the interface-implementing
            // type, pretending there was an extra virtual slot.
            if (_type.IsInterface)
                return;

            bool isAsyncStateMachineValueType = implType.IsValueType
                && factory.TypeSystemContext.IsAsyncStateMachineType((MetadataType)implType);

            // Actual vtable slots follow
            IReadOnlyList<MethodDesc> virtualSlots = declVTable.Slots;

            for (int i = 0; i < virtualSlots.Count; i++)
            {
                MethodDesc declMethod = virtualSlots[i];

                // Object.Finalize shouldn't get a virtual slot. Finalizer is stored in an optional field
                // instead: most MethodTable don't have a finalizer, but all EETypes contain Object's vtable.
                // This lets us save a pointer (+reloc) on most EETypes.
                Debug.Assert(!declType.IsObject || declMethod.Name != "Finalize");

                // No generic virtual methods can appear in the vtable!
                Debug.Assert(!declMethod.HasInstantiation);

                // Final NewSlot methods cannot be overridden, and therefore can be placed in the sealed-vtable to reduce the size of the vtable
                // of this type and any type that inherits from it.
                if (declMethod.CanMethodBeInSealedVTable(factory) && !declType.IsArrayTypeWithoutGenericInterfaces())
                    continue;

                if (!declVTable.IsSlotUsed(declMethod))
                {
                    objData.EmitZeroPointer();
                    continue;
                }

                MethodDesc implMethod = implType.GetClosestDefType().FindVirtualFunctionTargetMethodOnObjectType(declMethod);

                bool shouldEmitImpl = !implMethod.IsAbstract;

                // We do a size optimization that removes support for built-in ValueType Equals/GetHashCode
                // Null out the vtable slot associated with built-in support to catch if it ever becomes illegal.
                // We also null out Equals/GetHashCode - that's just a marginal size/startup optimization.
                if (isAsyncStateMachineValueType)
                {
                    if ((declType.IsObject && declMethod.Name is "Equals" or "GetHashCode" && implMethod.OwningType.IsWellKnownType(WellKnownType.ValueType))
                        || (declType.IsWellKnownType(WellKnownType.ValueType) && declMethod.Name == ValueTypeGetFieldHelperMethodOverride.MetadataName))
                    {
                        shouldEmitImpl = false;
                    }
                }

                if (shouldEmitImpl)
                {
                    MethodDesc canonImplMethod = implMethod.GetCanonMethodTarget(CanonicalFormKind.Specific);

                    // If the type we're generating now is abstract, and the implementation comes from an abstract type,
                    // only use a tentative method entrypoint that can have its body replaced by a throwing stub
                    // if no "hard" reference to that entrypoint exists in the program.
                    // This helps us to eliminate method bodies for virtual methods on abstract types that are fully overridden
                    // in the children of that abstract type.
                    bool canUseTentativeEntrypoint = implType is MetadataType mdImplType && mdImplType.IsAbstract && !mdImplType.IsInterface
                        && implMethod.OwningType is MetadataType mdImplMethodType && mdImplMethodType.IsAbstract
                        && factory.CompilationModuleGroup.AllowVirtualMethodOnAbstractTypeOptimization(canonImplMethod);

                    IMethodNode implSymbol;
                    if (canUseTentativeEntrypoint)
                        implSymbol = factory.TentativeMethodEntrypoint(canonImplMethod, implMethod.OwningType.IsValueType);
                    else if (factory.DelegateTargetVirtualMethod(declMethod.GetCanonMethodTarget(CanonicalFormKind.Specific)).Marked)
                        implSymbol = factory.AddressTakenMethodEntrypoint(canonImplMethod, implMethod.OwningType.IsValueType);
                    else
                        implSymbol = factory.MethodEntrypoint(canonImplMethod, implMethod.OwningType.IsValueType);

                    objData.EmitPointerReloc(implSymbol);
                }
                else
                {
                    objData.EmitZeroPointer();
                }
            }
        }

        protected virtual IEETypeNode GetInterfaceTypeNode(NodeFactory factory, TypeDesc interfaceType)
        {
            return factory.NecessaryTypeSymbol(interfaceType.NormalizeInstantiation());
        }

        private void OutputInterfaceMap(NodeFactory factory, ref ObjectDataBuilder objData)
        {
            if (_type.IsCanonicalSubtype(CanonicalFormKind.Any))
            {
                // Canonical types (type loader templates) do not generate an interface list - we build
                // one for the loaded type at runtime dynamically from template data.
                foreach (DefType itf in _type.RuntimeInterfaces)
                {
                    // If the interface was optimized away, skip it
                    if (factory.InterfaceUse(itf.GetTypeDefinition()).Marked)
                    {
                        // Interface omitted for canonical instantiations (constructed at runtime for dynamic types from the native layout info)
                        objData.EmitZeroPointer();
                    }
                }
            }
            else
            {
                foreach (var itf in _type.RuntimeInterfaces)
                {
                    IEETypeNode interfaceTypeNode = GetInterfaceTypeNode(factory, itf);

                    // Only emit interfaces that were not optimized away.
                    if (interfaceTypeNode.Marked)
                    {
                        objData.EmitPointerReloc(interfaceTypeNode);
                    }
                }
            }
        }

        private void OutputFinalizerMethod(NodeFactory factory, ref ObjectDataBuilder objData)
        {
            if (_type.HasFinalizer)
            {
                MethodDesc finalizerMethod = _type.GetFinalizer();
                MethodDesc canonFinalizerMethod = finalizerMethod.GetCanonMethodTarget(CanonicalFormKind.Specific);
                if (factory.Target.SupportsRelativePointers)
                    objData.EmitReloc(factory.MethodEntrypoint(canonFinalizerMethod), RelocType.IMAGE_REL_BASED_RELPTR32);
                else
                    objData.EmitPointerReloc(factory.MethodEntrypoint(canonFinalizerMethod));
            }
        }

        protected void OutputTypeManagerIndirection(NodeFactory factory, ref ObjectDataBuilder objData)
        {
            if (factory.Target.SupportsRelativePointers)
                objData.EmitReloc(factory.TypeManagerIndirection, RelocType.IMAGE_REL_BASED_RELPTR32);
            else
                objData.EmitPointerReloc(factory.TypeManagerIndirection);
        }

        protected void OutputWritableData(NodeFactory factory, ref ObjectDataBuilder objData)
        {
            if (_writableDataNode != null)
            {
                if (factory.Target.SupportsRelativePointers)
                    objData.EmitReloc(_writableDataNode, RelocType.IMAGE_REL_BASED_RELPTR32);
                else
                    objData.EmitPointerReloc(_writableDataNode);
            }
            else
            {
                if (factory.Target.SupportsRelativePointers)
                    objData.EmitInt(0);
                else
                    objData.EmitZeroPointer();
            }
        }

        private void OutputSealedVTable(NodeFactory factory, bool relocsOnly, ref ObjectDataBuilder objData)
        {
            if (EmitVirtualSlots && !_type.IsArrayTypeWithoutGenericInterfaces())
            {
                // Sealed vtables have relative pointers, so to minimize size, we build sealed vtables for the canonical types
                SealedVTableNode sealedVTable = factory.SealedVTable(_type.ConvertToCanonForm(CanonicalFormKind.Specific));

                if (sealedVTable.BuildSealedVTableSlots(factory, relocsOnly) && sealedVTable.NumSealedVTableEntries > 0)
                {
                    if (factory.Target.SupportsRelativePointers)
                        objData.EmitReloc(sealedVTable, RelocType.IMAGE_REL_BASED_RELPTR32);
                    else
                        objData.EmitPointerReloc(sealedVTable);
                }
            }
        }

        protected void OutputGenericInstantiationDetails(NodeFactory factory, ref ObjectDataBuilder objData)
        {
            if (_type.HasInstantiation)
            {
                if (!_type.IsTypeDefinition)
                {
                    IEETypeNode typeDefNode = factory.MaximallyConstructableType(_type) == this ?
                        factory.ConstructedTypeSymbol(_type.GetTypeDefinition()) : factory.NecessaryTypeSymbol(_type.GetTypeDefinition());
                    if (factory.Target.SupportsRelativePointers)
                        objData.EmitReloc(typeDefNode, RelocType.IMAGE_REL_BASED_RELPTR32);
                    else
                        objData.EmitPointerReloc(typeDefNode);

                    ISymbolNode compositionNode;

                    if (this == factory.MaximallyConstructableType(_type)
                        && factory.MetadataManager.IsTypeInstantiationReflectionVisible(_type))
                    {
                        compositionNode = _type.Instantiation.Length > 1
                            ? factory.ConstructedGenericComposition(_type.Instantiation)
                            : factory.MaximallyConstructableType(_type.Instantiation[0]);
                    }
                    else
                    {
                        compositionNode = _type.Instantiation.Length > 1
                            ? factory.GenericComposition(_type.Instantiation)
                            : factory.NecessaryTypeSymbol(_type.Instantiation[0]);
                    }

                    if (factory.Target.SupportsRelativePointers)
                        objData.EmitReloc(compositionNode, RelocType.IMAGE_REL_BASED_RELPTR32);
                    else
                        objData.EmitPointerReloc(compositionNode);
                }
                else
                {
                    GenericVarianceDetails details;
                    if (_type == factory.TypeSystemContext.ArrayOfTEnumeratorType)
                    {
                        // Generic array enumerators use special variance rules recognized by the runtime
                        details = new GenericVarianceDetails(new[] { GenericVariance.ArrayCovariant });
                    }
                    else if (factory.TypeSystemContext.IsGenericArrayInterfaceType(_type))
                    {
                        // Runtime casting logic relies on all interface types implemented on arrays
                        // to have the variant flag set (even if all the arguments are non-variant).
                        // This supports e.g. casting uint[] to ICollection<int>
                        details = new GenericVarianceDetails(_type);
                    }
                    else if (_type.HasVariance)
                    {
                        details = new GenericVarianceDetails(_type);
                    }
                    else
                    {
                        details = default;
                    }

                    if (!details.IsNull)
                    {
                        ISymbolNode varianceInfoNode = factory.GenericVariance(details);
                        if (factory.Target.SupportsRelativePointers)
                            objData.EmitReloc(varianceInfoNode, RelocType.IMAGE_REL_BASED_RELPTR32);
                        else
                            objData.EmitPointerReloc(varianceInfoNode);
                    }
                }
            }
        }

        private void OutputFunctionPointerParameters(NodeFactory factory, ref ObjectDataBuilder objData)
        {
            if (_type.IsFunctionPointer)
            {
                MethodSignature sig = ((FunctionPointerType)_type).Signature;
                foreach (TypeDesc paramType in sig)
                {
                    ISymbolNode paramTypeNode = factory.NecessaryTypeSymbol(paramType);
                    if (factory.Target.SupportsRelativePointers)
                        objData.EmitReloc(paramTypeNode, RelocType.IMAGE_REL_BASED_RELPTR32);
                    else
                        objData.EmitPointerReloc(paramTypeNode);
                }
            }
        }

        private void OutputDispatchMap(NodeFactory factory, ref ObjectDataBuilder objData)
        {
            if (MightHaveInterfaceDispatchMap(factory))
            {
                ISymbolNode dispatchMap = factory.InterfaceDispatchMap(_type.ConvertToCanonForm(CanonicalFormKind.Specific));
                if (factory.Target.SupportsRelativePointers)
                    objData.EmitReloc(dispatchMap, RelocType.IMAGE_REL_BASED_RELPTR32);
                else
                    objData.EmitPointerReloc(dispatchMap);
            }
        }

        protected override void OnMarked(NodeFactory context)
        {
            Debug.Assert(_type.IsTypeDefinition || !_type.HasSameTypeDefinition(context.ArrayOfTClass), "Asking for Array<T> MethodTable");
        }

        public override int ClassCode => 1521789141;

        public override int CompareToImpl(ISortableNode other, CompilerComparer comparer)
        {
            return comparer.Compare(_type, ((EETypeNode)other)._type);
        }

        public override string ToString()
        {
            return _type.ToString();
        }

        private struct SlotCounter
        {
            private int _startBytes;

            public static SlotCounter BeginCounting(ref /* readonly */ ObjectDataBuilder builder)
                => new SlotCounter { _startBytes = builder.CountBytes };

            public int CountSlots(ref /* readonly */ ObjectDataBuilder builder)
            {
                int bytesEmitted = builder.CountBytes - _startBytes;
                Debug.Assert(bytesEmitted % builder.TargetPointerSize == 0);
                return bytesEmitted / builder.TargetPointerSize;
            }

        }

        private sealed class WritableDataNode : ObjectNode, ISymbolDefinitionNode
        {
            private readonly EETypeNode _type;

            public WritableDataNode(EETypeNode type) => _type = type;
            public override ObjectNodeSection GetSection(NodeFactory factory)
                => _type.GetFrozenRuntimeTypeNode(factory).Marked
                ? (factory.Target.IsWindows ? ObjectNodeSection.ReadOnlyDataSection : ObjectNodeSection.DataSection)
                : ObjectNodeSection.BssSection;

            public override bool StaticDependenciesAreComputed => true;
            public void AppendMangledName(NameMangler nameMangler, Utf8StringBuilder sb)
                => sb.Append("__writableData"u8).Append(nameMangler.GetMangledTypeName(_type.Type));
            public int Offset => 0;
            public override bool IsShareable => true;
            public override bool ShouldSkipEmittingObjectNode(NodeFactory factory) => _type.ShouldSkipEmittingObjectNode(factory);

            public override ObjectData GetData(NodeFactory factory, bool relocsOnly = false)
            {
                ObjectDataBuilder builder = new ObjectDataBuilder(factory, relocsOnly);

                builder.RequireInitialAlignment(WritableData.GetAlignment(factory.Target.PointerSize));
                builder.AddSymbol(this);

                // If the whole program view contains a reference to a preallocated RuntimeType
                // instance for this type, generate a reference to it.
                // Otherwise, generate as zero to save size.
                if (!relocsOnly
                    && !_type.Type.IsCanonicalSubtype(CanonicalFormKind.Any)
                    && _type.GetFrozenRuntimeTypeNode(factory) is { Marked: true } runtimeTypeObject)
                {
                    builder.EmitPointerReloc(runtimeTypeObject);
                }
                else
                {
                    builder.EmitZeroPointer();
                }

                Debug.Assert(builder.CountBytes == WritableData.GetSize(factory.Target.PointerSize));

                return builder.ToObjectData();
            }

            protected override string GetName(NodeFactory factory) => this.GetMangledName(factory.NameMangler);

            public override int ClassCode => -5647893;

            public override int CompareToImpl(ISortableNode other, CompilerComparer comparer)
                => comparer.Compare(_type, ((WritableDataNode)other)._type);
        }
    }
}
