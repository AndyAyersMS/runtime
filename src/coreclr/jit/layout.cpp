// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

#include "jitpch.h"
#include "layout.h"
#include "compiler.h"

// Keeps track of layout objects associated to class handles or block sizes. A layout is usually
// referenced by a pointer (ClassLayout*) but can also be referenced by a number (unsigned,
// FirstLayoutNum-based), when space constraints or other needs make numbers more appealing.
// Layout objects are immutable and there's always a 1:1 mapping between class handles/block sizes,
// pointers and numbers (e.g. class handle equality implies ClassLayout pointer equality).
class ClassLayoutTable
{
    // Each layout is assigned a number, starting with TYP_UNKNOWN + 1. This way one could use a single
    // unsigned value to represent the notion of type - values below TYP_UNKNOWN are var_types and values
    // above it are struct layouts.
    static constexpr unsigned FirstLayoutNum = TYP_UNKNOWN + 1;

    typedef JitHashTable<unsigned, JitSmallPrimitiveKeyFuncs<unsigned>, unsigned>               BlkLayoutIndexMap;
    typedef JitHashTable<CORINFO_CLASS_HANDLE, JitPtrKeyFuncs<CORINFO_CLASS_STRUCT_>, unsigned> ObjLayoutIndexMap;
    typedef JitHashTable<CORINFO_CLASS_HANDLE, JitPtrKeyFuncs<CORINFO_CLASS_STRUCT_>, unsigned> BoxLayoutIndexMap;

    union {
        // Up to 4 layouts can be stored "inline" and finding a layout by handle/size can be done using linear search.
        // Most methods need no more than 2 layouts.
        ClassLayout* m_layoutArray[4];
        // Otherwise a dynamic array is allocated and hashtables are used to map from handle/size to layout array index.
        struct
        {
            ClassLayout**      m_layoutLargeArray;
            BlkLayoutIndexMap* m_blkLayoutMap;
            ObjLayoutIndexMap* m_objLayoutMap;
            BoxLayoutIndexMap* m_boxLayoutMap;
        };
    };
    // The number of layout objects stored in this table.
    unsigned m_layoutCount;
    // The capacity of m_layoutLargeArray (when more than 4 layouts are stored).
    unsigned m_layoutLargeCapacity;

public:
    ClassLayoutTable() : m_layoutCount(0), m_layoutLargeCapacity(0)
    {
    }

    // Get the layout number (FirstLayoutNum-based) of the specified layout.
    unsigned GetLayoutNum(ClassLayout* layout) const
    {
        return GetLayoutIndex(layout) + FirstLayoutNum;
    }

    // Get the layout having the specified layout number (FirstLayoutNum-based)
    ClassLayout* GetLayoutByNum(unsigned num) const
    {
        assert(num >= FirstLayoutNum);
        return GetLayoutByIndex(num - FirstLayoutNum);
    }

    // Get the layout having the specified size but no class handle.
    ClassLayout* GetBlkLayout(Compiler* compiler, unsigned blockSize)
    {
        return GetLayoutByIndex(GetBlkLayoutIndex(compiler, blockSize));
    }

    // Get the number of a layout having the specified size but no class handle.
    unsigned GetBlkLayoutNum(Compiler* compiler, unsigned blockSize)
    {
        return GetBlkLayoutIndex(compiler, blockSize) + FirstLayoutNum;
    }

    // Get the layout for the specified class handle.
    ClassLayout* GetObjLayout(Compiler* compiler, CORINFO_CLASS_HANDLE classHandle, bool isBoxedValueClass)
    {
        return GetLayoutByIndex(GetObjLayoutIndex(compiler, classHandle, isBoxedValueClass));
    }

    // Get the number of a layout for the specified class handle.
    unsigned GetObjLayoutNum(Compiler* compiler, CORINFO_CLASS_HANDLE classHandle, bool isBoxedValueClass)
    {
        return GetObjLayoutIndex(compiler, classHandle, isBoxedValueClass) + FirstLayoutNum;
    }

private:
    bool HasSmallCapacity() const
    {
        return m_layoutCount <= _countof(m_layoutArray);
    }

    ClassLayout* GetLayoutByIndex(unsigned index) const
    {
        assert(index < m_layoutCount);

        if (HasSmallCapacity())
        {
            return m_layoutArray[index];
        }
        else
        {
            return m_layoutLargeArray[index];
        }
    }

    unsigned GetLayoutIndex(ClassLayout* layout) const
    {
        assert(layout != nullptr);

        if (HasSmallCapacity())
        {
            for (unsigned i = 0; i < m_layoutCount; i++)
            {
                if (m_layoutArray[i] == layout)
                {
                    return i;
                }
            }
        }
        else
        {
            unsigned index = 0;

            if ((layout->IsBlockLayout() && m_blkLayoutMap->Lookup(layout->GetSize(), &index)) ||
                (layout->IsBoxedValueClass() && m_boxLayoutMap->Lookup(layout->GetClassHandle(), &index)) ||
                m_objLayoutMap->Lookup(layout->GetClassHandle(), &index))
            {
                return index;
            }
        }

        unreached();
    }

    unsigned GetBlkLayoutIndex(Compiler* compiler, unsigned blockSize)
    {
        if (HasSmallCapacity())
        {
            for (unsigned i = 0; i < m_layoutCount; i++)
            {
                if (m_layoutArray[i]->IsBlockLayout() && (m_layoutArray[i]->GetSize() == blockSize))
                {
                    return i;
                }
            }
        }
        else
        {
            unsigned index;
            if (m_blkLayoutMap->Lookup(blockSize, &index))
            {
                return index;
            }
        }

        return AddBlkLayout(compiler, CreateBlkLayout(compiler, blockSize));
    }

    ClassLayout* CreateBlkLayout(Compiler* compiler, unsigned blockSize)
    {
        return new (compiler, CMK_ClassLayout) ClassLayout(blockSize);
    }

    unsigned AddBlkLayout(Compiler* compiler, ClassLayout* layout)
    {
        if (m_layoutCount < _countof(m_layoutArray))
        {
            m_layoutArray[m_layoutCount] = layout;
            return m_layoutCount++;
        }

        unsigned index = AddLayoutLarge(compiler, layout);
        m_blkLayoutMap->Set(layout->GetSize(), index);
        return index;
    }

    unsigned GetObjLayoutIndex(Compiler* compiler, CORINFO_CLASS_HANDLE classHandle, bool isBoxedValueClass)
    {
        assert(classHandle != NO_CLASS_HANDLE);

        if (HasSmallCapacity())
        {
            for (unsigned i = 0; i < m_layoutCount; i++)
            {
                if ((m_layoutArray[i]->GetClassHandle() == classHandle) && (isBoxedValueClass == m_layoutArray[i]->IsBoxedValueClass()))
                {
                    return i;
                }
            }
        }
        else if (isBoxedValueClass)
        {
            unsigned index;
            if (m_boxLayoutMap->Lookup(classHandle, &index))
            {
                return index;
            }
        }
        else
        {
            unsigned index;
            if (m_objLayoutMap->Lookup(classHandle, &index))
            {
                return index;
            }
        }

        return AddObjLayout(compiler, CreateObjLayout(compiler, classHandle, isBoxedValueClass));
    }

    ClassLayout* CreateObjLayout(Compiler* compiler, CORINFO_CLASS_HANDLE classHandle, bool isBoxedValueClass)
    {
        return ClassLayout::Create(compiler, classHandle, isBoxedValueClass);
    }

    unsigned AddObjLayout(Compiler* compiler, ClassLayout* layout)
    {
        if (m_layoutCount < _countof(m_layoutArray))
        {
            m_layoutArray[m_layoutCount] = layout;
            return m_layoutCount++;
        }

        unsigned index = AddLayoutLarge(compiler, layout);

        if (layout->IsBoxedValueClass())
        {
            m_boxLayoutMap->Set(layout->GetClassHandle(), index);
        }
        else
        {
            m_objLayoutMap->Set(layout->GetClassHandle(), index);
        }
        return index;
    }

    unsigned AddLayoutLarge(Compiler* compiler, ClassLayout* layout)
    {
        if (m_layoutCount >= m_layoutLargeCapacity)
        {
            CompAllocator alloc       = compiler->getAllocator(CMK_ClassLayout);
            unsigned      newCapacity = m_layoutCount * 2;
            ClassLayout** newArray    = alloc.allocate<ClassLayout*>(newCapacity);

            if (m_layoutCount <= _countof(m_layoutArray))
            {
                BlkLayoutIndexMap* blkLayoutMap = new (alloc) BlkLayoutIndexMap(alloc);
                ObjLayoutIndexMap* objLayoutMap = new (alloc) ObjLayoutIndexMap(alloc);
                BoxLayoutIndexMap* boxLayoutMap = new (alloc) BoxLayoutIndexMap(alloc);

                for (unsigned i = 0; i < m_layoutCount; i++)
                {
                    ClassLayout* l = m_layoutArray[i];
                    newArray[i]    = l;

                    if (l->IsBlockLayout())
                    {
                        blkLayoutMap->Set(l->GetSize(), i);
                    }
                    else if (l->IsBoxedValueClass())
                    {
                        boxLayoutMap->Set(l->GetClassHandle(), i);
                    }
                    else
                    {
                        objLayoutMap->Set(l->GetClassHandle(), i);
                    }
                }

                m_blkLayoutMap = blkLayoutMap;
                m_objLayoutMap = objLayoutMap;
                m_boxLayoutMap = boxLayoutMap;
            }
            else
            {
                memcpy(newArray, m_layoutLargeArray, m_layoutCount * sizeof(newArray[0]));
            }

            m_layoutLargeArray    = newArray;
            m_layoutLargeCapacity = newCapacity;
        }

        m_layoutLargeArray[m_layoutCount] = layout;
        return m_layoutCount++;
    }
};

ClassLayoutTable* Compiler::typCreateClassLayoutTable()
{
    assert(m_classLayoutTable == nullptr);

    if (compIsForInlining())
    {
        m_classLayoutTable = impInlineInfo->InlinerCompiler->m_classLayoutTable;

        if (m_classLayoutTable == nullptr)
        {
            m_classLayoutTable = new (this, CMK_ClassLayout) ClassLayoutTable();

            impInlineInfo->InlinerCompiler->m_classLayoutTable = m_classLayoutTable;
        }
    }
    else
    {
        m_classLayoutTable = new (this, CMK_ClassLayout) ClassLayoutTable();
    }

    return m_classLayoutTable;
}

ClassLayoutTable* Compiler::typGetClassLayoutTable()
{
    if (m_classLayoutTable == nullptr)
    {
        return typCreateClassLayoutTable();
    }

    return m_classLayoutTable;
}

ClassLayout* Compiler::typGetLayoutByNum(unsigned layoutNum)
{
    return typGetClassLayoutTable()->GetLayoutByNum(layoutNum);
}

unsigned Compiler::typGetLayoutNum(ClassLayout* layout)
{
    return typGetClassLayoutTable()->GetLayoutNum(layout);
}

unsigned Compiler::typGetBlkLayoutNum(unsigned blockSize)
{
    return typGetClassLayoutTable()->GetBlkLayoutNum(this, blockSize);
}

ClassLayout* Compiler::typGetBlkLayout(unsigned blockSize)
{
    return typGetClassLayoutTable()->GetBlkLayout(this, blockSize);
}

unsigned Compiler::typGetObjLayoutNum(CORINFO_CLASS_HANDLE classHandle, bool isBoxedValueClass)
{
    return typGetClassLayoutTable()->GetObjLayoutNum(this, classHandle, isBoxedValueClass);
}

ClassLayout* Compiler::typGetObjLayout(CORINFO_CLASS_HANDLE classHandle, bool isBoxedValueClass)
{
    ClassLayout* const result = typGetClassLayoutTable()->GetObjLayout(this, classHandle, isBoxedValueClass);
    assert(result->IsBoxedValueClass() == isBoxedValueClass);
    return result;
}

ClassLayout* ClassLayout::Create(Compiler* compiler, CORINFO_CLASS_HANDLE classHandle, bool isBoxedValueClass)
{
    bool     isValueClass = compiler->info.compCompHnd->isValueClass(classHandle);
    unsigned size;

    if (isValueClass)
    {
        size = compiler->info.compCompHnd->getClassSize(classHandle);

        if (isBoxedValueClass) 
        {
            size += TARGET_POINTER_SIZE;
        }
    }
    else
    {
        assert(!isBoxedValueClass);
        size = compiler->info.compCompHnd->getHeapClassSize(classHandle);
    }

    INDEBUG(const char* className = compiler->info.compCompHnd->getClassName(classHandle);)

    ClassLayout* layout =
        new (compiler, CMK_ClassLayout) ClassLayout(classHandle, isValueClass, isBoxedValueClass, size DEBUGARG(className));
    layout->InitializeGCPtrs(compiler);
    return layout;
}

void ClassLayout::InitializeGCPtrs(Compiler* compiler)
{
    assert(!m_gcPtrsInitialized);
    assert(!IsBlockLayout());

    if (m_size < TARGET_POINTER_SIZE)
    {
        assert(GetSlotCount() == 1);
        assert(m_gcPtrCount == 0);

        m_gcPtrsArray[0] = TYPE_GC_NONE;
    }
    else
    {
        BYTE* gcPtrs;

        if (GetSlotCount() > sizeof(m_gcPtrsArray))
        {
            gcPtrs = m_gcPtrs = new (compiler, CMK_ClassLayout) BYTE[GetSlotCount()];
        }
        else
        {
            gcPtrs = m_gcPtrsArray;
        }

        // The gcPtrs array will have the right size for boxed value classes, but all
        // entries will be shifted down one slot to match the unboxed rep.
        //
        unsigned gcPtrCount = compiler->info.compCompHnd->getClassGClayout(m_classHandle, gcPtrs);

        assert((gcPtrCount == 0) || ((compiler->info.compCompHnd->getClassAttribs(m_classHandle) &
                                      (CORINFO_FLG_CONTAINS_GC_PTR | CORINFO_FLG_CONTAINS_STACK_PTR)) != 0));

        assert(gcPtrCount < (1 << 24));

        m_gcPtrCount = gcPtrCount;
    }

    INDEBUG(m_gcPtrsInitialized = true;)
}

//------------------------------------------------------------------------
// AreCompatible: check if 2 layouts are the same for copying.
//
// Arguments:
//    layout1 - the first layout;
//    layout2 - the second layout.
//
// Return value:
//    true if compatible, false otherwise.
//
// Notes:
//    Layouts are called compatible if they are equal or if
//    they have the same size and the same GC slots.
//
// static
bool ClassLayout::AreCompatible(const ClassLayout* layout1, const ClassLayout* layout2)
{
    assert((layout1 != nullptr) && (layout2 != nullptr));
    CORINFO_CLASS_HANDLE clsHnd1 = layout1->GetClassHandle();
    CORINFO_CLASS_HANDLE clsHnd2 = layout2->GetClassHandle();

    if ((clsHnd1 != NO_CLASS_HANDLE) && (clsHnd1 == clsHnd2))
    {
        return true;
    }

    if (layout1->IsBoxedValueClass() != layout2->IsBoxedValueClass())
    {
        return false;
    }

    if (layout1->GetSize() != layout2->GetSize())
    {
        return false;
    }

    if (layout1->HasGCPtr() != layout2->HasGCPtr())
    {
        return false;
    }

    if (!layout1->HasGCPtr() && !layout2->HasGCPtr())
    {
        return true;
    }

    assert(clsHnd1 != NO_CLASS_HANDLE);
    assert(clsHnd2 != NO_CLASS_HANDLE);
    assert(layout1->HasGCPtr() && layout2->HasGCPtr());

    if (layout1->GetGCPtrCount() != layout2->GetGCPtrCount())
    {
        return false;
    }

    assert(layout1->GetSlotCount() == layout2->GetSlotCount());
    unsigned slotsCount = layout1->GetSlotCount();

    for (unsigned i = 0; i < slotsCount; ++i)
    {
        if (layout1->GetGCPtrType(i) != layout2->GetGCPtrType(i))
        {
            return false;
        }
    }
    return true;
}
