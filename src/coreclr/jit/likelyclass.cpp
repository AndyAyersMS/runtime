// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

/*XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XX                                                                           XX
XX                           Likely Class Processing                         XX
XX                                                                           XX
XX   Parses Pgo data to find the most likely class in use at a given         XX
XX   IL offset in a method. Used by both the JIT, and by crossgen            XX
XX                                                                           XX
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
*/

#include "jitpch.h"
#ifdef _MSC_VER
#pragma hdrstop
#endif

#include <algorithm.h>

#ifndef DLLEXPORT
#define DLLEXPORT
#endif // !DLLEXPORT

// Maximum number of distinct (de-duplicated) entries we track when
// summarizing a histogram. The base HandleHistogram has SIZE=32; the
// caller-sensitive variant has SIZE=128 pairs, so we size for that.
//
#define LIKELYCLASS_MAX_DISTINCT 128

// Data item in class profile histogram
//
struct LikelyClassMethodHistogramEntry
{
    // Handle that was observed at runtime
    INT_PTR m_handle; // This may be an "unknown handle"
    // Number of observations in the table
    unsigned m_count;
};

// Summarizes a ClassProfile table by forming a Histogram
//
struct LikelyClassMethodHistogram
{
    LikelyClassMethodHistogram(INT_PTR* histogramEntries, unsigned entryCount, bool int32Data = false);

    // Construct a histogram from a context-sensitive (interleaved
    // Handle, Caller) table, optionally filtering to only pairs whose
    // Caller matches callerMethodHandle. Pass 0 to disable filtering.
    LikelyClassMethodHistogram(INT_PTR* histogramEntries, unsigned entryCount, INT_PTR callerMethodHandle, bool int32Data);

    template <typename ElemType>
    void LikelyClassMethodHistogramInner(ElemType* histogramEntries, unsigned entryCount);

    template <typename ElemType>
    void LikelyClassMethodHistogramWithCallerInner(ElemType* histogramEntries, unsigned entryCount, INT_PTR callerMethodHandle);

    // Sum of counts from all entries in the histogram. This includes "unknown" entries which are not captured in
    // m_histogram
    unsigned m_totalCount;
    // Rough guess at count of unknown handles
    unsigned m_unknownHandles;
    // Histogram entries, in no particular order.
    LikelyClassMethodHistogramEntry m_histogram[LIKELYCLASS_MAX_DISTINCT];
    UINT32                          countHistogramElements = 0;

    LikelyClassMethodHistogramEntry HistogramEntryAt(unsigned index)
    {
        return m_histogram[index];
    }
};

//------------------------------------------------------------------------
// LikelyClassMethodHistogram::LikelyClassMethodHistogram: construct a new histogram
//
// Arguments:
//    histogramEntries - pointer to the table portion of a ClassProfile* object (see corjit.h)
//    entryCount - number of entries in the table to examine
//    int32Data - true if table entries are 32 bits
//
LikelyClassMethodHistogram::LikelyClassMethodHistogram(INT_PTR* histogramEntries, unsigned entryCount, bool int32Data)
{
    if (int32Data)
    {
        LikelyClassMethodHistogramInner<int>((int*)histogramEntries, entryCount);
    }
    else
    {
        LikelyClassMethodHistogramInner<INT_PTR>(histogramEntries, entryCount);
    }
}

template <typename ElemType>
void LikelyClassMethodHistogram::LikelyClassMethodHistogramInner(ElemType* histogramEntries, unsigned entryCount)
{
    m_unknownHandles               = 0;
    m_totalCount                   = 0;
    uint32_t unknownTypeHandleMask = 0;

    for (unsigned k = 0; k < entryCount; k++)
    {
        if (histogramEntries[k] == 0)
        {
            continue;
        }

        m_totalCount++;
        INT_PTR currentEntry = (INT_PTR)histogramEntries[k];

        bool     found = false;
        unsigned h     = 0;
        for (; h < countHistogramElements; h++)
        {
            if (m_histogram[h].m_handle == currentEntry)
            {
                m_histogram[h].m_count++;
                found = true;
                break;
            }
        }

        if (!found)
        {
            if (countHistogramElements >= ArrLen(m_histogram))
            {
                continue;
            }
            LikelyClassMethodHistogramEntry newEntry;
            newEntry.m_handle                     = currentEntry;
            newEntry.m_count                      = 1;
            m_histogram[countHistogramElements++] = newEntry;
        }
    }
}

//------------------------------------------------------------------------
// LikelyClassMethodHistogram: construct from an interleaved (Handle, Caller)
// table, optionally filtering by caller method handle.
//
// Arguments:
//    histogramEntries  - pointer to the interleaved table from a
//                        HandleHistogramWithCaller* object (see corjit.h).
//                        Each pair is (handle, caller).
//    entryCount        - total number of slots in the table (= 2 * pair count).
//    callerMethodHandle - if non-zero, only pairs whose Caller slot equals
//                         this value are included; if zero, all pairs are
//                         included (Caller ignored).
//    int32Data         - true if table entries are 32 bits.
//
LikelyClassMethodHistogram::LikelyClassMethodHistogram(INT_PTR* histogramEntries, unsigned entryCount, INT_PTR callerMethodHandle, bool int32Data)
{
    if (int32Data)
    {
        LikelyClassMethodHistogramWithCallerInner<int>((int*)histogramEntries, entryCount, callerMethodHandle);
    }
    else
    {
        LikelyClassMethodHistogramWithCallerInner<INT_PTR>(histogramEntries, entryCount, callerMethodHandle);
    }
}

template <typename ElemType>
void LikelyClassMethodHistogram::LikelyClassMethodHistogramWithCallerInner(ElemType* histogramEntries, unsigned entryCount, INT_PTR callerMethodHandle)
{
    m_unknownHandles = 0;
    m_totalCount     = 0;

    // The table is laid out as pairs: even index = handle, odd index = caller.
    // Iterate in steps of 2.
    for (unsigned k = 0; (k + 1) < entryCount; k += 2)
    {
        ElemType handleEntry = histogramEntries[k];
        ElemType callerEntry = histogramEntries[k + 1];

        if (handleEntry == 0)
        {
            continue;
        }

        // If a caller filter is supplied, skip pairs whose caller does
        // not match. An unresolved/unknown caller (caller slot is unknown
        // handle or zero) will not match a real method handle.
        if (callerMethodHandle != 0 && (INT_PTR)callerEntry != callerMethodHandle)
        {
            continue;
        }

        m_totalCount++;
        INT_PTR currentEntry = (INT_PTR)handleEntry;

        bool     found = false;
        unsigned h     = 0;
        for (; h < countHistogramElements; h++)
        {
            if (m_histogram[h].m_handle == currentEntry)
            {
                m_histogram[h].m_count++;
                found = true;
                break;
            }
        }

        if (!found)
        {
            if (countHistogramElements >= ArrLen(m_histogram))
            {
                continue;
            }
            LikelyClassMethodHistogramEntry newEntry;
            newEntry.m_handle                     = currentEntry;
            newEntry.m_count                      = 1;
            m_histogram[countHistogramElements++] = newEntry;
        }
    }
}

//------------------------------------------------------------------------
// getLikelyClassesOrMethods:
//   Find class/method profile data for an IL offset, and return the most
//   likely classes/methods.
//
//   This is a common entrypoint for getLikelyClasses and getLikelyMethods.
//   See documentation for those for more information.
//
//   When 'callerMethodHandle' is non-zero AND the schema contains a
//   context-sensitive class histogram (HandleHistogramTypesWithCaller), only
//   entries whose caller slot matches will be considered. The non-context-
//   sensitive kinds (HandleHistogramTypes / HandleHistogramMethods) ignore
//   the filter (legacy behavior).
//
static unsigned getLikelyClassesOrMethods(LikelyClassMethodRecord*               pLikelyEntries,
                                          UINT32                                 maxLikelyClasses,
                                          ICorJitInfo::PgoInstrumentationSchema* schema,
                                          UINT32                                 countSchemaItems,
                                          BYTE*                                  pInstrumentationData,
                                          int32_t                                ilOffset,
                                          bool                                   types,
                                          INT_PTR                                callerMethodHandle = 0)
{
    if (maxLikelyClasses == 0)
    {
        return 0;
    }

    ICorJitInfo::PgoInstrumentationKind histogramKind =
        types ? ICorJitInfo::PgoInstrumentationKind::HandleHistogramTypes
              : ICorJitInfo::PgoInstrumentationKind::HandleHistogramMethods;
    ICorJitInfo::PgoInstrumentationKind compressedKind = types ? ICorJitInfo::PgoInstrumentationKind::GetLikelyClass
                                                               : ICorJitInfo::PgoInstrumentationKind::GetLikelyMethod;

    memset(pLikelyEntries, 0, maxLikelyClasses * sizeof(*pLikelyEntries));

    if (schema == nullptr)
    {
        return 0;
    }

    for (COUNT_T i = 0; i < countSchemaItems; i++)
    {
        if (schema[i].ILOffset != ilOffset)
            continue;

        if ((schema[i].InstrumentationKind == compressedKind) && (schema[i].Count == 1))
        {
            intptr_t result = *(intptr_t*)(pInstrumentationData + schema[i].Offset);
            if (ICorJitInfo::IsUnknownHandle(result))
            {
                return 0;
            }
            assert(result != 0); // we don't expect zero in GetLikelyClass/GetLikelyMethod
            pLikelyEntries[0].likelihood = (UINT32)(schema[i].Other & 0xFF);
            pLikelyEntries[0].handle     = result;
            return 1;
        }

        const bool isHistogramCount =
            (schema[i].InstrumentationKind == ICorJitInfo::PgoInstrumentationKind::HandleHistogramIntCount) ||
            (schema[i].InstrumentationKind == ICorJitInfo::PgoInstrumentationKind::HandleHistogramLongCount);

        // Context-sensitive class histogram (only meaningful when types==true,
        // since the method-profile path is not yet caller-sensitive).
        const bool isWithCallerHistogramCount =
            types &&
            ((schema[i].InstrumentationKind == ICorJitInfo::PgoInstrumentationKind::HandleHistogramWithCallerIntCount) ||
             (schema[i].InstrumentationKind == ICorJitInfo::PgoInstrumentationKind::HandleHistogramWithCallerLongCount));

        if (isWithCallerHistogramCount && (schema[i].Count == 1) && ((i + 1) < countSchemaItems) &&
            (schema[i + 1].InstrumentationKind == ICorJitInfo::PgoInstrumentationKind::HandleHistogramTypesWithCaller))
        {
            const bool isInt32 = schema[i].InstrumentationKind ==
                                 ICorJitInfo::PgoInstrumentationKind::HandleHistogramWithCallerIntCount;
            LikelyClassMethodHistogram h((INT_PTR*)(pInstrumentationData + schema[i + 1].Offset),
                                         schema[i + 1].Count, callerMethodHandle, isInt32);

            // Fall through to the common formatting below by reusing the
            // existing histogram-to-LikelyEntries lowering code.
            // We do that by jumping into a small inline block to format the
            // results from h.
            //
            // (Implementation below is duplicated from the non-WithCaller path;
            //  could be extracted but kept inline for clarity.)

            if (h.countHistogramElements == 0)
            {
                // No matching entries (or no entries at all).
                return 0;
            }

            LikelyClassMethodHistogramEntry sortedEntries[LIKELYCLASS_MAX_DISTINCT];
            unsigned knownHandles           = 0;
            bool     containsUnknownHandles = false;
            for (unsigned m = 0; m < h.countHistogramElements; m++)
            {
                LikelyClassMethodHistogramEntry const hist = h.HistogramEntryAt(m);
                if (!ICorJitInfo::IsUnknownHandle(hist.m_handle))
                {
                    sortedEntries[knownHandles++] = hist;
                }
                else
                {
                    containsUnknownHandles = true;
                }
            }

            if (knownHandles == 0)
            {
                return 0;
            }

            jitstd::sort(sortedEntries, sortedEntries + knownHandles,
                         [](const LikelyClassMethodHistogramEntry& h1,
                            const LikelyClassMethodHistogramEntry& h2) -> bool {
                return h1.m_count > h2.m_count;
            });

            const UINT32 numberOfClasses = min(knownHandles, maxLikelyClasses);

            UINT32 totalLikelihood = 0;
            for (size_t hIdx = 0; hIdx < numberOfClasses; hIdx++)
            {
                LikelyClassMethodHistogramEntry const hc = sortedEntries[hIdx];
                pLikelyEntries[hIdx].handle              = hc.m_handle;
                pLikelyEntries[hIdx].likelihood          = hc.m_count * 100 / h.m_totalCount;
                totalLikelihood += pLikelyEntries[hIdx].likelihood;
            }

            assert(totalLikelihood <= 100);

            if (!containsUnknownHandles)
            {
                assert(numberOfClasses > 0);
                assert(totalLikelihood > 0);
                pLikelyEntries[0].likelihood += 100 - totalLikelihood;
                assert(pLikelyEntries[0].likelihood <= 100);
            }

            return numberOfClasses;
        }

        if (isHistogramCount && (schema[i].Count == 1) && ((i + 1) < countSchemaItems) &&
            (schema[i + 1].InstrumentationKind == histogramKind))
        {
            // Form a histogram
            //
            LikelyClassMethodHistogram h((INT_PTR*)(pInstrumentationData + schema[i + 1].Offset), schema[i + 1].Count);

            // Use histogram count as number of classes estimate
            // Report back what we've learned
            // (perhaps, use count to augment likelihood?)
            //
            switch (h.countHistogramElements)
            {
                case 0:
                    return 0;

                case 1:
                {
                    LikelyClassMethodHistogramEntry const hist0 = h.HistogramEntryAt(0);
                    // Fast path for monomorphic cases
                    if (ICorJitInfo::IsUnknownHandle(hist0.m_handle))
                    {
                        return 0;
                    }
                    pLikelyEntries[0].likelihood = 100;
                    pLikelyEntries[0].handle     = hist0.m_handle;
                    return 1;
                }

                case 2:
                {
                    // Fast path for two classes
                    LikelyClassMethodHistogramEntry const hist0 = h.HistogramEntryAt(0);
                    LikelyClassMethodHistogramEntry const hist1 = h.HistogramEntryAt(1);
                    if ((hist0.m_count >= hist1.m_count) && !ICorJitInfo::IsUnknownHandle(hist0.m_handle))
                    {
                        pLikelyEntries[0].likelihood = (100 * hist0.m_count) / h.m_totalCount;
                        pLikelyEntries[0].handle     = hist0.m_handle;

                        if ((maxLikelyClasses > 1) && !ICorJitInfo::IsUnknownHandle(hist1.m_handle))
                        {
                            pLikelyEntries[1].likelihood = (100 * hist1.m_count) / h.m_totalCount;
                            pLikelyEntries[1].handle     = hist1.m_handle;
                            return 2;
                        }
                        return 1;
                    }

                    if (!ICorJitInfo::IsUnknownHandle(hist1.m_handle))
                    {
                        pLikelyEntries[0].likelihood = (100 * hist1.m_count) / h.m_totalCount;
                        pLikelyEntries[0].handle     = hist1.m_handle;

                        if ((maxLikelyClasses > 1) && !ICorJitInfo::IsUnknownHandle(hist0.m_handle))
                        {
                            pLikelyEntries[1].likelihood = (100 * hist0.m_count) / h.m_totalCount;
                            pLikelyEntries[1].handle     = hist0.m_handle;
                            return 2;
                        }
                        return 1;
                    }
                    return 0;
                }

                default:
                {
                    LikelyClassMethodHistogramEntry sortedEntries[LIKELYCLASS_MAX_DISTINCT];

                    // Since this method can be invoked without a jit instance we can't use any existing allocators
                    unsigned knownHandles           = 0;
                    unsigned containsUnknownHandles = false;
                    for (unsigned m = 0; m < h.countHistogramElements; m++)
                    {
                        LikelyClassMethodHistogramEntry const hist = h.HistogramEntryAt(m);
                        if (!ICorJitInfo::IsUnknownHandle(hist.m_handle))
                        {
                            sortedEntries[knownHandles++] = hist;
                        }
                        else
                        {
                            containsUnknownHandles = true;
                        }
                    }

                    if (knownHandles == 0)
                    {
                        // We don't have known handles
                        return 0;
                    }

                    // sort by m_count (descending)
                    jitstd::sort(sortedEntries, sortedEntries + knownHandles,
                                 [](const LikelyClassMethodHistogramEntry& h1,
                                    const LikelyClassMethodHistogramEntry& h2) -> bool {
                        return h1.m_count > h2.m_count;
                    });

                    const UINT32 numberOfClasses = min(knownHandles, maxLikelyClasses);

                    UINT32 totalLikelihood = 0;
                    for (size_t hIdx = 0; hIdx < numberOfClasses; hIdx++)
                    {
                        LikelyClassMethodHistogramEntry const hc = sortedEntries[hIdx];
                        pLikelyEntries[hIdx].handle              = hc.m_handle;
                        pLikelyEntries[hIdx].likelihood          = hc.m_count * 100 / h.m_totalCount;
                        totalLikelihood += pLikelyEntries[hIdx].likelihood;
                    }

                    assert(totalLikelihood <= 100);

                    // Distribute the rounding error and just apply it to the first entry.
                    // Assume that there is no error If we have unknown handles.
                    if (!containsUnknownHandles)
                    {
                        assert(numberOfClasses > 0);
                        assert(totalLikelihood > 0);
                        pLikelyEntries[0].likelihood += 100 - totalLikelihood;
                        assert(pLikelyEntries[0].likelihood <= 100);
                    }

                    return numberOfClasses;
                }
            }
        }
    }

    // Failed to find histogram data for this method
    //
    return 0;
}

//------------------------------------------------------------------------
// getLikelyClasses: find class profile data for an IL offset, and return the most likely classes
//
// Arguments:
//    pLikelyClasses - [OUT] array of likely classes sorted by likelihood (descending). It must be
//                     at least of 'maxLikelyClasses' (next argument) length.
//                     The array consists of pairs "clsHandle - likelihood" ordered by likelihood
//                     (descending) where likelihood can be any value in [0..100] range. clsHandle
//                     is never null for [0..<return value of this function>) range, Items in
//                     [<return value of this function>..maxLikelyClasses) are zeroed if the number
//                     of classes seen is less than maxLikelyClasses provided.
//    maxLikelyClasses - limit for likely classes to output
//    schema - profile schema
//    countSchemaItems - number of items in the schema
//    pInstrumentationData - associated data
//    ilOffset - il offset of the callvirt
//
// Returns:
//    Estimated number of classes seen at runtime
//
// Notes:
//    A "monomorphic" call site will return likelihood 100 and number of entries = 1.
//
//   This is used by the devirtualization logic below, and by crossgen2 when producing
//   the R2R image (to reduce the sizecost of carrying the type histogram)
//
//   This code can runs without a jit instance present, so JITDUMP and related
//   cannot be used.
//
extern "C" DLLEXPORT UINT32 WINAPI getLikelyClasses(LikelyClassMethodRecord*               pLikelyClasses,
                                                    UINT32                                 maxLikelyClasses,
                                                    ICorJitInfo::PgoInstrumentationSchema* schema,
                                                    UINT32                                 countSchemaItems,
                                                    BYTE*                                  pInstrumentationData,
                                                    int32_t                                ilOffset,
                                                    INT_PTR                                callerMethodHandle)
{
    return getLikelyClassesOrMethods(pLikelyClasses, maxLikelyClasses, schema, countSchemaItems, pInstrumentationData,
                                     ilOffset, true, callerMethodHandle);
}

//------------------------------------------------------------------------
// getLikelyMethods: find method profile data for an IL offset, and return the most likely methods
//
// See documentation on getLikelyClasses above.
//
extern "C" DLLEXPORT UINT32 WINAPI getLikelyMethods(LikelyClassMethodRecord*               pLikelyMethods,
                                                    UINT32                                 maxLikelyMethods,
                                                    ICorJitInfo::PgoInstrumentationSchema* schema,
                                                    UINT32                                 countSchemaItems,
                                                    BYTE*                                  pInstrumentationData,
                                                    int32_t                                ilOffset)
{
    return getLikelyClassesOrMethods(pLikelyMethods, maxLikelyMethods, schema, countSchemaItems, pInstrumentationData,
                                     ilOffset, false);
}

//------------------------------------------------------------------------
// getLikelyValues: find a value profile data for an IL offset
//
// Arguments:
//    pLikelyValues     - [OUT] array of likely values sorted by likelihood (descending). It must be
//                           at least of 'maxLikelyValues' (next argument) length.
//                           The array consists of pairs "value - likelihood" ordered by likelihood
//                           (descending) where likelihood can be any value in [0..100] range.
//    maxLikelyValues      - limit for likely classes to output
//    schema               - profile schema
//    countSchemaItems     - number of items in the schema
//    pInstrumentationData - associated data
//    ilOffset             - il offset of the node of interest
//
// Returns:
//    Estimated number of different constants seen at runtime
//
extern "C" DLLEXPORT UINT32 WINAPI getLikelyValues(LikelyValueRecord*                     pLikelyValues,
                                                   UINT32                                 maxLikelyValues,
                                                   ICorJitInfo::PgoInstrumentationSchema* schema,
                                                   UINT32                                 countSchemaItems,
                                                   BYTE*                                  pInstrumentationData,
                                                   int32_t                                ilOffset)
{
    if ((maxLikelyValues == 0) || (schema == nullptr))
    {
        return 0;
    }

    memset(pLikelyValues, 0, maxLikelyValues * sizeof(*pLikelyValues));

    for (COUNT_T i = 0; i < countSchemaItems; i++)
    {
        if (schema[i].ILOffset != ilOffset)
            continue;

        // We currently re-use existing infrastructure for type handles for simplicity.
        //
        const bool isIntHistogramCount =
            (schema[i].InstrumentationKind == ICorJitInfo::PgoInstrumentationKind::ValueHistogramIntCount);
        const bool isLongHistogramCount =
            (schema[i].InstrumentationKind == ICorJitInfo::PgoInstrumentationKind::ValueHistogramLongCount);
        const bool isHistogramCount = isIntHistogramCount || isLongHistogramCount;

        if (isHistogramCount && (schema[i].Count == 1) && ((i + 1) < countSchemaItems) &&
            (schema[i + 1].InstrumentationKind == ICorJitInfo::PgoInstrumentationKind::ValueHistogram))
        {
            LikelyClassMethodHistogram h((INT_PTR*)(pInstrumentationData + schema[i + 1].Offset), schema[i + 1].Count,
                                         isIntHistogramCount);
            LikelyClassMethodHistogramEntry sortedEntries[LIKELYCLASS_MAX_DISTINCT];

            if (h.countHistogramElements == 0)
            {
                return 0;
            }

            for (unsigned hi = 0; hi < h.countHistogramElements; hi++)
            {
                LikelyClassMethodHistogramEntry const hist = h.HistogramEntryAt(hi);
                sortedEntries[hi]                          = hist;
            }

            // sort by m_count (descending)
            jitstd::sort(sortedEntries, sortedEntries + h.countHistogramElements,
                         [](const LikelyClassMethodHistogramEntry& h1,
                            const LikelyClassMethodHistogramEntry& h2) -> bool {
                return h1.m_count > h2.m_count;
            });

            const UINT32 numberOfLikelyConst = min(h.countHistogramElements, maxLikelyValues);

            UINT32 totalLikelihood = 0;
            for (size_t hIdx = 0; hIdx < numberOfLikelyConst; hIdx++)
            {
                LikelyClassMethodHistogramEntry const hc = sortedEntries[hIdx];
                pLikelyValues[hIdx].value                = hc.m_handle;
                pLikelyValues[hIdx].likelihood           = hc.m_count * 100 / h.m_totalCount;
                totalLikelihood += pLikelyValues[hIdx].likelihood;
            }

            assert(totalLikelihood <= 100);

            // Distribute the rounding error and just apply it to the first entry.
            assert(numberOfLikelyConst > 0);
            assert(totalLikelihood > 0);
            pLikelyValues[0].likelihood += 100 - totalLikelihood;
            assert(pLikelyValues[0].likelihood <= 100);
            return numberOfLikelyConst;
        }
    }
    return 0;
}
