// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

#include "common.h"
#include "log.h"
#include "pgo.h"

#ifdef FEATURE_PGO

ICorJitInfo::BlockCounts* PgoManager::s_PgoData;
unsigned                  PgoManager::s_PgoIndex;
const char* const         PgoManager::s_FileHeaderString  = "*** START PGO Data, max index = %u ***\n";
const char* const         PgoManager::s_FileTrailerString = "*** END PGO Data ***\n";
const char* const         PgoManager::s_MethodHeaderString = "@@@ token 0x%08X hash 0x%08X ilSize 0x%08X records 0x%08X index %u\n";
const char* const         PgoManager::s_RecordString = "ilOffs %u count %u\n";

void PgoManager::Initialize()
{
    LIMITED_METHOD_CONTRACT;

    // If any PGO mode is active, allocate the slab
    if ((CLRConfig::GetConfigValue(CLRConfig::INTERNAL_ReadPGOData) > 0) ||
        (CLRConfig::GetConfigValue(CLRConfig::INTERNAL_WritePGOData) > 0) ||
        (CLRConfig::GetConfigValue(CLRConfig::INTERNAL_TieredPGO) > 0))
    {
        s_PgoData = new ICorJitInfo::BlockCounts[BUFFER_SIZE];
        s_PgoIndex = 0;
    }

    // If we're reading in counts, do that now
    ReadPgoData();
}

void PgoManager::Shutdown()
{
    WritePgoData();
}

void PgoManager::WritePgoData()
{
    if (CLRConfig::GetConfigValue(CLRConfig::INTERNAL_WritePGOData) == 0)
    {
        return;
    }

    if (s_PgoData == NULL)
    {
        return;
    }

    CLRConfigStringHolder fileName(CLRConfig::GetConfigValue(CLRConfig::INTERNAL_PGODataPath));

    if (fileName == NULL)
    {
        return;
    }

    FILE* const pgoDataFile = _wfopen(fileName, W("w"));

    if (pgoDataFile == NULL)
    {
        return;
    }

    fprintf(pgoDataFile, s_FileHeaderString, s_PgoIndex);
    unsigned       index    = 0;
    const unsigned maxIndex = s_PgoIndex;

    while (index < maxIndex)
    {
        const Header* const header = (Header*)&s_PgoData[index];

        if ((header->recordCount < MIN_RECORD_COUNT) || (header->recordCount > MAX_RECORD_COUNT))
        {
            fprintf(pgoDataFile, "Unreasonable record count %u at index %u\n", header->recordCount, index);
            break;
        }

        fprintf(pgoDataFile, s_MethodHeaderString, header->token, header->hash, header->ilSize, header->recordCount, index);

        index += 2;

        ICorJitInfo::BlockCounts* records     = &s_PgoData[index];
        unsigned                  recordCount = header->recordCount - 2;
        unsigned                  lastOffset  = 0;
        for (unsigned i = 0; i < recordCount; i++)
        {
            const unsigned thisOffset = records[i].ILOffset;
            assert((thisOffset > lastOffset) || (lastOffset == 0));
            lastOffset = thisOffset;
            fprintf(pgoDataFile, s_RecordString, records[i].ILOffset, records[i].ExecutionCount);
        }

        index += recordCount;
    }

    fprintf(pgoDataFile, s_FileTrailerString);
    fclose(pgoDataFile);
}

void PgoManager::ReadPgoData()
{
    // Skip, if we're not reading, or we're writing profile data, or doing tiered pgo
    //
    if ((CLRConfig::GetConfigValue(CLRConfig::INTERNAL_WritePGOData) > 0) ||
        (CLRConfig::GetConfigValue(CLRConfig::INTERNAL_TieredPGO) > 0) ||
        (CLRConfig::GetConfigValue(CLRConfig::INTERNAL_ReadPGOData) == 0))
    {
        return;
    }

    // PGO data slab should already be set up, if not, just bail
    //
    if (s_PgoData == NULL)
    {
        return;
    }

    CLRConfigStringHolder fileName(CLRConfig::GetConfigValue(CLRConfig::INTERNAL_PGODataPath));

    if (fileName == NULL)
    {
        return;
    }

    FILE* const pgoDataFile = _wfopen(fileName, W("r"));

    if (pgoDataFile == NULL)
    {
        return;
    }

    char     buffer[256];
    unsigned maxIndex = 0;

    // Header must be first line
    //
    if (fgets(buffer, sizeof(buffer), pgoDataFile) == nullptr)
    {
        return;
    }

    if (sscanf_s(buffer, s_FileHeaderString, &maxIndex) != 1)
    {
        return;
    }

    // Sanity check data will fit into the slab
    //
    if ((maxIndex == 0) || (maxIndex >= MAX_RECORD_COUNT))
    {
        return;
    }

    // Fill in the data
    //
    unsigned index   = 0;
    unsigned methods = 0;
    unsigned probes = 0;

    bool failed = false;
    while (!failed)
    {
        if (fgets(buffer, sizeof(buffer), pgoDataFile) == nullptr)
        {
            break;
        }

        // Find the next method entry line
        //
        unsigned recordCount = 0;
        unsigned token       = 0;
        unsigned hash        = 0;
        unsigned ilSize      = 0;
        unsigned rIndex      = 0;

        if (sscanf_s(buffer, s_MethodHeaderString, &token, &hash, &ilSize, &recordCount, &rIndex) != 5)
        {
            continue;
        }

        assert(index == rIndex);
        methods++;

        // If there's not enough room left, bail
        if ((index + recordCount) > maxIndex)
        {
            failed = true;
            break;
        }

        Header* const header = (Header*)&s_PgoData[index];

        header->recordCount = recordCount;
        header->token       = token;
        header->hash        = hash;
        header->ilSize      = ilSize;

        // Sanity check
        //
        if ((recordCount < MIN_RECORD_COUNT) || (recordCount > MAX_RECORD_COUNT))
        {
            failed = true;
            break;
        }

        index += 2;

        // Read il data
        //
        for (unsigned i = 0; i < recordCount - 2; i++)
        {
            if (fgets(buffer, sizeof(buffer), pgoDataFile) == nullptr)
            {
                failed = true;
                break;
            }

            if (sscanf_s(buffer, s_RecordString, &s_PgoData[index].ILOffset, &s_PgoData[index].ExecutionCount) != 2)
            {
                failed = true;
                break;
            }

            index++;
        }

        probes += recordCount - 2;
    }

    s_PgoIndex = maxIndex;
}

HRESULT PgoManager::allocMethodBlockCounts(MethodDesc* pMD, UINT32 count,
    ICorJitInfo::BlockCounts** pBlockCounts, unsigned ilSize)
{
    // Initialize our out param
    *pBlockCounts = NULL;

    if (s_PgoData == nullptr)
    {
        return E_NOTIMPL;
    }

    unsigned methodIndex = 0;
    unsigned recordCount = count + 2;

    // Look for space in the profile buffer for this method.
    // Note other jit invocations may be vying for space concurrently.
    //
    while (true)
    {
        const unsigned oldIndex = s_PgoIndex;
        const unsigned newIndex = oldIndex + recordCount;

        // If there is no room left for this method,
        // that's ok, we just won't profile this method.
        //
        if (newIndex >= BUFFER_SIZE)
        {
            return E_NOTIMPL;
        }

        const unsigned updatedIndex = InterlockedCompareExchangeT(&s_PgoIndex, newIndex, oldIndex);

        if (updatedIndex == oldIndex)
        {
            // Found space
            methodIndex = oldIndex;
            break;
        }
    }

    // Fill in the header
    Header* const header = (Header*)&s_PgoData[methodIndex];
    header->recordCount = recordCount;
    header->token = pMD->IsDynamicMethod() ? 0 : pMD->GetMemberDef();
    header->hash = pMD->GetStableHash();
    header->ilSize = ilSize;

    // Return pointer to start of count records
    *pBlockCounts = &s_PgoData[methodIndex + 2];
    return S_OK;
}

HRESULT PgoManager::getMethodBlockCounts(MethodDesc* pMD, unsigned ilSize, UINT32* pCount,
    ICorJitInfo::BlockCounts** pBlockCounts, UINT32* pNumRuns)
{
    // printf("**** getMethodBlockCounts for %p (ilSize=%u)\n", pMD, ilSize);

    // Initialize our out params
    *pCount = 0;
    *pBlockCounts = NULL;
    *pNumRuns = 0;

   // Bail if there's no profile data.
    //
    if (s_PgoData == NULL)
    {
        return E_NOTIMPL;
    }

    // See if we can find counts for this method in the profile buffer.
    //
    const unsigned maxIndex = s_PgoIndex;
    const unsigned token    = pMD->IsDynamicMethod() ? 0 : pMD->GetMemberDef();
    const unsigned hash     = pMD->GetStableHash();


    unsigned index = 0;
    unsigned methodsChecked = 0;

    while (index < maxIndex)
    {
        // The first two "records" of each entry are actually header data
        // to identify the method.
        //
        Header* const header = (Header*)&s_PgoData[index];

        // printf("... checking entry %u at %p\n", index, header);

        // Sanity check that header data looks reasonable. If not, just
        // fail the lookup.
        //
        if ((header->recordCount < MIN_RECORD_COUNT) || (header->recordCount > MAX_RECORD_COUNT))
        {
            break;
        }

        // See if the header info matches the current method.
        //
        if ((header->token == token) && (header->hash == hash) && (header->ilSize == ilSize))
        {
            // printf(" ... found match\n");

            // Yep, found data.
            //
            *pBlockCounts = &s_PgoData[index + 2];
            *pCount       = header->recordCount - 2;
            *pNumRuns     = 1;
            return S_OK;
        }

        index += header->recordCount;
        methodsChecked++;
    }

    return E_NOTIMPL;
}

struct ClassProfileEntry
{
    uint ilOffset;
    uint count;
    CORINFO_CLASS_HANDLE table[4];
};

struct HistogramEntry
{
    CORINFO_CLASS_HANDLE m_mt;
    uint                 m_count;
};

CORINFO_CLASS_HANDLE PgoManager::getLikelyClass(MethodDesc* pMD, unsigned ilSize, unsigned ilOffset, UINT32* pLikelihood, UINT32* pNumberOfClasses)
{
    *pLikelihood = 0;
    *pNumberOfClasses = 0;

    // printf("**** getLikelyClass for %p (ilSize=%u) at offset %u\n", pMD, ilSize, ilOffset);
    // Bail if there's no profile data.
    //
    if (s_PgoData == NULL)
    {
        // printf("... no pgo data, sorry\n");
        return NULL;
    }

    // See if we can find profile data for this method in the profile buffer.
    //
    const unsigned maxIndex = s_PgoIndex;
    const unsigned token    = pMD->IsDynamicMethod() ? 0 : pMD->GetMemberDef();
    const unsigned hash     = pMD->GetStableHash();

    unsigned index = 0;
    unsigned methodsChecked = 0;

    while (index < maxIndex)
    {
        // The first two "records" of each entry are actually header data
        // to identify the method.
        //
        Header* const header = (Header*)&s_PgoData[index];

        // printf("... checking entry %u at %p\n", index, header);

        // Sanity check that header data looks reasonable. If not, just
        // fail the lookup.
        //
        if ((header->recordCount < MIN_RECORD_COUNT) || (header->recordCount > MAX_RECORD_COUNT))
        {
            break;
        }

        // See if the header info matches the current method.
        //
        if ((header->token == token) && (header->hash == hash) && (header->ilSize == ilSize))
        {
            // printf("... found match for method\n");

            // Yep, found data. See if there is a suitable class profile.
            //
            // This bit is currently somewhat hacky ... we scan the records, the count records come
            // first and are in increasing IL offset order. So when we see an entry with
            // decreasting iL offset, it's going to be an class profile.
            //
            // Note if there are no count probes in a method we may fail to find class profiles.
            //
            unsigned countILOffset = 0;
            unsigned j = 2;

            // Skip past all the count entries
            //
            while (j < header->recordCount)
            {
                // printf("... at %p, il offset is %u\n", &s_PgoData[index + j], s_PgoData[index + j].ILOffset);

                if (s_PgoData[index + j].ILOffset < countILOffset)
                {
                    break;
                }

                countILOffset = s_PgoData[index + j].ILOffset;
                j++;
            }

            // Now we're in the "class profile" portion of the slab for this method.
            // Look for the one that has the right IL offset.
            //
            while (j < header->recordCount)
            {
                // printf("... class profile at entry %u is for offset %u\n", j, s_PgoData[index + j].ILOffset);
                if (s_PgoData[index + j].ILOffset != ilOffset)
                {
                    j += 5;     // make this a global constant
                    continue;
                }

                // This is the entry we want. Form a histogram...
                //
                // Currently table holds 4 entries that may be null
                // or may be method table values.
                // 
                ClassProfileEntry* profileEntry = (ClassProfileEntry*)&s_PgoData[index + j];

                // printf("... class profile table=0x%p il=0x%X count=%u\n", profileEntry, profileEntry->ilOffset, profileEntry->count);
                
                for (int j = 0; j < 4; j++)
                {
                    TypeHandle th(profileEntry->table[j]);
                    MethodTable* pMT = th.AsMethodTable();
                    // printf("    entry[%d] = 0x%p (%s)\n", j, pMT, pMT == NULL ? "" : pMT->GetDebugClassName());
                }

                // Build the histogram
                //
                HistogramEntry histogram[4];
                unsigned histogramCount = 0;
                unsigned totalCount = 0;

                for (int k = 0; k < 4; k++)
                {
                    CORINFO_CLASS_HANDLE currentEntry = profileEntry->table[k];

                    if (currentEntry == NULL)
                    {
                        continue;
                    }

                    totalCount++;

                    bool found = false;
                    unsigned h = 0;
                    for(; h < histogramCount; h++)
                    {
                        if (histogram[h].m_mt == currentEntry)
                        {
                            histogram[h].m_count++;
                            found = true;
                            break;
                        }
                    }
                    
                    if (!found)
                    {
                        histogram[h].m_mt = currentEntry;
                        histogram[h].m_count = 1;
                        histogramCount++;
                    }
                }

                // Use histogram count as number of classes estimate
                //
                *pNumberOfClasses = histogramCount;

                // Report back what we've learned
                // (perhaps, use count to augment likelihood?)
                // 
                switch (histogramCount)
                {
                    case 1:
                    {
                        *pLikelihood = 100;
                        return histogram[0].m_mt;
                    }
                    break;

                    case 2:
                    {
                        // counts could be {3/1}, 2/2, {2/1}, 1/1
                        //
                        if (histogram[0].m_count >= histogram[1].m_count)
                        {
                            *pLikelihood = (100 * histogram[0].m_count) / totalCount;
                            return histogram[0].m_mt;
                        }
                        else
                        {
                            *pLikelihood = (100 * histogram[1].m_count) / totalCount;
                            return histogram[1].m_mt;
                        }
                    }
                    break;

                    case 3:
                    {
                        // Counts could be 1/1/1 or {2/1/1}
                        //
                        // If any entry has majority of counts, return it.
                        //
                        for (int m = 0; m < 3; m++)
                        {
                            if (histogram[m].m_count > 1)
                            {
                                *pLikelihood = (100 * histogram[m].m_count) / totalCount;
                                return histogram[m].m_mt;
                            }
                        }

                        // Othewise, just guess the first one.
                        *pLikelihood = (100 * histogram[0].m_count) / totalCount;
                        return histogram[0].m_mt;
                    }
                    break;

                    case 4:
                    {
                        // Counts must be 1/1/1/1.
                        //
                        // Just guess the first one. Caller can decide not
                        // to speculate if it so chooses.
                        //
                        *pLikelihood = (100 * histogram[0].m_count) / totalCount;
                        return histogram[0].m_mt;
                    }
                    break;

                    default:
                    {
                        return NULL;
                    }
                    break;
                }
            }

            // Failed to find a class profile entry
            // printf("... no class profile data for this method, sorry\n");
            return NULL;
        }

        index += header->recordCount;
        methodsChecked++;
    }

    // Failed to find any sort of profile data
    // printf("... no pgo data for this method, sorry\n");
    return NULL;
}

#else

// Stub version for !FEATURE_PGO builds
//
HRESULT PgoManager::allocMethodBlockCounts(MethodDesc* pMD, UINT32 count,
    ICorJitInfo::BlockCounts** pBlockCounts, unsigned ilSize)
{
    pBlockCounts = NULL;
    return E_NOTIMPL;
}

// Stub version for !FEATURE_PGO builds
//
HRESULT PgoManager::getMethodBlockCounts(MethodDesc* pMD, unsigned ilSize, UINT32* pCount,
    ICorJitInfo::BlockCounts** pBlockCounts, UINT32* pNumRuns)
{
    pBlockCounts = NULL;
    pCount = 0;
    pNumRuns = 0;
    return E_NOTIMPL;
}

// Stub version for !FEATURE_PGO builds
//
CORINFO_CLASS_HANDLE PgoManager::getLikelyClass(MethodDesc* pMD, unsigned ilSize, unsigned ilOffset)
{
    return NULL;
}

#endif // FEATURE_PGO
