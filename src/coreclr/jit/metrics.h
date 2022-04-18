// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

#ifndef _METRIC_H_
#define _METRIC_H_

class Metrics;
class Compiler;

//------------------------------------------------------------------------
// Metrics
//
// Metrics provide a way to externalize ad-hoc numeric data about methods
// being compiled.
//
// Currently this data is per compilation request; aggregation/analysis is
// expected to be done by external tools.
//
// Usage:
//
// For metrics that are set once and/or read/written rarely:
//
//    compiler->m_metrics->Set("mymetric", v);
//
// For metrics that are set frequently:
// 
//    Metric* const m = compiler->m_metrics->FindOrCreate("mymetric");
//    m->Increment();
//
// To Externalize
//
//    compiler->m_metrics->ForEachMetric(<functor>);
//
//------------------------------------------------------------------------

// A single metric

class Metric
{
    friend class Metrics;

private:

    const char* m_name;
    double      m_value;

    void SetName(const char* name)
    {
        m_name = name;
    }

    Metric() : m_name(nullptr), m_value(0) {}
    Metric(const Metric&) = delete;
    Metric& operator=(const Metric&) = delete;

public:

    const char* Name() const
    {
        return m_name;
    }
    double Value() const
    {
        return m_value;
    }
    int IntValue() const
    {
        return (int)m_value;
    }
    unsigned int UintValue() const
    {
        return (unsigned int)m_value;
    }
    void Set(double d)
    {
        m_value = d;
    }
    void Reset()
    {
        m_value = 0.0;
    }
    void Add(double d)
    {
        m_value += d;
    }
};

// A collection of Metrics

class Metrics
{
private:

    Metric*        m_metrics;
    Metric         m_overflowMetric;
    const unsigned m_size;
    unsigned       m_count;

public:
    Metrics(Compiler*, unsigned size = 128);

    Metric* FindOrCreateMetric(const char* name)
    {
        for (unsigned i = 0; (i < m_count) && (i < m_size); i++)
        {
            if (strcmp(name, m_metrics[i].Name()) == 0)
            {
                return &m_metrics[i];
            }
        }

        if (m_count < m_size)
        {
            m_metrics[m_count].SetName(name);
            return &m_metrics[m_count++];
        }

        m_count++;
        return &m_overflowMetric;
    }

    Metric* GetMetric(unsigned i)
    {
        if (i < Count())
        {
            return &m_metrics[i];
        }

        return &m_overflowMetric;
    }

    void Set(const char* name, double value)
    {
        FindOrCreateMetric(name)->Add(value);
    }

    void Add(const char* name, double value)
    {
         FindOrCreateMetric(name)->Add(value);
    }

    void Increment(const char* name)
    {
        Add(name, 1.0);
    }

    void Decrement(const char* name)
    {
        Add(name, -1.0);
    }

    unsigned Count() const
    {
        return min(m_size, m_count);
    }

    unsigned Size() const
    {
        return m_size;
    }

    unsigned TotalCount() const
    {
        return m_count;
    }
};



#endif // _METRIC_H_
