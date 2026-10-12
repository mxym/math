#!/usr/bin/env python3
"""Independent exact checker for 18 fixed S_n three-subset LP certificates.

NO optimizer, symbolic solver, floating point, or discovery code is used.
Given published fixed JSON, the checker independently enumerates every
conjugacy class for each n=6,...,23, verifies class-mass primal positivity
and all 4 orbital moments, and checks dual inequalities at every class.
The universal linear-programming duality is proved in paper.md, Section 18.

Usage from repository root:
python notes/sharp-robust-permanent/code/check_three_subset_certificates.py
"""
from fractions import Fraction as F
from itertools import combinations
from json import loads
from math import comb, factorial
from pathlib import Path


def partitions(n, limit=None):
    if n == 0:
        yield ()
        return
    if limit is None:
        limit = n
    for head in range(min(n, limit), 0, -1):
        for tail in partitions(n-head, head):
            yield (head,) + tail


def conjugacy_size(p):
    n=sum(p)
    divisor=1
    for length in set(p):
        k=p.count(length)
        divisor *= length**k * factorial(k)
    assert factorial(n)%divisor == 0
    return factorial(n)//divisor


def representative(p):
    """Canonical permutation of vertices with these cycle lengths."""
    result=[]
    offset=0
    for k in p:
        result.extend(offset+(i+1)%k for i in range(k))
        offset += k
    return result


def edge_orbit_counts(n, p, triples):
    """Exact number of 3-sets E with |E intersect g(E)| = j, j=0..3."""
    g=representative(p)
    out=[0,0,0,0]
    for e in triples:
        transformed=(g[e[0]],g[e[1]],g[e[2]])
        count=(e[0] in transformed)+(e[1] in transformed)+(e[2] in transformed)
        out[count] += 1
    assert sum(out)==comb(n,3)
    return tuple(out)


def verify_certificate(cert):
    n=cert['n']
    assert 6<=n<=23
    id_part=(1,)*n
    pos=[(tuple(row['cycles']),F(row['weight'])) for row in cert['P']]
    neg=[(tuple(row['cycles']),F(row['weight'])) for row in cert['Q']]
    assert len(pos) in (2,3) and len(neg)==2
    assert pos[0][0]==id_part and all(p!=id_part for p,_ in pos[1:]+neg)
    assert all(q>0 for _,q in pos+neg)
    assert sum(q for _,q in pos)==sum(q for _,q in neg)==1
    assert len({p for p,_ in pos+neg})==len(pos+neg)
    assert all(sum(p)==n and tuple(sorted(p,reverse=True))==p
               for p,_ in pos+neg)

    C=F(cert['optimal_coefficient'])
    coeff=tuple(F(x) for x in cert['dual'])
    upper=F(cert['upper'])
    lower=F(cert['lower'])
    assert len(coeff)==3 and 0<C<1 and upper-lower==C
    assert pos[0][1]==C

    triples=list(combinations(range(n),3))
    all_parts=list(partitions(n))
    stats={p:edge_orbit_counts(n,p,triples) for p in all_parts}
    assert sum(conjugacy_size(p) for p in all_parts)==factorial(n)
    assert all(p in stats for p,_ in pos+neg)

    # The orbital averages determine complete edge-image marginals for
    # conjugation-invariant distributions; use all four orbitals.
    for j in range(4):
        p_stat=sum(weight*stats[p][j] for p,weight in pos)
        q_stat=sum(weight*stats[p][j] for p,weight in neg)
        assert p_stat==q_stat, (n,j,p_stat,q_stat)
        size_of_orbital=comb(n,3)*comb(3,j)*comb(n-3,3-j)
        assert size_of_orbital>0 and p_stat/size_of_orbital>=0

    def dual_value(p):
        data=stats[p]
        return int(p==id_part)-sum(coeff[j]*data[j] for j in range(3))

    for p in all_parts:
        val=dual_value(p)
        assert lower<=val<=upper,(n,p,val,lower,upper)
    for p,_ in pos:
        assert dual_value(p)==upper,(n,p,'P not upper tight')
    for p,_ in neg:
        assert dual_value(p)==lower,(n,p,'Q not lower tight')

    # A positive rational delta makes uniform + delta*(P-Q) a probability.
    # Since P and Q have disjoint class support, total variation is delta.
    group_size=factorial(n)
    qmax=max(weight/conjugacy_size(p) for p,weight in neg)
    delta=F(1,2*group_size*qmax)
    base=F(1,group_size)
    assert delta>0
    perturbed={}
    for p,weight in pos:
        perturbed[p]=base+delta*weight/conjugacy_size(p)
    for p,weight in neg:
        perturbed[p]=base-delta*weight/conjugacy_size(p)
    assert min(perturbed.values())>=0
    assert perturbed[id_part]-base==C*delta
    assert sum(w for _,w in pos)==sum(w for _,w in neg)==1

    return len(all_parts),C


def main():
    path=Path(__file__).resolve().parents[1] / 'certificates' / 'three_subset_n6_23.json'
    data=loads(path.read_text(encoding='utf-8'))
    records=data['degrees']
    assert len(records)==18
    assert [r['n'] for r in records]==list(range(6,24))
    results=[]
    for cert in records:
        count,C=verify_certificate(cert)
        results.append((cert['n'],C))
        print('PASS n=%d classes=%d EXACT OPTIMAL C=%s' %
              (cert['n'],count,C),flush=True)
    assert results[0]==(6,F(5,14))
    assert results[1]==(7,F(5,14))
    assert results[2]==(8,F(89,244))
    assert results[-1]==(23,F(6219,11242))
    print('EIGHTEEN EXACT THREE-SUBSET CERTIFICATES REPLAYED;'
          ' all classes, primal/dual bounds, rational positivity.')


if __name__=='__main__':
    main()
