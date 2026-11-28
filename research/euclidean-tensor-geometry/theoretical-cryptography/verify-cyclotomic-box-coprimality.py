#!/usr/bin/env python3
"""Finite-field identities behind a coefficient-box coprimality bound."""
from collections import Counter
from itertools import product
from math import gcd, prod


def phi(M):
    return sum(gcd(j,M)==1 for j in range(M))


def residue_degree(q,M):
    u=q%M
    f=1
    while u != 1:
        u=u*q%M
        f+=1
    return f


def make_field(q,P):
    f=len(P)-1
    assert P[-1] == 1
    z=(0,)*f
    one=(1,)+(0,)*(f-1)
    all_elements=list(product(range(q),repeat=f))

    def mul(a,b):
        out=[0]*(2*f-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                out[i+j]+=x*y
        for k in range(2*f-2,f-1,-1):
            for j in range(f):
                out[k-f+j]-=out[k]*P[j]
        return tuple(x%q for x in out[:f])

    def add(a,b):
        return tuple((x+y)%q for x,y in zip(a,b))

    def scale(c,v):
        return tuple(c*x%q for x in v)

    def power(a,e):
        r=one
        while e:
            if e%2:
                r=mul(r,a)
            a=mul(a,a)
            e//=2
        return r

    def trace(a):
        out=z
        for _ in range(f):
            out=add(out,a)
            a=power(a,q)
        assert all(x==0 for x in out[1:])
        return out[0]

    assert all(power(x,len(all_elements)-1)==one for x in all_elements if x!=z)
    alpha=((-P[0])%q,) if f==1 else (0,1)+(0,)*(f-2)
    return all_elements,z,one,alpha,mul,add,scale,power,trace


def min_power_order(M,z,one,a,mul):
    x=one
    assert a!=z
    for k in range(1,M+1):
        x=mul(x,a)
        if x==one:
            return k
    raise AssertionError


def fixture(M,q,P):
    n = phi(M)
    elems,z,one,alpha,mul,add,scale,power,trace=make_field(q,P)
    f=len(P)-1
    assert residue_degree(q,M)==f and f<=n and n%f==0
    Q=q**f
    assert Q>=M+1>=n+1
    assert min_power_order(M,z,one,alpha,mul)==M
    mon=[power(alpha,k) for k in range(n)]
    assert len(set(mon))==n
    L=n//f
    weights=[1,3]+list(range(2,q)) if q>=2 else [1]
    vals={}
    checks=0
    for b in range(L):
        vec=[tuple(trace(mul(u,a)) for a in mon[b*f:(b+1)*f]) for u in elems]
        assert len(set(vec))==Q
        g={u:prod(weights[c] for c in x) for u,x in zip(elems,vec)}
        assert sum(v**L for v in g.values())==sum(w**L for w in weights)**f
        vals[b]=g
        checks+=Q

    assert sum(prod(vals[b][u] for b in range(L)) for u in elems) <= sum(w**L for w in weights)**f
    # Integer counters for boxes with varying lengths and centers: direct
    # unnormalized convolutions agree with explicit enumeration for the
    # first f factors, and the largest normalized atom cannot then grow.
    pm=Counter({z:1})
    total=1
    previous_ratio=None
    independent_peaks=[]
    for j,a in enumerate(mon):
        values=range(-1,j%3+2)
        new=Counter()
        for x,c in pm.items():
            for v in values:
                new[add(x,scale(v+j,a))]+=c
        pm=new
        total*=len(values)
        independent_peaks.append(max(Counter((v+j)%q for v in values).values()))
        if j+1==f:
            assert max(pm.values())==prod(independent_peaks)
        assert sum(pm.values())==total
        if j+1>=f:
            assert max(pm.values())*3**f <= total*2**f
            if previous_ratio:
                prev_n,prev_d=previous_ratio
                assert max(pm.values())*prev_d <= prev_n*total
            previous_ratio=max(pm.values()),total
        checks+=len(pm)
    return checks


def check_split_level_sets(M,q,alpha):
    if alpha is None:
        # Consecutive distinct weights produce nontrivial small level
        # sets in the general scalar lemma, separately from ring fixtures.
        n=M
        a=list(range(1,n+1))
    else:
        n=phi(M)
        a=[pow(alpha,j,q) for j in range(n)]
        assert pow(alpha,M,q)==1
        for t in range(1,M):
            assert pow(alpha,t,q)!=1
    assert len(set(a))==n
    values=[]
    for u in range(q):
        values.append(sum(min(u*w%q,(-u*w)%q)**2 for w in a))

    Smax=(q*q*n)//64
    large_set={u for u,v in enumerate(values) if v<=Smax}
    assert len(large_set)*n<=4*q
    tests=0
    for s in sorted(set(values)):
        if 0<s<=Smax:
            one_set={u for u,v in enumerate(values) if v<=s}
            k=1
            while (k+1)**2*s<=Smax:
                k+=1
            sumset={0}
            for _ in range(k):
                sumset={(u+v)%q for u in sumset for v in one_set}
            assert all(values[u]<=k*k*s for u in sumset)
            assert min(q,k*(len(one_set)-1)+1)<=len(sumset)
            tests+=1
    return tests


def main():
    total=sum(fixture(*p) for p in (
      (8,3,(2,1,1)), (8,5,(2,0,1)), (7,2,(1,1,0,1)),
      (5,2,(1,1,1,1,1)), (13,3,(2,2,0,1)), (9,2,(1,0,0,1,0,0,1)),
      (16,17,(14,1)), (7,29,(13,1)),
    ))
    level=sum(check_split_level_sets(M,q,a) for M,q,a in (
        (16,17,3), (7,29,16), (16,97,8), (16,257,2),
        (16,769,27), (8,769,None), (10,257,None),
    ))
    assert level>0
    print(f"PASS: {total} exact residue-basis/Hölder/convolution checks "
          f"and {level} nonzero split level sets.")


if __name__=="__main__":
    main()
