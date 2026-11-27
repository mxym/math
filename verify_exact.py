#!/usr/bin/env python3
"""Exact integer spectra of tensor witnesses, including all tiny Boolean cores."""
from itertools import combinations, product
from math import prod


def sign(z, i):
    return 1-2*(z >> i & 1)


def transform(a):
    a = list(a)
    width = 1
    while width < len(a):
        for start in range(0,len(a),2*width):
            for j in range(start,start+width):
                x,y = a[j],a[j+width]
                a[j],a[j+width] = x+y,x-y
        width *= 2
    return a


def levels(a):
    return {w.bit_count() for w,c in enumerate(transform(a)) if c}


def all_cores(m):
    values=[]
    for flags in range(1<<(1<<m)):
        w=[sign(flags,x) for x in range(1<<m)]
        l=levels(w)
        if len(l)==1:
            values.append((next(iter(l)),w))
    return values


def matchings(indices):
    if not indices:
        yield ()
    else:
        pivot=indices[0]
        for k in range(1,len(indices)):
            for remaining in matchings(indices[1:k]+indices[k+1:]):
                yield ((pivot,indices[k]),)+remaining


def lift(n, pairs, eps, free, core, dual):
    return [prod(sign(x,i)+s*sign(x,j) for (i,j),s in zip(pairs,eps)) *
            (1+core[sum((x>>i&1)<<j for j,i in enumerate(free))]) *
            (-1)**(dual*x.bit_count()) for x in range(1<<n)]


def verify(n,i,j,records):
    dual=i+j>n
    k,l=(n-j,n-i) if dual else (i,j)
    m=n-2*k
    v=1<<(n-k-1)
    hits=0
    for pair_axes in combinations(range(n),2*k):
        free=tuple(x for x in range(n) if x not in pair_axes)
        for pairs in matchings(pair_axes):
            for signs in product((-1,1),repeat=k):
                for d,g in records[m]:
                    if d!=l-k: continue
                    f=lift(n,pairs,signs,free,g,dual)
                    assert levels(f)=={i,j}
                    assert sum(bool(z) for z in f)==v
                    hits+=1
    assert hits
    return hits


def main():
    bank={m:all_cores(m) for m in range(5)}
    print('homogeneous signed cores through four variables:', [len(bank[m]) for m in bank])
    cnt=sum(verify(n,i,j,bank) for n in range(1,5)
            for i in range(n+1) for j in range(i+1,n+1) if (j-i)%2)
    print(f'{cnt} all classified tensor witnesses for n<=4, ties and duals included')
    cases=0
    for n in range(1,11):
        for i in range(n+1):
            for j in range(i+1,n+1,2):
                dual=i+j>n
                k,l=(n-j,n-i) if dual else (i,j)
                free=tuple(range(2*k,n))
                fixed=[(-1)**(x&((1<<(l-k))-1)).bit_count() for x in range(1<<len(free))]
                f=lift(n,[(x,x+1) for x in range(0,2*k,2)], [1]*k, free, fixed,dual)
                assert levels(f)=={i,j}
                assert sum(bool(z) for z in f)==1<<(max(n-i,j)-1)
                cases+=1
    print(f'{cases} explicit witnesses over all opposite parity pairs through n=10')
    core=[]
    for x in range(32):
        a,b,c,d,e=[sign(x,i) for i in range(5)]
        core.append(e*(a*b+b*c+c*d-a*d)//2)
    tf=transform(core)
    assert all(abs(x)==1 for x in core)
    assert sum(x!=0 for x in tf)==4 and levels(core)=={3}
    assert sum(x!=-1 for x in core)==16
    sf=[1+sign(x,0)*sign(x,1)+sign(x,0)*sign(x,2)+sign(x,1)*sign(x,2)
        for x in range(8)]
    assert levels(sf)=={0,2} and sum(z!=0 for z in sf)==2
    print('non-character {0,3} extremizer checked; same-parity {0,2} control violates opposite-parity formula')
    print('PASS exact Walsh spectra and tensor witnesses')


if __name__=='__main__': main()
