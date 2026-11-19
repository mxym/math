#!/usr/bin/env python3
"""Finite integer checks: peak formula, all signed canonical laws, competing arbitrary placements."""
from itertools import product, combinations
from functools import lru_cache


def req(test, message):
    if not test:
        raise ArithmeticError(message)


def conv(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return out


@lru_cache(None)
def peak(l):
    x=[1]
    for w in l:x=conv(x,[1]*(1+w))
    c=sum(l)//2
    return x[c], x[c]-(x[c+1] if c+1<len(x) else 0)


@lru_cache(None)
def exact(params):
    total=0; sensitive=[]
    for bits in product(range(2),repeat=3):
        w=1; l=[]
        for bit,(k,p,r) in zip(bits,params):
            w*=r if bit else p-r
            l.append(k-1+bit)
        M,D=peak(tuple(l))
        total+=w*M
        if sum(l)%2==0:
            req(D==int(2*max(l)<=sum(l)),('drop',l))
            sensitive.append(w*D)
    return total-min(sensitive)


def canonical(params):
    best=0
    for flips in product(range(2),repeat=2):
        arr=[1]
        for (k,p,r),flip in zip(params,(0,*flips)):
            x=[p]*k+[r]
            if flip:x.reverse()
            arr=conv(arr,x)
        best=max(best,max(arr))
    return best


@lru_cache(None)
def plans(k,p,r):
    # Complete placements of first two marginals using sites 0..5, up to translation.
    out=set()
    for heavy in combinations(range(6),k):
        for extra in set(range(6))-set(heavy):
            A=[(i,p) for i in heavy]+([(extra,r)] if r else [])
            start=min(i for i,_ in A)
            out.add(tuple(sorted((i-start,v) for i,v in A)))
    return sorted(out)


def main():
    chk=0
    pars=[(k,p,r) for k in range(1,7) for p,r in ((1,0),(3,1),(3,2),(2,1))]
    for pars3 in combinations(pars,3):
        a=exact(pars3)
        req(a==canonical(pars3),('canonical',pars3,a))
        chk+=1
    for i in pars:
        for j in pars:
            pars3=(i,i,j)
            req(exact(pars3)==canonical(pars3),('repeat',pars3))
            chk+=1
    print('Signed-interval convolution and closed box formula agree:',chk,'cap triples.')

    # No shape theorem used in competitor search. Enumerate two arbitrary marginals;
    # optimize the third over every possible integer placement by direct value sorting.
    small=[(k,p,r) for k in (1,2,3,4) for p,r in ((1,0),(3,1),(3,2))]
    cases=0
    for ia,i in enumerate(small):
        for j in small[ia:]:
            bounds=[exact((i,j,k)) for k in small]
            pairmax=[0]*len(small)
            for first in plans(*i):
                for second in plans(*j):
                    tmp=[0]*11
                    for pos,u in first:
                        for pos2,v in second:tmp[pos+pos2]+=u*v
                    tmp.sort(reverse=True)
                    for h,(k,p,r) in enumerate(small):
                        val=p*sum(tmp[:k])+r*tmp[k]
                        pairmax[h]=max(pairmax[h],val)
                    cases+=1
            req(pairmax==bounds,('competitor',i,j,pairmax,bounds))
    print('Exhaustive arbitrary two-marginal placements up to translation:',cases,
          'pairs; every pair tested against 12 optimally placed third shapes.')
    print('Includes singleton antecedents, reciprocal caps, unequal caps and positive residuals.')
    print('PASS; these finite checks are not the general proof.')


if __name__=='__main__':main()
