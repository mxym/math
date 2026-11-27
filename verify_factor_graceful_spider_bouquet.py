#!/usr/bin/env python3
"""Exact checks for the leaf-rooted bouquet lift and spider zero pins."""
from itertools import product

checks = 0


def check(ok):
    global checks
    checks += 1
    if not ok:
        raise AssertionError("exact check failed")


def differences(xs):
    return [abs(x-y) for x,y in zip(xs,xs[1:])]


def path(n, alpha=False, pin=None):
    """Find a graceful permutation by depth-first exact search."""
    low=n//2+1 if n%2 else n//2
    L=(1<<(low))-1
    F=(1<<n)-1
    order=tuple(z for i in range((n+1)//2)
                  for z in ([i,n-1-i] if i<n-1-i else [i]))
    p,t=pin if pin is not None else (-1,-1)
    used=[]
    def dfs(V,D):
        j=len(used)
        if j==n:
            return tuple(used)
        C=F^V
        if alpha:
            C&=(F^L) if j%2 else L
        C=C & (1<<t) if j==p else C & ~(1<<t) if t>=0 else C
        for z in order:
            b=1<<z
            if not C&b:
                continue
            d=1<<abs(used[-1]-z) if j else 0
            if D&d:
                continue
            if n>1 and pin is not None and t in (0,n-1):
                other=n-1-t
                if z==other and abs(j-p)!=1:
                    continue
            used.append(z)
            result=dfs(V|b,D|d)
            if result is not None:
                return result
            used.pop()
        return None
    return dfs(0,0)


def lift_spider(k,A,B):
    m=len(B)
    q=k*m
    center=A[0]
    legs=[tuple(a+(q-m if j%2 else 0) for j,a in enumerate(A[1:],1))]
    for i in range(2,k+1):
        legs.append(tuple(b + m*(k-i+1 if j%2 else i-1)
                          for j,b in enumerate(B,1)))
    return center,legs


def verify(k,m,center,legs):
    q=k*m
    check(len(legs)==k and all(len(leg)==m for leg in legs))
    check(sorted([center]+[a for leg in legs for a in leg])==list(range(q+1)))
    check(sorted([d for leg in legs for d in differences((center,)+leg)])==
          list(range(1,q+1)))


def rofa4(k):
    if k==1:
        return 1,[(4,0,2,3)]
    q=4*k
    legs=[(q-2,0,q,1),(q-1,4,q-3,3)]
    for i in range(3,k+1):
        legs.append((4*(k-i+1)+2,4*i-5,4*(k-i+1)+1,4*i-4))
    return 2,legs


def generic_bouquet(k,es,A,B):
    m=len(es)
    parity=[None]*(m+1)
    parity[0]=0
    for u,v in es:
        parity[v]=1-parity[u]
    q=m*k
    copies=[tuple(A[v]+(q-m)*parity[v] for v in range(1,m+1))]
    for i in range(2,k+1):
        copies.append(tuple(B[v-1]+m*(k-i+1 if parity[v] else i-1)
                            for v in range(1,m+1)))
    vals=[A[0]]+[x for row in copies for x in row]
    diffs=[]
    for row in copies:
        z=(A[0],)+row
        diffs.extend(abs(z[u]-z[v]) for u,v in es)
    check(sorted(vals)==list(range(q+1)))
    check(sorted(diffs)==list(range(1,q+1)))


def main():
    pins=0
    for m in range(1,17):
        h=(m+1)//2
        for j in range(m+1):
            if (m,j)==(4,2):
                check(path(5,True,(2,0)) is None)
                for k in (1,2,3,4,9,37,128):
                    c,L=rofa4(k)
                    verify(k,m,c,L)
                    check(L[0][1]==0)
                continue
            v=m if j%2 else 0
            A=path(m+1,True,(j,v))
            check(A is not None)
            b=path(m,False,(0,A[0]+h-1))
            check(b is not None)
            B=tuple(z-h+1 for z in b)
            pins+=1
            for k in (1,2,3,4,9,37,128):
                c,L=lift_spider(k,A,B)
                verify(k,m,c,L)
                check((c if j==0 else L[0][j-1])==(k*m if j%2 else 0))
    explicit=[
        ((1,5,0,3,2,4),(1,0,-2,2,-1),2,0),
        ((1,3,2,5,0,4),(1,0,-2,2,-1),3,5),
        ((1,3,2,5,0,4),(1,0,-2,2,-1),4,0),
        ((2,3,1,4,0,5),(2,-2,1,-1,0),5,5),
    ]
    for A,B,j,v in explicit:
        for k in range(1,51):
            c,L=lift_spider(k,A,B)
            verify(k,5,c,L)
            check(L[0][j-1]==(v*k))

    # A branched rooted copy: r attached to the center of a 4-star.
    es=[(0,1),(1,2),(1,3),(1,4)]
    A=(0,4,1,2,3)
    B=(0,1,2,3)
    for k in range(1,51):
        generic_bouquet(k,es,A,B)

    for m,k in product(range(1,41),range(2,61)):
        t=range(2-k,k-1,2)
        internal=[abs(m*j+r) for j in t for r in range(1,m)]
        check(sorted(internal)==[x for x in range(1,m*(k-1)+1) if x%m])
    print(f"Bouquet lift: {checks} exact assertions; "
          f"{pins} independent alpha path pins through leg length 16.")


if __name__=="__main__":
    main()
