#!/usr/bin/env python3
"""Pure integer/Fraction replay of the all-fixed-k Chebyshev primal mechanism.

Sample supports for k=1,...,6, n=100,300,1000 are literal integer cycle
counts. The supports were discovered from Chebyshev-Lobatto fixed fractions,
but no floating-point, trigonometric library, solver or numerical optimization
is used on the certificate checking path. The all-n proof is mathematical,
not an inference from these finite regressions.
"""
from fractions import Fraction as Q
from transfer import moment

FIXED_COUNTS={
  1:{100:[0],300:[0],1000:[0]},
  2:{100:[50,0],300:[150,0],1000:[500,0]},
  3:{100:[75,25,0],300:[225,75,0],1000:[750,250,0]},
  4:{100:[85,50,14,0],300:[256,150,43,0],1000:[853,500,146,0]},
  5:{100:[90,65,34,9,0],300:[271,196,103,28,0],
     1000:[904,654,345,95,0]},
  6:{100:[93,75,50,25,6,0],300:[279,225,150,75,20,0],
     1000:[933,750,500,250,66,0]},
}


def solve(A,b):
    k=len(b)
    assert len(A)==k and all(len(row)==k for row in A)
    m=[[Q(v) for v in A[i]]+[Q(b[i])] for i in range(k)]
    for j in range(k):
        p=next((i for i in range(j,k) if m[i][j]),None)
        assert p is not None
        m[j],m[p]=m[p],m[j]
        d=m[j][j]
        m[j]=[v/d for v in m[j]]
        for i in range(k):
            if i!=j:
                d=m[i][j]
                m[i]=[m[i][r]-d*m[j][r] for r in range(k+1)]
    w=[m[i][-1] for i in range(k)]
    assert all(sum(Q(a)*b for a,b in zip(A[i],w))==Q(b[i])
               for i in range(k))
    return w


def certify(k,n,xlist):
    assert 1<=k<=6 and n>=100 and len(xlist)==k
    I=(n,)+(0,)*(k-1)
    T=((n-2,1)+(0,)*(k-2)) if k>=2 else (n-2,)
    nodes=[(x,)+(0,)*(k-1) for x in xlist]
    assert len(set(nodes+[I,T]))==k+2
    assert all(n-x>=k+1 for x in xlist)
    stats={typ:moment(n,k,typ) for typ in [I,T]+nodes}
    M=[]
    target=[]
    for j in range(k):
        M.append([
            (stats[node][j]-stats[I][j]) if q%2==0
            else -(stats[node][j]-stats[T][j])
            for q,node in enumerate(nodes)])
        target.append(n*(stats[T][j]-stats[I][j]))
    weights=solve(M,target)
    assert all(w>0 for w in weights)
    odd=sum(w for q,w in enumerate(weights) if q%2==0)
    even=sum(w for q,w in enumerate(weights) if q%2==1)
    pI=1-odd/n
    qT=1-even/n
    assert pI>0 and qT>0
    P=[(I,pI)]+[(nodes[q],w/n) for q,w in enumerate(weights)
                if q%2==0]
    R=[(T,qT)]+[(nodes[q],w/n) for q,w in enumerate(weights)
                if q%2==1]
    assert sum(w for _,w in P)==sum(w for _,w in R)==1
    for j in range(k+1):
        assert sum(w*stats[typ][j] for typ,w in P)==\
               sum(w*stats[typ][j] for typ,w in R)
    assert odd>0
    return odd


def main():
    count=0
    for k,tests in FIXED_COUNTS.items():
        for n,counts in tests.items():
            deficit=certify(k,n,counts)
            print('PASS k=%d n=%d exact marginal equality; all weights >0; '
                  'n(1-pI)>0: %s'%(k,n,bool(deficit>0)),flush=True)
            count+=1
    assert count==18
    print('ALL 18 ALL-RANK PRIMAL REGRESSIONS PASSED (k=1..6)')


if not __debug__:
    raise RuntimeError('Run without -O: optimized Python disables assert checks')

if __name__=='__main__':
    main()
