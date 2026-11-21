#!/usr/bin/env python3
"""Exact physical Jacobian controls; proof is analytic + Bezout, not interpolation."""
from fractions import Fraction as Q
from check_eac_historical_jets import eac

def ck(b,s):
    if not b:raise ArithmeticError(s)
def rank(a):
    a=[list(map(Q,r)) for r in a]
    n=len(a);m=len(a[0]) if a else 0;i=0
    for j in range(m):
        z=next((u for u in range(i,n) if a[u][j]),None)
        if z is None:continue
        a[i],a[z]=a[z],a[i];p=a[i][j]
        for u in range(i+1,n):
            t=a[u][j]/p
            a[u]=[x-t*y for x,y in zip(a[u],a[i])]
        i+=1
        if i==n:break
    return i

controls=0
for N in [128,1718,1862,1928,2200,6142]:
    P,A=eac(N);k=len(P);full=rank(A);ck(full==k,('historical A',N))
    # Literal integer Jacobian of p_i+product p_j^A_ij−N at the tuple.
    J=[[int(i==j)+A[i][j]*((N-P[i])//P[j]) for j in range(k)]+[-1] for i in range(k)]
    # The two columns differ by scaling only: when Aij nonzero, divisor is exact.
    C=list(map(lambda p:Q(p,N-p),P))
    L=[[Q(A[i][j])+int(i==j)*C[i] for j in range(k)]+[-(1+C[i])] for i in range(k)]
    ck(all(Q(J[i][j])*([*P,N][j])/(N-P[i])==L[i][j] for i in range(k) for j in range(k+1)),N)
    small=[i for i,p in enumerate(P) if p*p<=N]
    # All ≤√N fixed must leave no tangent with changing N; literal check here.
    other=[i for i in range(k) if i not in small]
    a=[[r[i] for i in other] for r in J]
    b=[[r[i] for i in other]+[r[-1]] for r in J]
    ck(rank(b)==rank(a)+1,('large-factor path',N));controls+=1
    # For the historical tuples a number of them even have a sufficient single
    # small coordinate without freezing every tiny label. Do not assume this.
    one=[P[i] for i in small if rank([[z for j,z in enumerate(r) if j!=i] for r in J])==k]
    print(N,'k',k,'single-coordinate literal checks',one)
print(controls,'exact genuine Jacobian and sqrt-path checks: PASS')
