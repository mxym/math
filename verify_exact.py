#!/usr/bin/env python3
"""Exact integer slice matrices and explicit harmonic-vector evaluations."""
from itertools import combinations
from math import comb
from fractions import Fraction as Q

def multiply_right_integer(m, diag, adj, weight):
    # m*(diag I + weight Adj), using graph sparsity.
    out = []
    for row in m:
        out.append([diag*row[j]+weight*sum(row[i] for i in adj[j])
                    for j in range(len(row))])
    return out

def cheb_rat(t, x):
    # Direct coefficients by expanding (x+sqrt(x*x-1))^t symmetrically.
    return sum(comb(t, 2*r)*x**(t-2*r)*(x*x-1)**r
               for r in range(t//2+1))

slices = filters = harmonics = support_zeros = 0
for n in range(3, 10):
    for k in range(1, (n-1)//2+1):
        omega = [sum(1<<v for v in E) for E in combinations(range(n), k)]
        m = len(omega)
        overlap = [[(a&b).bit_count() for b in omega] for a in omega]
        adj = [[i for i, x in enumerate(row) if x==k-1] for row in overlap]
        a = [[int(x==0) for x in row] for row in overlap]
        kdeg, jdeg = comb(n-k,k), k*(n-k)
        assert all(sum(row)==kdeg for row in a)
        assert all(len(ns)==jdeg for ns in adj)
        aj = multiply_right_integer(a,0,adj,1)
        assert all(aj[i][j]==aj[j][i] for i in range(m) for j in range(m))
        Hx, Av, vectors, multiplicity = [], [], [], []
        for j in range(k+1):
            # Product of disjoint signed pair differences on the slice.
            v = [1]*m
            for l in range(j):
                for i, E in enumerate(omega):
                    v[i] *= ((E>>(2*l))&1)-((E>>(2*l+1))&1)
            assert any(v)
            x = Q(j*(n-j+1),n)
            nu = Q((-1)**j*comb(n-k-j,k-j), kdeg)
            for i in range(m):
                assert sum(a[i][h]*v[h] for h in range(m))==kdeg*nu*v[i]
                assert jdeg*v[i]-sum(v[h] for h in adj[i])==n*x*v[i]
            Hx.append(x); Av.append(nu); vectors.append(v)
            multiplicity.append(comb(n,j)-(comb(n,j-1) if j else 0))
        # Negative control: the merely disjoint kernel is not U.
        assert Av[1]==-Q(k,n-k) and any(a[0][i]==0 for i in range(m))
        for t in range(1,k+1):
            L=32*t
            D=(L-1)*n
            znum=(L+1)*n
            diag=znum-2*jdeg
            # D^t A_raw T_t(Z) as an integer matrix.
            lo=a
            hi=multiply_right_integer(a,diag,adj,2)
            for _ in range(1,t):
                z=multiply_right_integer(hi,diag,adj,2)
                lo,hi=hi,[[2*z[i][j]-D*D*lo[i][j] for j in range(m)]
                             for i in range(m)]
            denom0=cheb_rat(t,Q(znum,D))
            denom=kdeg*D**t*denom0
            assert denom.denominator==1 and denom>0
            for i in range(m):
                row=hi[i]
                assert sum(row)==denom
                assert sum(map(abs,row))<=denom*(2*n+7)**t
                for j in range(m):
                    assert hi[j][i]==row[j]
                    if overlap[i][j]>t:
                        assert row[j]==0
                        support_zeros+=1
            lambdas = [nu*cheb_rat(t,Q(L+1-2*x,L-1))/denom0
                       for x,nu in zip(Hx,Av)]
            for v,lam in zip(vectors,lambdas):
                for i in range(m):
                    assert sum(hi[i][j]*v[j] for j in range(m))==denom*lam*v[i]
                harmonics+=1
            assert Q(sum(a*a for row in hi for a in row),denom**2)==sum(
                d*lam**2 for d,lam in zip(multiplicity,lambdas))
            if t<k:
                assert all(not hi[i][i] for i in range(m))
            else:
                # Negative control: degree k does permit diagonal support.
                assert all(hi[i][i]>0 for i in range(m))
            filters+=1
        slices+=1
print("EXACT PASS:",slices,"slices,",filters,"matrix filters,",harmonics,
      "harmonic eigenvector checks,",support_zeros,"forbidden entries")
