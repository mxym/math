#!/usr/bin/env python3
"""Exact certificates from rational support matrices, no SDP solver."""
from fractions import Fraction as F
from itertools import combinations,product


def eye_kron(E):
    return [[E[i%2][j%2] if i//2==j//2 else F(0) for j in range(4)]
            for i in range(4)]


def sub(U,V):
    return [[a-b for a,b in zip(x,y)] for x,y in zip(U,V)]


def determinant(A):
    if len(A)==1:
        return A[0][0]
    return sum((-1)**j*v*determinant([row[:j]+row[j+1:] for row in A[1:]])
               for j,v in enumerate(A[0]) if v)


def principal(M):
    for r in range(1,len(M)+1):
        for I in combinations(range(len(M)),r):
            yield determinant([[M[i][j] for j in I] for i in I])


def mult(A,v):
    return [sum(x*y for x,y in zip(row,v)) for row in A]


def quadratic(A,v):
    return sum(x*y for x,y in zip(mult(A,v),v))


def state(a,b):
    return [[z/2 for z in row] for row in
            [[a+b,a,F(0),b], [a,a,F(0),F(0)],
             [F(0)]*4, [b,F(0),F(0),b]]]


def check_profile(t):
    denom=1+4*t-t*t
    a,b=4*t/denom,(1-t*t)/denom
    assert a+b==1 and 0<a<1 and a*(1-t*t)==4*b*t
    W=state(a,b)
    u=b*(1+t)/((1-t)*(1+t*t))
    E=[[u,u*t],[u*t,b+u*t*t]]
    c=E[0][0]+E[1][1]
    slack=sub(eye_kron(E),W)
    prec=list(principal(slack))
    assert all(x>=0 for x in prec) and prec[-1]==0
    v=[1,t,-t,1]
    assert mult(slack,v)==[0]*4
    # Actual squared lower witness for c from a state dual.
    assert quadratic(W,v)==(1+t*t)*c
    # Check exact cost without radical arithmetic.
    assert c>a/2+b and (c-a/2-b)**2==b*b+a*a/4
    assert E[0][0]-E[1][1]==2*b*t/(1+t*t)>0
    return a,b,E,c,slack


def check_whites():
    examples=0
    # Choose squared block sizes so that the conditional optimizers
    # themselves are rational despite the pure state vector.
    for sizes in ([1],[1,1],[1,4],[4,9],[1,4,9],[4,4,4]):
        roots=[i for n in sizes for i in range(1,4) if i*i==n]
        assert len(roots)==len(sizes)
        m=sum(sizes)
        cst=F(sum(roots)**2,m)
        cch=len(sizes)
        # In Schmidt coordinates these are the exact inverse
        # inequalities corresponding to the state/Choi choices.
        Est=[F(k*sum(roots),m) for k in roots]
        Ech=[F(n*cch,m) for n in sizes]
        assert sum(Est)==cst and sum(Ech)==cch
        assert all(y>0 for y in Est+Ech)
        for E in (Est,Ech):
            assert sum((F(n,m)/y for n,y in zip(sizes,E)))==1
        # Every correlated-input diagonal is E_i/n_i.
        assert len({y/n for y,n in zip(sizes,Ech)})==1
        assert (len({y/n for y,n in zip(sizes,Est)})==1)==(len(set(sizes))==1)
        for p in (F(0),F(1,9),F(1,2),F(1)):
            state_cost=p/4+(1-p)*cst
            channel_cost=p/4+(1-p)*cch
            assert (state_cost==channel_cost)==(p==1 or len(set(sizes))==1)
            examples+=1
    # Explicit qutrit family cost state 1+2 sqrt(2)/3 < 2.
    assert F(8,9)<1
    return examples


def main():
    grid=sorted({F(a,b) for b in range(2,20) for a in range(1,b)})
    for t in grid:
        check_profile(t)
    a,b,E,c,S=check_profile(F(1,3))
    assert (a,b)==(F(3,5),F(2,5))
    assert c==F(6,5) and E==[[F(18,25),F(6,25)],[F(6,25),F(12,25)]]
    assert [[50*z for z in row] for row in S]==[[11,-3,0,-10],[-3,9,0,0],
                                                    [0,0,36,12],[-10,0,12,14]]
    w=[12,2,-3,8]
    assert w[0]*w[1]+w[2]*w[3]==0
    lhs=2*quadratic(state(a,b),w)/sum(v*v for v in w)
    assert lhs==F(1388,1105)>c
    whites=check_whites()
    print(f"rational checks: {len(grid)} interior mixture profiles, all 15 PSD minors and exact trace-dual matches")
    print(f"60:40: state cost {c}, exact channel lower bound {lhs} > state")
    print(f"white-noise checks: {whites} partition/noise cases, unequal qutrit blocks PASS")


if __name__=='__main__':
    main()
