#!/usr/bin/env python3
"""Finite synthetic checks of unimodular fibers and soft-node extrapolation."""
from collections import Counter
from decimal import Decimal as Dc, localcontext
from fractions import Fraction as F
from itertools import combinations, product
from random import Random
from sympy import Matrix, eye, zeros

rng=Random(65834)
log=Counter()


def coeff_shape(M):
    n=M.cols
    s=M.rows
    I=list(M.T.rref()[1])
    r=len(I)
    J=list(M[I,:].rref()[1])
    B=M[I,J]
    inv=B.inv()
    assert abs(B.det())==1
    free=[j for j in range(n) if j not in J]
    V=M[:,J]
    U=zeros(n,len(free))
    X=zeros(n,r)
    for j,j0 in enumerate(J):
        X[j0,j]=1
    for q,j in enumerate(free):
        U[j,q]=1
        u=-inv*M[I,j]
        for j0,t in zip(J,u):
            U[j0,q]=t
    assert M*U==zeros(s,len(free)) and all(abs(t)<=1 and t.is_Integer for t in U)
    assert M*X==V
    W=M[:,J]*inv
    assert all(abs(t)<=1 and t.is_Integer for t in W)
    return I,J,V,U,X,W


def check(M,Q,ntrials):
    s,n=M.shape
    I,J,V,U,X,W=coeff_shape(M)
    r=len(I)
    K=U.T*Q*U
    G=X.T*Q*X-X.T*Q*U*K.inv()*U.T*Q*X if U.cols else X.T*Q*X
    H=V.T*V
    T=F(rng.randrange(3,20),rng.randrange(1,3))
    A=Q+T*M.T*M
    Ai=A.inv()
    for k in range(ntrials):
        if k%3:
            t=Matrix(r,1,[rng.randrange(-3,4) for _ in I])
            y=V*t
        else:
            t=None
            y=Matrix(s,1,[rng.randrange(-4,5) for _ in range(s)])
        y0=y[I,:]
        u=(T*T*y.T*M*Ai*M.T*y)[0]
        f=(T*y.T*y)[0]-u
        assert 0<=u<=(T*y.T*y)[0]
        if W*y0==y:
            xx=zeros(n,1)
            pred=M[I,J].inv()*y0
            for a,b in zip(J,pred):
                xx[a]=b
            assert M*xx==y and all(x.is_Integer for x in xx)
            g=pred
            direct=(g.T*G*(eye(r)+H.inv()*G/T).inv()*g)[0]
            f0=(g.T*G*g)[0]
            assert f==direct and 0<=f<=f0
            log["integer fibers/effective precisions"]+=1
        else:
            assert f>=T/F(r+1)
            # Projection-distance bound independently of the left relation.
            k=y-V*H.inv()*V.T*y
            assert (k.T*k)[0]>=F(1,r+1)
            log["infeasible lattice gaps"]+=1


for nit in range(21):
    n=rng.randrange(2,6)
    C=[]
    for a,b in [(0,min(n,3))]+[(rng.randrange(n),None) for _ in range(6)]:
        if b is None:
            b=rng.randrange(a+1,n+1)
        ss=rng.choice((-1,1))
        C.append([ss*int(a<=j<b) for j in range(n)])
    M=Matrix(C)
    # Independently check all minors in the synthetic interval examples.
    for r in range(1,n+1):
        for I in combinations(range(len(C)),r):
            for J in combinations(range(n),r):
                assert abs(M[list(I),list(J)].det())<=1
                log["TU minors"]+=1
    Q=eye(n)*F(1,211)
    check(M,Q,22)
    I,J,V,U,X,W=coeff_shape(M)
    Q=zeros(n)
    for j in range(n):
        if j not in J:
            Q[j,j]=F(j+1,123)
    check(M,Q,10)


def weights(nodes):
    out=[]
    for i,u in enumerate(nodes):
        w=F(1)
        for j,v in enumerate(nodes):
            if i!=j:
                w*=(-v)/(u-v)
        out.append(w)
    return out


for r in range(1,23):
    h=F(1,163+r*r)
    nodes=[h*(1+F(i,r)) for i in range(r+1)]
    ww=weights(nodes)
    assert sum(abs(x) for x in ww)<=2**(4*r)
    for i in range(r+1):
        assert sum(w*x**i for w,x in zip(ww,nodes))==(1 if i==0 else 0)
        log["interpolation constraints"]+=1

with localcontext() as ctx:
    ctx.prec=68
    def expq(f):
        f=F(f)
        return (Dc(f.numerator)/Dc(f.denominator)).exp()
    for sign in (-1,1):
        M=Matrix([[1,1],[sign,sign]])
        Q=eye(2)*F(1,73)
        points=[Matrix(2,1,v) for v in product((-1,0,1),repeat=2)]
        D=11
        nodes=[F(1,601)*(1+F(i,D)) for i in range(D+1)]
        ww=weights(nodes)
        def soft(T):
            A=(Q+T*M.T*M).inv()
            return sum(expq(-(F(2)+T)*(v.T*v)[0]+(T*T*v.T*M*A*M.T*v)[0]) for v in points)
        val=sum(soft(1/h)*(Dc(w.numerator)/Dc(w.denominator)) for w,h in zip(ww,nodes))
        ref=sum(expq(-4*i*i-F(1,146)*i*i) for i in (-1,0,1))
        assert abs(val-ref)<Dc("1e-45")
        log["soft-node numerical checks"]+=1

for P in (0,1,20,80):
    for m in (1,3,17):
        for n in (1,3,16):
            K=64*(m+1)*(n+1)**3*(n+P+10)
            q=F(1,2**(K//(m*n**3)))
            assert (1+2*q/(1-q))**n-1 < F(1,2**(P+20))
            log["kernel Poisson bounds"]+=1
print("PASS unimodular soft Gaussian theta:",dict(log))
