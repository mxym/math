#!/usr/bin/env python3
"""Exact finite sanity checks; the continuum inequalities are proved in PROOF.md."""
from fractions import Fraction as Q
from itertools import product

def check(v):
    if not v:
        raise ArithmeticError("failed exact buyback check")

def fee(p):
    f, s = 2*p*p/(1+p*p), 2*p/(1+p*p)
    check(s*s == f*(2-f))
    return f, s

def calc(first, Y, Z, f):
    """Backward induction conditional on seeing the first value and direct offline max."""
    def g(x): return sum(p*max(x,z-f*x) for z,p in Z)
    v,w=g(first),g(0)
    accept=sum(p*max(v,g(y)-f*first) for y,p in Y)
    reject=sum(p*max(w,g(y)) for y,p in Y)
    M=sum(p*r*max(first,y,z) for y,p in Y for z,r in Z)
    return M, accept, reject

def check_all():
    witnesses=switches=grids=general=tails=0
    for p in sorted(set(Q(i,j) for j in range(2,22) for i in range(1,j))):
        f,s=fee(p); a=1+f; c=a*(1+s)/(1+3*f+a*s)
        T=2*f/(f+s); x=1+f/T; q=1/x; t=(1-T)/a
        M,V,W=calc(1,[(0,1-q),(x,q)],[(0,1-t),(a*x,t)],f)
        check(V==W==M*c); witnesses+=1
    for p in [Q(1,13),Q(2,9),Q(1,3),Q(2,3),Q(8,9)]:
        f,s=fee(p); a=1+f; c=a*(1+s)/(1+3*f+a*s)
        for h,T,j in product([f/2,f,2*f,Q(2,3),Q(5),Q(29,2)],
                             [Q(k,8) for k in range(1,9)], range(1,8)):
            D=T*j/7; x=1+h; e=min(h*T,f); q=D/(D+e)
            u=(T-D)/a; t=(1-T)/a
            Y=[(0,1-q),(x,q)]; Z=[(0,1-u-t),(a,u),(a*x,t)]
            M,V,W=calc(1,Y,Z,f)
            N=e*(f+D)+D*(max(f-h,0)*(T-D)+f*x*(1-T))
            B=e*(1-D+h*(1-T))+D*x
            check(V==W and a*(M/V-1)==N/B and V>=c*M)
            if h<=f: check(N-f*B==-(f-h)*D**2-f*h*h*T*(1-T))
            switches+=1
        for h,q,i,j in product([Q(1,15),Q(1,4),Q(1),Q(3)],
                              [Q(k,8) for k in range(9)], range(7), range(7)):
            if i+j>6: continue
            x=1+h; u,t=Q(i,6),Q(j,6)
            M,V,W=calc(1,[(0,1-q),(x,q)],[(0,1-u-t),(a,u),(a*x,t)],f)
            check(max(V,W)>=c*M); grids+=1
        # A separate set with both variables taking more than two values.
        for x1,x2,y1,y2 in product([Q(1,9),Q(1,2),Q(4,3),Q(8,5)],repeat=4):
            Y=[(x1,Q(1,4)),(x2,Q(1,3)),(Q(2),Q(5,12))]
            Z=[(0,Q(1,7)),(y1,Q(1,4)),(y2,Q(2,7)),(Q(3),Q(9,28))]
            M,V,W=calc(1,Y,Z,f); check(max(V,W)>=c*M); general+=1
        # Validate cap/round direction for 2-point Y and arbitrary Z.
        for x,q in product([Q(10,9),Q(4,3),Q(3,2),Q(7,2)],[Q(k,6) for k in range(7)]):
            Y=[(0,1-q),(x,q)]
            Z=[(0,Q(1,7)),(a/2,Q(1,4)),(a*(1+x)/2,Q(3,7)),(a*x+Q(5),Q(5,28))]
            M,V,W=calc(1,Y,Z,f); C=[(min(z,a*x),r) for z,r in Z]; m,v,w=calc(1,Y,C,f)
            check(M-m==V-v==W-w==sum(r*max(0,z-a*x) for z,r in Z))
            mass={0:Q(),a:Q(),a*x:Q()}
            for z,r in C:
                lo,hi=(0,a) if z<=a else (a,a*x)
                mass[lo]+=r*(hi-z)/(hi-lo); mass[hi]+=r*(z-lo)/(hi-lo)
            m1,v1,w1=calc(1,Y,mass.items(),f)
            check(m1>=m and v1==v and w1==w); tails+=1
    print("PASS: exact attaining instances =",witnesses)
    print("PASS: interior-switch identities =",switches)
    print("PASS: arbitrary activation/grid instances =",grids)
    print("PASS: additional multivalued instances =",general)
    print("PASS: cap/rounding comparisons =",tails)

if __name__=='__main__': check_all()
