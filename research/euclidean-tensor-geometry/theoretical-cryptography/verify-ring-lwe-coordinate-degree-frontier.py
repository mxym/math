"""Exact small-model checks and a Stirling-window sanity check.

Synthetic algebra only. This program does not take instances or compute labels
that optimize likelihood. The finite checks are not substitutes for the proof.
"""
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import product
from random import Random

def mul(x,y,q):
    d=len(x); z=[0]*d
    for i,a in enumerate(x):
        for j,b in enumerate(y):
            z[(i+j)%d]+=(-1 if i+j>=d else 1)*a*b
    return tuple(v%q for v in z)

def bar(x,q):
    return x[:1]+tuple(-x[j]%q for j in range(len(x)-1,0,-1))

def add(x,y,q):
    return tuple((a+b)%q for a,b in zip(x,y))

def coeff_spectrum(q,A,I,w):
    d=len(A[0]); N=d*len(A)
    V=tuple(product(range(q),repeat=d))
    S=[s for s in V if tuple(s[j] for j in I)==w]
    B=[bar(a,q) for a in A]
    sums=[0]*(N+1)
    for full in product(range(q),repeat=N):
        length=sum(x!=0 for x in full)
        v=(0,)*d
        for i,b in enumerate(B):
            v=add(v,mul(b,full[i*d:(i+1)*d],q),q)
        if all(v[j]==0 for j in range(d) if j not in I):
            sums[length]+=1
    # Independently integrate pairs of conditional scalar densities under the
    # uniform reference and expand by subsets of scalar response positions.
    phases=[tuple(z for a in A for z in mul(a,s,q)) for s in S]
    pair=[0]*(N+1)
    for p in phases:
        for p2 in phases:
            row=[1]+[0]*N
            for j,(u,v) in enumerate(zip(p,p2),1):
                x=q*int(u==v)-1
                for k in range(j,0,-1):
                    row[k]+=row[k-1]*x
            for k in range(N+1):
                pair[k]+=row[k]
    assert [Fraction(a,len(S)**2) for a in pair]==sums
    return N+1

rng=Random(697125)
spectra=0
for q in (3,9):
    V=list(product(range(q),repeat=2))
    Aset=list(product(V,repeat=2)) if q==3 else [tuple(rng.choices(V,k=2)) for _ in range(9)]
    for A in Aset:
        for I in ((), (0,), (1,)):
            for w in [()] if not I else [(0,),(q-1,)]:
                spectra+=coeff_spectrum(q,A,I,w)

# A fixed dimension-four Hensel lift modulo nine.
# (X^2+4X+8)(X^2-4X+8)=X^4+1 in (Z/9)[X].
def rem(v,a):
    z=list(v)
    for k in (3,2):
        lead=z[k]
        z[k-1]-=lead*a
        z[k-2]-=lead*8
    return tuple(x%9 for x in z[:2])
def poly_mul(P,Q):
    L=[0]*(len(P)+len(Q)-1)
    for i,p in enumerate(P):
        for j,q in enumerate(Q):
            L[i+j]+=p*q
    return L
ideals=shells=0
V4=list(product(range(9),repeat=4))
R4=[(v,rem(v,4),rem(v,-4)) for v in V4]
for e,f in product(range(3),repeat=2):
    J=[v for v,a,b in R4 if all(x%3**e==0 for x in a) and all(x%3**f==0 for x in b)]
    divisor=3**max(e,f)
    H=[v for v in V4 if all(x%divisor==0 for x in v)]
    assert len(J)==3**(2*(4-e-f)) and set(H)<=set(J)
    if J!=H:
        assert len(J)>=2*len(H)
    ck=lambda V: [sum(sum(x!=0 for x in v)==j for v in V) for j in range(5)]
    P=ck(J); Q=ck(H); E=[p-q for p,q in zip(P,Q)]
    assert E[:2]==[0,0] and min(E)>=0
    B=poly_mul(Q,[E[0]+1]+E[1:])
    assert all(a<=b for a,b in zip(P,B))
    for _ in range(4):
        P=poly_mul(P,ck(J));B=poly_mul(B,poly_mul(Q,[E[0]+1]+E[1:]))
        assert all(a<=b for a,b in zip(P,B))
        shells+=len(P)
    ideals+=1

pairs=0
for q in (3,9):
    V=list(product(range(q),repeat=2))
    # Fixed triangular two-column map on two uniform ring variables.
    for l in (0,1):
        U=((1,0),(3%q,2%q))
        F=((0,0),(0,1)) if l else ((0,0),(2,0))
        C=Counter((add(mul(U[0],a,q),mul(U[1],b,q),q),
                   mul(F[1],b,q)) for a,b in product(V,repeat=2))
        assert len(C)==len(V)**2 and set(C.values())=={1}
        pairs+=len(C)

with localcontext() as ctx:
    ctx.prec=60
    Dr=Decimal
    def root(u,t,a):
        T=(u-1)*t; B=a*Dr(u).ln()
        lo,hi=Dr(0),T
        for _ in range(105):
            w=(lo+hi)/2
            if w*(1+(T/w).ln())<B: lo=w
            else: hi=w
        return (lo+hi)/2
    ordering=0
    for q in (9,15,25,27,45,63,75,81,105,121,625):
        divisors=[x for x in range(2,q+1) if q%x==0]
        for a in (Dr(1),Dr('0.94')):
            t=Dr(q).ln()+Dr('0.2')
            first=root(divisors[0],t,a)
            assert all(first<root(u,t,a) for u in divisors[1:])
            ordering+=len(divisors)-1
    worst=Dr(0)
    for d in (4096,8192,16384):
        u,t,ell=3,Dr('2.4'),d//17
        a=1-Dr(ell)/d
        T=(u-1)*t
        alpha=root(u,t,a); J=(T/alpha).ln()
        base=alpha*d+Dr(d).ln()/(2*J)
        for k in (-2,0,1,4):
            D=int(base)+k
            # Finite binomial sum, choosing m = 12d^2/5 rounded down and b^2
            # to make T exactly the prescribed mean scale.
            m=12*d*d//5; N=m*d; lam=T/m
            term=Dr(u)**(ell-d); val=Dr(0)
            for r in range(1,D+1):
                term*=Dr(N-r+1)*lam/r
                val+=term
            expected=(J*(Dr(D)-base)).exp()/((1-(-J).exp())*
                     (2*Dr('3.14159265358979323846264338327950288419716939937510')*alpha).sqrt())
            worst=max(worst,abs(val/expected-1))
    assert worst<Dr('0.016')
print("PASS: conditional spectral rows, ideal types/shells, joint images, quotient orderings:",
      spectra,ideals,shells,pairs,ordering)
print("window sanity maximum relative discrepancy:", worst)
