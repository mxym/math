"""Finite labeled prime fixtures, exact data and anchors. No factoring solver."""
from math import gcd,isqrt,prod
from fractions import Fraction as Q

def prime(n):return n>=2 and all(n%i for i in range(2,isqrt(n)+1))
def val(n,p):
    d=0
    while n%p==0:d+=1;n//=p
    return d
def block(N,T,r):
    b,a=r.numerator,r.denominator
    nb,ta=N**b,T**a
    j=gcd(nb,ta)
    return N//gcd(N,pow((nb//j)*(ta//j),N.bit_length(),N))
def mul_linear(c,x):
    h=[0]*(len(c)+1)
    for i,y in enumerate(c):h[i]-=x*y;h[i+1]+=y
    return h
def interp(pts):
    # Standard Lagrange for F-z^t, only for individually known singleton values.
    t=len(pts);out=[Q(0)]*(t+1);out[t]=1
    for x,v in pts:
        c=[Q(1)];di=Q(1)
        for y,u in pts:
            if y!=x:c=mul_linear(c,y);di*=x-y
        for j,w in enumerate(c):out[j]+=(v-x**t)*w/di
    return out

# Templates give (parent type, edge multiplier, multiplicity), with a root marker.
cases=[
 ("quartic",(1013,1103,1451,1481),[(None,0,1),(0,2,2),(0,6,3)],9),
 ("joint-hull",(13883,14153,14303,15791),[(None,0,1),(0,2,2),(0,6,2),(0,12,3)],14),
 ("crossing",(382069,421831,941249,1221113,1606859),
  [(None,0,1)]+[(0,m,e) for m,e in zip((210,420,630,840,1050,1260),(2,3,3,4,4,2))],5300),
 ("depth-two",(41,89),[(None,0,1),(0,2,2),(1,2,3)],9)]
for name,roots,spec,A in cases:
    t=len(roots);ac=[];deg=[0]*len(spec)
    for par,m,e in spec:
        if par is None:ac.append((1,0))
        else:
            a,b=ac[par];ac.append((m*a,m*b+1));deg[par]+=1
    trees=[[a*x+b for a,b in ac] for x in roots]
    ss=[q for tr in trees for q in tr]
    assert len(ss)==len(set(ss)) and all(prime(p) for p in ss) and max(ss)<=A*min(ss)
    edges={(tr[par],tr[i]) for tr in trees for i,(par,m,e) in enumerate(spec) if par is not None}
    assert {(p,q) for p in ss for q in ss if (q-1)%p==0}==edges
    N=prod(p**e for tr in trees for p,(_,_,e) in zip(tr,spec))
    T=prod((p-1)*p**(e-1) for tr in trees for p,(_,_,e) in zip(tr,spec))
    C=prod(m for par,m,e in spec if par is not None)**t
    U=T//gcd(T,N);Y=U//gcd(U,pow(N,N.bit_length(),U))
    assert Y==C*prod(p-1 for p in roots)
    assert U//Y==prod(p**(d-1) for tr in trees for p,d in zip(tr,deg) if d>0)
    coeff=[1]
    for x in roots:coeff=mul_linear(coeff,x)
    F=lambda z:sum(v*z**i for i,v in enumerate(coeff))
    assert (-1)**t*F(1)==Y//C
    groups={}
    for j,(par,m,e) in enumerate(spec):
        a,b=ac[j];xi=-Q(b,a);mval=(-1)**t*a**t*F(xi)
        assert mval==prod(tr[j] for tr in trees) and mval>0
        r=Q(e-1+deg[j],e)
        assert all(Q(val(T,tr[j]),e)==r for tr in trees)
        groups.setdefault(r,[]).append((mval,e,xi))
    for r,grp in groups.items():assert block(N,T,r)==prod(y**e for y,e,xi in grp)
    print(name,"support",len(ss),"directed edges",len(edges),"profile block sizes",sorted(len(x) for x in groups.values()))
    if name=="quartic":
        pts=[(xi,F(xi)) for g in groups.values() for y,e,xi in g]+[(Q(1),Q(Y,C))]
        assert interp(pts)==coeff==[2401084414609,-7823175944,9470382,-5048,1]
        assert (N.bit_length(),Y,C)==(286,49626861318144000,20736)
        print("quartic bitlength, saturated numerator, slopes",N.bit_length(),Y,C)
    if name=="depth-two":
        assert C==16 and prod(a for a,b in ac)**t==64 and Y==16*40*88
