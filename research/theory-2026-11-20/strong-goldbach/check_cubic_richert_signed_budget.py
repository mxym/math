#!/usr/bin/env python3
from fractions import Fraction as F
from math import factorial
from functools import lru_cache

def must(c,msg):
    if not c:raise ArithmeticError(msg)

def J(x): return F(x)
# Coordinates a (anchor), b,c smallest cofactor slots; remainder largest.
bands=[
 (J('.005'),J('.020'),J('.123'),J('.360'),J('.017')),
 (J('.020'),J('.050'),J('.114'),J('.349'),J('.073')),
 (J('.050'),J('.100'),J('.105'),J('.330'),J('.179')),
]
pad=J('.0005')
ones=[(1,0,0),(0,1,0),(0,0,1)]
Dvec=(-1,-1,-1)

def geom(box,k,u,w,eta,c):
    n=len(box)
    lo=[r[0] for r in box];hi=[r[1] for r in box]
    crow=[(i,tuple(int(j==i) for j in range(n))) for i in range(n)]
    # Discard boxes with no ordered cofactor representation.
    if any(lo[i]>hi[i+1] for i in range(1,n-1)):
        return True
    if lo[-1]>1-sum(lo):
        return True
    lD=max(u,lo[-1],1-sum(hi));hD=1-sum(lo)
    if lD>hD:return True
    # We compute all rank-two outside; 3 and 4 below.
    if k==3:
        pen=sum(max(0,1-v/w) for v in (hi[1],hD))
        W=1-pen/eta
        return 24*lo[0]*lo[1]*lD>=c*W
    mid=[(a+b)/2 for a,b in box];wid=[(b-a)/2 for a,b in box]
    a,b,t=mid;d=1-sum(mid)
    dvec=Dvec
    V=1
    g=[F(0),F(0),F(0)]
    rem=F(0)
    def add(X,vec,sign):
        nonlocal V,rem
        v=1-2*X
        val=abs(v)**3
        der=-6*v*abs(v)
        V+=sign*val
        for h in range(3):g[h]+=sign*der*vec[h]
        if sign<0:
            radius=sum(abs(vec[h])*wid[h] for h in range(3))
            rem+=12*(abs(v)+2*radius)*radius**2
    for x,v in zip((a,b,t,d),(*ones,dvec)):add(x,v,-1)
    for x,v in zip((b,t,d),(ones[1],ones[2],dvec)):
        add(a+x,tuple(ones[0][h]+v[h] for h in range(3)),1)
    V-=c
    for x,v in zip((b,t,d),(ones[1],ones[2],dvec)):
        q=1-x/w
        if q>0:
            V+=c*q/eta
            for h in range(3):g[h]-=c*v[h]/(w*eta)
    return V-rem-sum(abs(m)*r for m,r in zip(g,wid))>0

def certify(k,a,b,u,w,eta,c):
    lo=a-pad;hi=b+pad;u0=u-pad; w0=w-J('.001')
    must(k in (3,4),'right rank')
    if k==3:
        base=((lo,hi),(u0,(1-lo)/2))
    else:
        base=((lo,hi),(u0,(1-lo)/3),(u0,(1-lo-u0)/2))
    todo=[(base,0)]
    n=0;maxd=0
    while todo:
        box,depth=todo.pop()
        n+=1;maxd=max(maxd,depth)
        if geom(box,k,u0,w0,eta,c):
            continue
        must(depth<42,('unverified box',k,box))
        i=max(range(len(box)),key=lambda i:box[i][1]-box[i][0])
        a,b=box[i];m=(a+b)/2
        todo+=[(box[:i]+((a,m),)+box[i+1:],depth+1),
               (box[:i]+((m,b),)+box[i+1:],depth+1)]
    return n,maxd

def logs(r,K=90):
    # After power-of-two reduction all transformed arguments <=1/3.
    def ln_norm(v):
        z=(v-1)/(v+1)
        f=sum((2*z**(2*i+1)/(2*i+1) for i in range(K)), F(0))
        return f,f+2*z**(2*K+1)/((2*K+1)*(1-z*z))
    l2,u2=ln_norm(F(2))
    e=0
    while r>=2:
        r/=2;e+=1
    lo,hi=ln_norm(r)
    return lo+e*l2,hi+e*u2
jl,ju=logs(F(7,5));jl-=J('.1408');ju-=J('.1408')
lb=F(0)
for a,b,u,w,c in bands:
    D=J('.499')-b
    eta=4-(1-a+J('.001'))/w
    must(2<D/u<4 and 0<(D-w)/u<(D-u)/u<3 and eta>0 and b<u,'sieve rail')
    must(1-(1-2*(a-pad))**3>c,'rank two score')
    print('certified profile boxes',a,b,certify(3,a,b,u,w,eta,c),certify(4,a,b,u,w,eta,c))
    A0,A1=logs(D/u-1)
    C0,C1=logs(w/u)
    H0,H1=logs((D-u)/(D-w))
    blo=A0/D-(C1/D+(1/D-1/w)*H0)/eta
    must(blo>0,'lower Richert bracket')
    lb+=jl*2*blo*logs(b/a)[0]*c
must(lb>J('.0679775'),'strict favorable rational endpoint')

# Signed angular coefficients at k=6,8 by rigorous monotone integration.
def atan(u,n=14):
    def series(x,n):
        p=sum(((-1)**j*x**(2*j+1)/(2*j+1) for j in range(n)),F(0))
        q=p+(-1)**n*x**(2*n+1)/(2*n+1)
        return (min(p,q),max(p,q))
    a0,a1=series(F(1,5),14);b0,b1=series(F(1,239),6)
    pi0,pi1=16*a0-4*b1,16*a1-4*b0
    if u<=F(1,2):return series(u,n)
    if u<=2:
        lo,hi=series((u-1)/(u+1),n)
        return pi0/4+lo,pi1/4+hi
    lo,hi=series(1/u,n)
    return pi0/2-hi,pi1/2-lo

pi0,pi1=2*atan(F(2**20))[0],2*atan(F(2**20))[1]+F(2,2**20)
def angle_abs(k):
    lo=F(0)
    hi=F(1,4)**(k-3)/(k-3)+(pi1/2)**k/(3*128**3)
    for e in range(-2,7):
        for i in range(64):
            a= F(2)**e*(1+F(i,64));b=F(2)**e*(1+F(i+1,64))
            I=(a**-3-b**-3)/3
            L=atan(a)[0]**k*I;H=atan(b)[1]**k*I
            lo+=F((L*(1<<40)).__floor__(),1<<40)
            hi+=F((H*(1<<40)).__ceil__(),1<<40)
    return 3/pi1*2**k/factorial(k)*lo,3/pi0*2**k/factorial(k)*hi

a6,b6=angle_abs(6);a8,b8=angle_abs(8)
must(b6<J('.0405'),'rank6 angular <.0405')
D6=J('4.8')*ju*b6
must(D6<J('.0374801'),'strict rank-six rational endpoint')
must(lb-D6-J('.0073')>J('.02319'),'strict combined rational endpoint')
tail_lo=a8*(1-pi1*pi1/F(90));tail_hi=b8
dyad_lo=(5-tail_hi)*jl;dyad_hi=(5-tail_lo)*ju
must(J('.9778264')<dyad_lo<dyad_hi<J('.9779012'),'strict dyadic rational endpoints')
print(f'favorable>{float(lb):.9f}, rank6<{float(D6):.9f}, net>{float(lb-D6-J(".0073")):.9f}, dyadic mean ({float(dyad_lo):.9f},{float(dyad_hi):.9f})')
