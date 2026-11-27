#!/usr/bin/env python3
"""Exact Fourier/Gram certificates. Standard library only. No SDP solver or floats."""
import json,math,sys
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
D=10**12
Q=10**24
# pi/4 = atan(1/2)+atan(1/3), by the addition law and the first quadrant.
def atan_box(q):
    s=sum((F((-1)**i,(2*i+1)*q**(2*i+1)) for i in range(60)),F())
    return s,s+F(1,121*q**121)
p=F(314159265358979323846264338327,10**29)
L,H=atan_box(2); l,h=atan_box(3)
assert p<4*(L+l)<4*(H+h)<p+F(1,10**29)
@lru_cache(None)
def table(m):
    assert 3<=m<=10**8
    # Rounded complex rotation; component error at most 2/Q after floor.
    z=2*p/m; T=F(1); C=F(1); S=F(0)
    for j in range(1,43):
        T*=z/j
        if j%4==0:C+=T
        if j%4==1:S+=T
        if j%4==2:C-=T
        if j%4==3:S-=T
    assert z**43/math.factorial(43)+2*F(1,10**29)/m<F(1,Q)
    a,b=(v.numerator//v.denominator for v in (Q*C,Q*S))
    x,y=Q,0; boxes=[(Q,Q)]
    for j in range(1,m//2+1):
        x,y=(a*x-b*y)//Q,(a*y+b*x)//Q
        # True rotation preserves norm. Approximate rotation differs in
        # operator 2-norm by <3/Q; rounded vector has norm <=2 by induction;
        # floor costs <2/Q. Therefore error increases by <8/Q per step.
        boxes.append((max(-Q,x-8*j),min(Q,x+8*j)))
    return boxes
def at(m,j):
    j%=m; return table(m)[min(j,m-j)]
def dyadic(m):
    assert m>1 and not(m&(m-1))
    t=[(Q,Q),(-Q,-Q)]; h=2
    while h<m:
        w=[(math.isqrt(Q*(Q+x)//2),min(Q,math.isqrt(Q*(Q+y)//2)+1)) for x,y in t]
        # cos(theta/2)>=0 on [0,pi]. The second half follows by reflection.
        t=w+[(-hi,-lo) for lo,hi in reversed(w[:-1])];h*=2
    return t
def universal(ys,B):
    assert all(isinstance(j,int) and 2<=j<=222 and isinstance(w,int) and w>0 for j,w in ys)
    assert len(set(j for j,w in ys))==len(ys)
    m=2**18; t=dyadic(m); lo=[x for x,y in t]; t=lo+lo[-2:0:-1]
    assert len(t)==m
    M=D+sum(j*j*w for j,w in ys) # D times an upper bound for |P''(theta)|
    b=min(D*t[i]+sum(w*t[i*j%m] for j,w in ys) for i in range(m//2+1))
    # Interpolating symmetrically between adjacent endpoints loses at most
    # M (2*pi/m)^2 / 8, where pi<22/7 follows from the bounds above.
    v=2*b+(2*B-sum(w for j,w in ys))*Q
    assert p+F(1,10**29)<F(22,7) and v*49*m*m>M*Q*484
def discrete(m,ws,B):
    assert all(isinstance(j,int) and 1<=j<m and isinstance(y,int) and y>=0 for j,y in ws)
    for k in range(m//2+1):
        t=2*D*at(m,k)[0]+(2*B-sum(y for j,y in ws))*Q
        assert t+2*sum(y*at(m,k*j)[0] for j,y in ws)>0,(m,k,B)
def witness(m,W,den,cycle_floor,limit_floor):
    assert all(0<=k<=m//2 and isinstance(w,int) and w>=0 for k,w in W)
    assert sum(w for k,w in W)<=den
    for j in range(1,m//2+1):
        ub=sum(w*at(m,k*j)[1] for k,w in W)
        assert 2*ub<=den*Q
        if j==1: a=F(-ub,den*Q)
    assert a>cycle_floor
    # Convolution with a uniform arc [-2/m,2/m]; all nonzero multiples
    # of m have |sinc(2j)|<=1/2, all negative sidelobes have magnitude
    # <=1/pi. First factor sinc(2/m)>=1-2/(3m^2).
    assert a*(1-F(2,3*m*m))>limit_floor
class I:
    def __init__(self,l,h=None):
        if isinstance(l,I): self.l,self.h=l.l,l.h
        else: self.l,self.h=F(l),F(l if h is None else h)
    def __add__(a,o): b=I(o);return I(a.l+b.l,a.h+b.h)
    __radd__=__add__
    def __neg__(a):return I(-a.h,-a.l)
    def __sub__(a,o):return a+-I(o)
    def __rsub__(a,o):return -a+o
    def __mul__(a,o):
        b=I(o);s=[x*y for x in (a.l,a.h) for y in (b.l,b.h)];return I(min(s),max(s))
    __rmul__=__mul__
    def __truediv__(a,o):
        b=I(o);assert b.l*b.h>0;return a*I(1/b.h,1/b.l)
def fifteen():
    def R(k):
        lo,hi=at(15,k);return I(F(lo,Q),F(hi,Q))
    t=F(2,3)*(1-R(3))/(R(1)+F(1,2))
    assert t.l>F(3,10) and t.h<F(1,3)
    def c(j):return (F(1,3)-t)*R(5*j)+F(2,3)*R(6*j)+t*R(7*j)
    for j in [1,3,4,6,7]:assert c(j).h<F(1,2)
    assert -c(1).h>F(861833162549,10**12) and -c(1).l<F(861833162551,10**12)
    u=(R(5)-R(7))/(R(14)-R(10));v=(R(5)-R(6)+u*(R(10)-R(12)))/(R(30)-R(25))
    assert u.l>0 and v.l>0
    C=-R(5)-u*R(10)-v*R(25)
    for k in range(5):assert (C+R(k)+u*R(2*k)+v*R(5*k)).l>F(2337,10000)
    K=range(5,11)
    assert max(sum((k+l)%15==h for k in K for l in K if k<=l) for h in range(15))==3
def path_dual(n,row):
    q=row['q']; T=row['T']
    assert len(q)==n*(n+1)//2 and all(isinstance(v,int) and v>=0 for v in q)
    ids=iter(q); a=[[0]*n for i in range(n)]
    for i in range(n):
        for j in range(i,n):a[i][j]=a[j][i]=next(ids)
    e=sum(a[i][i+1] for i in range(n-1))
    u=sum(a[i][i] for i in range(n))+sum(a[i][j] for i in range(n) for j in range(i+2,n))
    assert e>0 and u*10**8<2*e*T
    # Exact positive definiteness from consecutive leading principal minors
    # using fraction-free symmetric Gaussian elimination, without pivoting.
    prev=1
    for k in range(n):
        piv=a[k][k]; assert piv>0
        for i in range(k+1,n):
            for j in range(i,n):
                num=piv*a[i][j]-a[i][k]*a[k][j]
                v,rem=divmod(num,prev);assert not rem
                a[i][j]=a[j][i]=v
        prev=piv
def check(data):
    ys=data['upper']['ys'];B=862073192000
    assert data['upper']['B']==B and len(ys)==25 and max(j for j,y in ys)==222
    universal(ys,B)
    E={n for j,w in ys for n in range(3,j+1) if j%n==0}
    assert len(E)==49 and E==set(map(int,data['exceptions']))
    for n in E:discrete(n,data['exceptions'][str(n)],B)
    for n in range(3,133):
        if n==15:continue
        discrete(n,data['finite'][str(n)],861832000000 if n<=21 else 862072537000)
    assert {int(n):v['T'] for n,v in data['paths'].items()}=={11:86213905,16:86209333,21:86208089,31:86207487,41:86207419}
    for n,v in data['paths'].items():path_dual(int(n),v)
    fifteen()
    w=data['lower'];assert w['m']==1201
    witness(1201,w['W'],10**11,F(8620731,10**7),F(86207271,10**8))
    assert [(w['m'],w['floor'],w['smooth']) for w in data['long']]==[(4099,862073128190,862073093984)]
    for w in data['long']:witness(w['m'],w['W'],10**13,F(w['floor'],10**12),F(w['smooth'],10**12))
    print('Certified strict all-length and finite cycle duals, all primal witnesses, the rigid 15-cycle and finite path matrices.')
if __name__=='__main__':
    check(json.loads((Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('kissing-antipodal-cycle-data.json')).read_text()))
