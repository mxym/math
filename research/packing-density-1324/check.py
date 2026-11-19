#!/usr/bin/env python3
"""Exact interval certificate for the scalar inequalities in the Bellman proof."""
from fractions import Fraction as Q
def need(b,m):
    if not b:raise ValueError(m)
S=10**12
class I:
    __slots__=('a','b')
    def __init__(self,x,y=None):
        x=Q(x)*S;y=x if y is None else Q(y)*S
        self.a=x.numerator//x.denominator;self.b=-((-y.numerator)//y.denominator)
    @classmethod
    def raw(cls,a,b):
        k=object.__new__(cls);k.a=a;k.b=b;return k
    def __add__(x,y):
        if not isinstance(y,I): y=I(y)
        return I.raw(x.a+y.a,x.b+y.b)
    __radd__=__add__
    def __neg__(x):return I.raw(-x.b,-x.a)
    def __sub__(x,y):return x+-y
    def __rsub__(x,y):return y+-x
    def __mul__(x,y):
        if not isinstance(y,I):y=I(y)
        v=(x.a*y.a,x.b*y.b,x.a*y.b,x.b*y.a)
        return I.raw(min(v)//S,-((-max(v))//S))
    __rmul__=__mul__
    def __pow__(x,k):
        if k==0:return I(1)
        return x*(x**(k-1))
    def __repr__(x):return f'[{x.a/S:.12g},{x.b/S:.12g}]'
def boxes(a,b,n):
    d=Q(b-a,n)
    for j in range(n):yield I(a+j*d,a+(j+1)*d)
A=Q(7,20);B=Q(81,200)
D=I('-.151','-.147');DD=I('0','.04');g0=I('.1546','.1548')
def checks(ta,y,kind):
    g=g0+(ta*y)*D; H1=3*y**2*g+ta*y**3*D+(1-ta)*(1-y)*(1-3*y)
    if kind=='left':return H1.a>0
    if kind=='right':return H1.b<0
    if kind=='far':
        # Lower bound on [G(t)-H(t,y)]/(1-y) for y<1.
        gap=(1+y+y**2)*(g0+ta*D)+y**3*ta*D-(1-ta)*y*(1-y)
        return gap.a>0
    H2=6*y*g+6*ta*y**2*D+ta**2*y**3*DD+(1-ta)*(6*y-4)
    Ht=y**4*D-y*(1-y)**2
    Hty=4*y**3*D+ta*y**4*DD-(1-y)*(1-3*y)
    # Htt>=0.  Htt-Hty²/Hyy < .04 by Hyy < -1/3.
    return 3*H2.b< -S and Ht.a>=D.a and Ht.b<=D.b and (y**5*DD+3*Hty**2).b<DD.b
def bell():
    need(3*(1+Q(1546,10000))**2<4<3*(1+Q(1548,10000))**2,'g(0) bounds')
    for k,(u,v) in dict(left=(Q(0),A), core=(A,B), right=(B,Q(7,10)),far=(Q(7,10),Q(1))).items():
        # recursively bisect widest active span; arbitrary real inputs covered
        visit=0
        def go(tl,th,yl,yh):
            nonlocal visit
            visit+=1
            if checks(I(tl,th),I(yl,yh),k):return
            need(max(th-tl,yh-yl)>Q(1,1<<20),('unresolved',k,tl,th,yl,yh))
            if th-tl>yh-yl:
                m=(th+tl)/2;go(tl,m,yl,yh);go(m,th,yl,yh)
            else:
                m=(yh+yl)/2;go(tl,th,yl,m);go(tl,th,m,yh)
        go(Q(0),Q(1,2),u,v);print(k,'boxes',visit)
def center():
    t=Q(61,200);y=Q(3,8)
    s=sum((t*y**i*(1-y))**2*(t*y**(i+1))*(1-t*y**i) for i in range(3))
    need(12*(2*s+t*t*(1-2*t)**2)>Q(244,1000),'finite competitor')
    al,be=Q(1548,10000),Q(147,1000)
    # Sum s=l+r; product P=lr in [max(0,(s-.5)/2),s²/4].
    count=0
    def go(lo,hi):
        nonlocal count
        count+=1
        # Upper constant and linear coefficient; keep negative quadratic exactly, maximize it.
        C=al*hi**3-be*lo**4
        A=(1-lo)**2-3*al*lo+4*be*hi**2
        p=max(Q(0),(lo-Q(1,2))/2,min(A/(4*be),hi**2/4))
        if 12*(C+A*p-2*be*p*p)<Q(244,1000):return
        need(hi-lo>Q(1,1<<25),('unresolved center',lo,hi))
        m=(hi+lo)/2;go(lo,m);go(m,hi)
    go(Q(0),Q(58,100));go(Q(642,1000),Q(1))
    m=Q(6)*al
    # max(linear minus quadratic), plus separate t^3 term at t=1/2.
    curv=m*m/(4*12*be)+Q(4,100)*Q(1,8)
    need(curv<Q(128,1000)<(1-Q(642,1000))**2,'transverse curvature')
    for t in (Q(29,100),Q(321,1000)):
        need(2*curv+2-24*t+48*t*t< -Q(2,5),'axial curvature')
    print('center localization intervals',count,'; tail curvature upper',curv)
if __name__=='__main__':bell();center()
