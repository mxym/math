"""Exact independent finite-spectrum checker. No external packages; do not rely on asserts."""
from collections import Counter
from fractions import Fraction as Q
from math import isqrt
from decimal import Decimal as Dec, localcontext
def must(v,msg):
    if not v: raise ValueError(msg)
x,y,t=Q(1,12),Q(5,6),Q(1,60)
# Each block is a I + b Z + sqrt(3)c X; d the scalar flag.
states=[(x+t,0,0,y-2*t),(x-t,0,0,y+2*t),(x,t,0,y),(x,-t/2,t/2,y),(x,-t/2,-t/2,y)]
weights=[3,3,-2,-2,-2]
def sqrtq(x):
    a,b=isqrt(x.numerator),isqrt(x.denominator)
    must(a*a==x.numerator and b*b==x.denominator,'irrational test radius')
    return Q(a,b)
def spectrum(v):
    a,b,c,d=map(Q,v);r=sqrtq(b*b+3*c*c)
    return a-r,a+r,d
def mid(i,j):
    return tuple((Q(a)+Q(b))/2 for a,b in zip(states[i],states[j]))
must(sum(weights)==0,'contrast')
for s in states:
    spec=spectrum(s);must(sum(spec)==1 and min(spec)>0,'state')
ub,fb=Counter(),Counter()
for i,ci in enumerate(weights):
    for j,cj in enumerate(weights):
        a,b,f=spectrum(mid(i,j))
        ub.update({a:ci*cj});ub.update({b:ci*cj});fb.update({f:ci*cj})
coeffs=[1,-4,6,-4,1]
must(ub==Counter({x+j*t/2:-6*c for j,c in zip(range(-2,3),coeffs)}),'upper stencil')
must(fb==Counter({y+j*t:9*c for j,c in zip(range(-2,3),coeffs)}),'flag stencil')
must((y-2*t)/(x+t)==8 and Q(3,8)*8**2>9,'all-order curvature certificate')
for k in range(5):
    a=sum(v*z**k for z,v in ub.items());b=sum(v*z**k for z,v in fb.items())
    if k<4:must(a==b==0,'moment cancel')
    else:must(a==-6*24*(t/2)**4 and b==9*24*t**4,'fourth moment')
print("PASS: five faithful rational-spectral qutrits; 25 ordered midpoints; both integer stencils; 8^2>24.")
def D(z):return Dec(z.numerator)/Dec(z.denominator)
with localcontext() as ctx:
    ctx.prec=75
    for q in map(Dec,('0.1','0.5','0.9','1','1.5','1.99')):
        def negent(v):
            if q==1:return sum(z*z.ln() for z in v)
            return sum(z**q for z in v)/(q-1)
        gap=-sum(Dec(c*d)*negent(tuple(D(z) for z in spectrum(mid(i,j)))) for i,c in enumerate(weights) for j,d in enumerate(weights))
        must(gap>0,'numerical sample-only test')
        print('Tsallis diagnostic: q=',q,'quadratic form=',f'{gap:.8E}')
    for q in map(Dec,('0.1','0.5','0.9')):
        eps=Dec('1e-60')
        g=Dec(0)
        for i,c in enumerate(weights):
            for j,d in enumerate(weights):
                a,b,_=map(D,spectrum(mid(i,j)))
                h=(eps*a)**q+(eps*b)**q+(1-eps*(a+b))**q
                g+=Dec(c*d)*h.ln()/(1-q)
        must(g>0,'Renyi numerical sample-only test')
        print('Renyi diagnostic: q=',q,'gap divided by epsilon^q=',f'{g/(eps**q):.8E}')

