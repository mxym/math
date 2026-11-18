"""Stdlib-only exact audit, not based on the Sylvester determinant in the first verifier."""
from fractions import Fraction as F
def ck(x,s):
    if not x: raise ArithmeticError(s)
def val(c,x):
    z=0
    for a in reversed(c):z=z*x+a
    return z
def divrem(c,d):
    n=list(c); m=len(d)
    while len(n)>=m:
        j=len(n)-m; z=F(n[-1],d[-1])
        for i,b in enumerate(d):n[j+i]-=b*z
        while n and not n[-1]:n.pop()
    return n
def sturm(c):
    chain=[c,[i*c[i] for i in range(1,len(c))]]
    while True:
        r=divrem(chain[-2],chain[-1])
        if not r: return chain
        chain.append([-a for a in r])
def variations(polys,t):
    signs=[v>0 for v in [val(poly,t) for poly in polys] if v]
    return sum(a!=b for a,b in zip(signs,signs[1:]))
J=[-139,-5378,39133,-86528,65536]
Q=[-3,22,-3,-28,16]
B=[713,-266,-1081,2426,1729,-2068,-1216,448,256]
def pof(w):return (1+2*w-w**3)/4
for w in map(F,range(-6,7)): # degree at most 12 throughout
    p=pof(w);x=4*p-1;r=(w-w**3)/4; a=2*p-4*p*p;P=p*(1-p)
    C=a+x*r-4*r*r
    ck(w==x-4*r and p-r==(1+w)/4,'parametrization')
    ck(C==(1-w*w)**3/4 and C*(x-8*r)==16*r**3,'stationarity')
    D=(P+r*r)**2-(p-r)*(1-p+r)*C
    ck(256*D==(1+w)**2*val(Q,w),'diagonal feasibility')
    ck(16*val(J,p)==val(Q,w)*val(B,w),'p eliminant')
for poly,lower,upper,count in ((J,0,F(1,4),0),(J,F(1,4),F(1,3),1),(Q,F(-5,8),0,0),(Q,0,F(1,6),1)):
    cc=sturm(poly)
    ck(variations(cc,lower)-variations(cc,upper)==count,'Sturm count')
lo=F(0);hi=F(1,6)
for _ in range(80):
    m=(lo+hi)/2
    if val(Q,m)<0:lo=m
    else:hi=m
ck(F(32053506,10**8)<pof(lo)<pof(hi)<F(32053508,10**8),'p root bracket')
ck(val(Q,F(1,6))>0 and 16*F(5,8)**3+28*F(5,8)**2<22 and 22-84*F(1,3)**2-6*F(1,3)>0,'coarse sign estimates')
print('PASS: signed critical-branch parametrization, factorization of true feasibility, and quartic in p checked exactly.')
print('PASS: four independent Sturm counts; rational bisection of the w root produces 0.32053506 < p0 < 0.32053508.')
