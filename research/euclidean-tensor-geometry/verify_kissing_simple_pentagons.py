#!/usr/bin/env python3
"""Exact algebra for three rotating pentagons; standard Python, no numeric optimizer."""
from fractions import Fraction as F
class K:
    def __init__(self,a=0,b=0):
        if isinstance(a,K):self.a,self.b=a.a,a.b
        else:self.a,self.b=F(a),F(b)
    def __add__(self,x):x=K(x);return K(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self):return K(-self.a,-self.b)
    def __sub__(self,x):return self+-K(x)
    def __rsub__(self,x):return K(x)+-self
    def __mul__(self,x):
        x=K(x);return K(self.a*x.a+5*self.b*x.b,self.a*x.b+self.b*x.a)
    __rmul__=__mul__
    def __truediv__(self,x):
        x=K(x);y=self*K(x.a,-x.b);q=x.a*x.a-5*x.b*x.b
        return K(y.a/q,y.b/q)
    def __rtruediv__(self,x):return K(x)/self
    def __pow__(self,n):
        if n<0:return (1/self)**(-n)
        u=K(1)
        for _ in range(n):u*=self
        return u
    def sign(self):
        a,b=self.a,self.b
        if not b:return (a>0)-(a<0)
        if not a:return (b>0)-(b<0)
        if (a>0)==(b>0):return 1 if a>0 else -1
        v=a*a-5*b*b
        return ((v>0)-(v<0))*(1 if a>0 else -1)
    def __eq__(self,x):x=K(x);return self.a==x.a and self.b==x.b
    def __lt__(self,x):return (self-x).sign()<0
    def __le__(self,x):return (self-x).sign()<=0
    def __gt__(self,x):return (self-x).sign()>0
    def __ge__(self,x):return (self-x).sign()>=0
def require(x):
    if not x: raise RuntimeError('algebraic certificate failed')
D5=K(0,1);C=(1+D5)/4;S2=1-C**2;b=2*S2;D=2*b-1;z=C-b
require(0<z<1 and 0<D<1 and b>0)
# Coefficients of (1+u^2)^2 times the necessary comparison gap.
a0=4*z*z-2*D*(D+b-1);a2=4*S2-8*z*b-4*D*(D+b);a4=4*b*b-2*D*(D+b+1)
require(a0==0 and (8*z)**2*S2>F(55,100)**2 and a2>F(-92,100))
require((8*b)**2*S2<F(326,100)**2 and a4>0)
U=F(27,100)
require((2-U)**2<3 and F(55,100)-F(92,100)*U-F(326,100)*U**2>0)
# r is the moving radius and H the norm of an unscaled fixed footpoint.
r2=1/(4*S2);H2=1-r2;cos72=2*C*C-1;A2=H2*cos72*cos72
require(r2==K(F(1,2),F(1,10)) and H2>0)
require(A2+F(1,4)==H2 and H2*cos72==r2*C-F(1,2))
require(A2-F(1,4)+r2==F(1,2))
require(r2*cos72+H2==F(1,2))
# regular fixed hexagon at phase 30 degrees: closest angle is 18 degrees.
require(H2*(1+C)/2==F(1,4))
# fixed D3/D4 directions: (A+1/2)/sqrt(2) and H/sqrt(2) < 1/2.
require(F(1,4)-A2>0 and (F(1,4)-A2)**2>A2 and H2<F(1,2))
# Equality Gram rank in scaled fixed space, repeated phase first.
e=1-b;require(D-e>0 and D*(D-e)==2*z*z and D+e>0)
print('PASS golden-ratio quartic, strict phase gap, rigid rank-two footpoint Gram, and 15-point construction')
