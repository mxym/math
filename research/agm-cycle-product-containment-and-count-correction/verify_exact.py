#!/usr/bin/env python3
"""Exact rational function identities and saturated cycle eliminants."""
from math import isqrt
from sympy import Poly, QQ, cancel, diff, expand, factor, groebner, prod, rem, symbols, together

a,b,d,x,y,z,u,w=symbols("a b d x y z u w")
h=a*b
aa=(a+b)/2
dd=(a-b)/2
X=(x+h)**2/(4*x)
Y=y*(x*x-h*h)/(8*x*x)
Ysq=x*(x-a*a)*(x-b*b)*(x*x-h*h)**2/(64*x**4)

# Directly check the normalized map and its inverse-sign negative control.
assert cancel(X-aa**2-(x-a*a)*(x-b*b)/(4*x)) == 0
assert cancel(X-h-(x-h)**2/(4*x)) == 0
assert cancel(X*(X-aa**2)*(X-h)-Ysq) == 0
assert cancel(diff(X,x)/(2*Y)-1/y) == 0
assert cancel(diff(X,x)/(-2*Y)+1/y) == 0
assert cancel(aa**2-h-dd**2) == 0
assert cancel(diff(x/w**2,x)/(2*y/w**3)-w/(2*y)) == 0


def equal_mod_d_square(expr):
    numer=together(expr).as_numer_denom()[0]
    return rem(expand(numer),b*b-a*a+d*d,b)==0


xp=a*(a+d)
yp=d*xp
assert equal_mod_d_square(yp**2-xp*(xp-a*a)*(xp-b*b))
assert equal_mod_d_square(x*(x-b*b)-(a+d)**2*(x-a*a)-(x-xp)**2)
assert equal_mod_d_square(a*a*b*b/xp-a*(a-d))
assert equal_mod_d_square(-a*a*b*b*yp/xp**2+a*d*(a-d))
assert equal_mod_d_square(X.subs(x,xp)-aa*(aa+dd))
assert equal_mod_d_square(Y.subs({x:xp,y:yp})-aa*dd*(aa+dd))
assert cancel((2*z**3-z*z-1)-(z-1)*(2*z*z+z+1)) == 0
assert rem(8*z**6-5*z**3+1,2*z*z+z+1,z)==0
assert rem(z**3-(1-z)/4,2*z*z+z+1,z)==0

# Pure algebraic independent alternate route for small N:
# no addition law or isogeny map enters these lex eliminations.
def eliminant(n, distinct=False):
    vs=symbols("v0:"+str(n))
    eqs=[2*l*r*r-l*l-1 for l,r in zip(vs,vs[1:]+vs[:1])]
    # A cyclic solution with a v_i^4=1 is entirely singular: -1 next
    # forces +-sqrt(-1), either forces 0 in the next step; all v_i must
    # be nonzero by the equation itself, so only the all-ones tuple
    # survives among singular cyclic solutions. Thus v0 is sufficient.
    excluded=vs[0]**4-1
    if distinct:
        excluded*=prod(vs[i]-vs[j] for i in range(n) for j in range(i+1,n))
    G=groebner(eqs+[w-prod(vs),u*excluded-1],u,*vs,w,order="lex",domain=QQ)
    polys=[f.as_expr() for f in G.polys if f.as_expr().free_symbols <= {w}]
    assert len(polys)==1
    return Poly(polys[0],w,domain=QQ).monic()


degs=[]
for n in range(1,4):
    p=eliminant(n)
    D=1<<n
    B=isqrt(4*D)
    signed=[t for t in range(-B,B+1) if (t-1-D)%4==0]
    Q=Poly(prod(D*w*w-t*w+1 for t in signed),w,domain=QQ).monic()
    # Containment, exact equality at small checked N, no repeated factors.
    assert Q.rem(p).is_zero and p==Q and p.gcd(p.diff()).degree()==0
    degs.append(p.degree())

assert eliminant(1).gcd(Poly(2*w*w-w+1,w,domain=QQ)).degree()==0
simple_v=eliminant(3,True)
target=Poly((8*w*w-w+1)*(8*w*w+3*w+1),w,domain=QQ).monic()
assert simple_v==target
assert simple_v.gcd(Poly(8*w*w-5*w+1,w,domain=QQ)).degree()==0
q7=Poly(8*w*w-5*w+1,w,modulus=7)
assert q7.gcd(q7.diff()).degree()==1
print(f"symbolic PASS: 16 map, sign, and loop identities; degrees {','.join(map(str,degs))} for N=1..3")
print("symbolic PASS: distinct-v N=3 eliminant excludes trace 5; characteristic-7 factor is repeated")
