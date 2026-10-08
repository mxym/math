#!/usr/bin/env python3
"""Exact k=4 Chebyshev corrected dual and rational positive primal replay.

Standalone source: no LP solver, no floats, no discovery library. SymPy
is used for Q(sqrt(2)) identities and exact rational matrix inversion.
"""
from math import comb,isqrt
import sympy as s

a,b,c,d,t=s.symbols('a b c d t',real=True)

def choose(n,k):
 if isinstance(n,int):return comb(n,k) if n>=k else 0
 return s.prod(n-j for j in range(k))/s.factorial(k)

def counts(n,x,y,z,w):
 N=choose(n,4)
 m1=x*choose(n-1,3)+(n-x)*choose(n-2,2)
 c22=choose(x,2)+y
 c21=x*(n-x)+(n-x-2*y)
 c20=choose(n,2)-c21-c22
 m2=c20+(n-3)*c21+choose(n-2,2)*c22
 c33=choose(x,3)+x*y+z
 c32=choose(x,2)*(n-x)+x*(n-x-2*y)+y*(n-2-x)+(n-x-2*y-3*z)
 m3=c32+(n-3)*c33
 m4=choose(x,4)+choose(x,2)*y+choose(y,2)+x*z+w
 moments=[N,m1,m2,m3,m4]
 return [sum((-1)**(j-i)*choose(j,i)*moments[j]
             for j in range(i,5)) for i in range(5)]

H=s.expand((1-s.chebyshevt(4,2*a-1))/2)
R=16*(a-1)*(200*a**3-232*a**2+63*a-4)
Jleading=3*(1-a)*s.diff(H,a)+(b-s.Rational(3,2)*a*(1-a))*s.diff(H,a,2)
J=s.expand(Jleading+R)
assert s.simplify(H-16*a*(1-a)*(2*a-1)**2)==0
nodes=[s.simplify((1+s.cos(s.pi*j/4))/2) for j in range(5)]
for j in range(1,5):
 bj=0 if j<4 else s.Rational(1,2)
 assert s.simplify(J.subs({a:nodes[j],b:bj})-(0 if j%2 else 32))==0
assert R.subs(a,1)==0
assert s.simplify(J.subs({a:1,b:0}))==0

beta=[s.Rational(0),s.Rational(4),-s.Rational(16,3),s.Rational(4),s.Rational(0)]
gamma=[s.Rational(64),-s.Rational(204),s.Rational(944,3),-s.Rational(108),s.Rational(0)]
bern=[choose(4,j)*a**j*(1-a)**(4-j) for j in range(5)]
assert s.simplify(sum(beta[j]*bern[j] for j in range(5))-H)==0
assert s.simplify(sum(gamma[j]*bern[j] for j in range(5))-R)==0
N=s.prod(1/t-j for j in range(4))/24
F=counts(1/t,a/t,b/t,c/t,d/t)
dual=s.factor(sum((beta[j]+t*gamma[j])*F[j] for j in range(4))/N)
assert s.simplify(s.limit(dual,t,0)-H)==0
assert s.simplify(s.limit((dual-H)/t,t,0)-J)==0
print('PASS exact Q(sqrt2) corrected Chebyshev dual and all four contacts')

for n in (60,120,240,480,960,1920):
 sq=isqrt(2*n*n)
 assert sq*sq<=2*n*n<(sq+1)**2
 nodes_int=[(2*n+sq+2)//4,n//2,(2*n-sq+2)//4,0]
 Id=counts(n,n,0,0,0)
 Tr=counts(n,n-2,1,0,0)
 V=[counts(n,x,0,0,0) for x in nodes_int]
 A=s.Matrix([[V[j][i]-Id[i] if j%2==0 else Tr[i]-V[j][i]
               for j in range(4)] for i in range(4)])
 rhs=s.Matrix([Tr[i]-Id[i] for i in range(4)])
 w=A.inv()*rhs
 assert A*w==rhs
 assert all(v>0 for v in w)
 assert w[0]+w[2]<1 and w[1]+w[3]<1
 print('PASS degree %d, exact marginal matching, positive primal, n*(1-P_id)=%s'%
       (n,s.factor(n*(w[0]+w[2]))))
print('EXACT k4 CHEBYSHEV + POSITIVE PRIMAL CHECKER PASSED')
