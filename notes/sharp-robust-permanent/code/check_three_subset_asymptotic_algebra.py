#!/usr/bin/env python3
"""Exact symbolic audit of the asymptotic Sn triple-action theorem (Section 22).

No LP solver, numerical optimizations or floating-point operations. Requires
SymPy 1.14 (or compatible). Inequalities for real a,b and positivity for large
m are proved in the manuscript, not asserted by the CAS output alone.
"""
import sympy as s
m=s.symbols('m',integer=True,positive=True)

def orbital(n,x,y,z):
 N=n*(n-1)*(n-2)/6
 b1=(n-2)*(2*n+(n-3)*x)/2
 b2=(n-2)*x*(x-1)/2+(x+1)*(n-x)+(n-4)*y
 b3=x*(x-1)*(x-2)/6+x*y+z
 return [s.expand(N-b1+b2-b3),s.expand(b1-2*b2+3*b3),
         s.expand(b2-3*b3),s.expand(b3)]

def five_types(r):
 n=4*m+r
 K=(n-(m+2),0,0) if r in (0,1) else (n-(m+3),0,0)
 H= ((0,2*m,0) if r==0 else
     (0,2*m-1,1) if r==1 else
     (0,2*m+1,0) if r==2 else (0,2*m,1))
 T=(n-2,1,0)
 E= ((m-3,0,m+1) if r==0 else
     (m-2,0,m+1) if r==1 else
     (m-2,0,m))
 return n,[(n,0,0),K,H,T,E]

def check_primal(r):
 n,types=five_types(r)
 rows=[[1,1,1,0,0],[0,0,0,1,1]]
 rows += [[orbital(n,*t)[j]*(1 if i<3 else -1)
           for i,t in enumerate(types)] for j in range(3)]
 A=s.Matrix(rows)
 det=s.factor(A.det())
 assert s.limit(det/m**9,m,s.oo)==-192,(r,det)
 w=[s.factor(v) for v in (A.inv()*s.Matrix([1,1,0,0,0]))]
 assert len(w)==5
 limits=[s.limit(m*(1-w[0]),m,s.oo),
         s.limit(m*w[1],m,s.oo),
         s.limit(m*w[2],m,s.oo),
         s.limit(m*w[4],m,s.oo)]
 expected=[s.Rational(9,2),4,s.Rational(1,2),s.Rational(4,3)]
 assert all(s.simplify(a-b)==0 for a,b in zip(limits,expected)),(r,limits)
 assert s.limit(w[3],m,s.oo)==1
 assert s.limit(w[0],m,s.oo)==1
 print('PASS residue %d: det leading -192m^9, 5 exact equations, weights %s'
       %(r,str(limits)),flush=True)

def check_dual():
 a,b,c,t=s.symbols('a b c t',real=True)
 n=1/t
 x=a/t;y=b/t;z=c/t
 F=orbital(n,x,y,z)[:3]
 lamb=[-6*t**3+18*t**4,
       12*t**3-436*t**4,
       -18*t**3+198*t**4]
 dual=s.expand(-sum(lamb[i]*F[i] for i in range(3)))
 H=(1-a)*(4*a-1)**2
 J=320*a**3-592*a**2+296*a-24+48*b*(1-2*a)
 R2=1216*a**2+1920*a*b-1765*a-1280*b-96*c+549
 R3=2*(1001*a+2176*b+960*c-1001)
 assert s.simplify(dual-(H+t*J+t*t*R2+t**3*R3))==0
 assert s.simplify(H-(1-a*(4*a-3)**2))==0
 assert s.simplify(J.subs(b,(1-a)/2)-32*a*(1-a)*(7-10*a))==0
 assert s.simplify(J.subs({a:s.Rational(1,4),b:0})-18)==0
 assert s.simplify(J.subs({a:s.Rational(3,4),b:0}))==0
 assert s.simplify(J.subs({a:0,b:s.Rational(1,2)}))==0
 l1=lambda expression:sum(abs(int(z)) for _,z in s.Poly(expression,a,b,c).terms())
 assert l1(R2)==6826 and l1(R3)==10276
 assert 2440**2//32==186050
 assert 186050+17102==203152 and 2*203152==406304
 print('PASS exact dual polynomial H, J, R2, R3 and coefficient bounds',flush=True)

if __name__=='__main__':
 check_dual()
 for r in range(4):check_primal(r)
 print('ASYMPTOTIC SYMBOLIC CERTIFICATE REPLAY PASSED',flush=True)
