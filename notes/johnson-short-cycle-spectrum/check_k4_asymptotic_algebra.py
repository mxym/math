#!/usr/bin/env python3
"""Exact symbolic replay for the sharp k=4 Johnson asymptotic theorem.

Optional dependency: SymPy.  Uses rational polynomial identities only, no
optimizer, probability simulation, or floating-point assumptions.

Run: python3 notes/johnson-short-cycle-spectrum/check_k4_asymptotic_algebra.py
"""
import sympy as S

if not __debug__:
    raise RuntimeError('Run without -O: optimized Python disables assert checks')

s,t,n,x,y,z,w,a,b,c,d=S.symbols('s t n x y z w a b c d')
U=s+(t-1)*s**2+(t-1)*(t-2)*s**3+(t-1)*(t*t-5*t+5)*s**4
Lplus=1+U
zeta=S.series((1+s*t-Lplus)/Lplus,s,0,5).removeO().expand()
logL=S.series(S.log(Lplus),s,0,5).removeO()
logsmall=[S.series(S.log(1+zeta**j),s,0,5).removeO()
          for j in range(1,5)]
logterms=S.Poly(S.expand(n*logL+sum(
    q*expr for q,expr in zip((x,y,z,w),logsmall))),s)
q=[S.expand(logterms.coeff_monomial(s**i)) for i in range(1,5)]
generating=S.expand(q[3]+q[0]*q[2]+q[1]**2/S.Integer(2)
                    +q[0]**2*q[1]/2+q[0]**4/S.Integer(24))
F=[S.expand(S.Poly(generating,t).coeff_monomial(t**j))
   for j in range(5)]
assert S.expand(sum(F)-n*(n-1)*(n-2)*(n-3)/24)==0

leading=(0,-96,128,-96)
correction=(-1536,4320,-6784,2016)
num=S.expand(-sum((leading[j]*n+correction[j])*F[j]
                  for j in range(4)))
poly=S.Poly(S.expand(num.subs({x:a*n,y:b*n,z:c*n,w:d*n})),n)
H=-16*a*(a-1)*(2*a-1)**2
J=16*(176*a**4-408*a**3-48*a*a*b+310*a*a
      +48*a*b-85*a-10*b+7)
R3=16*(1248*a**3+2112*a*a*b-2481*a*a-2544*a*b-96*a*c
       +1485*a-48*b*b+668*b+48*c-252)
R2=16*(4932*a*a+11712*a*b+4224*a*c-7637*a+2112*b*b
       -7418*b-2592*c-96*d+2705)
R1=64*(2049*a+4426*b+3456*c+1056*d-2049)
for p,v in ((5,H),(4,J),(3,R3),(2,R2),(1,R1),(0,0)):
    assert S.expand(poly.coeff_monomial(n**p)-v)==0,p
K=sum(sum(abs(S.Rational(v)) for v in
          S.Poly(P,a,b,c,d).coeffs()) for P in (R3,R2,R1))
assert K==1704864
# All numerical constants used in the interval-free global dual proof.
assert S.Rational(4096*63,8)>3408
assert S.Rational(4096*7,64)>352
assert S.Rational(4096*3,2)>320
assert 43280**2/S.Integer(60)+28800+2*K<35000000
P=8*a*a-8*a+1
Q=16*(a-1)*(22*a-7)
assert S.expand(H-(1-P**2))==0
assert S.expand(J-(P*Q+b*(-64-96*P)))==0

root=S.sqrt(2)
lo=(2-root)/4
hi=(2+root)/4
V=S.Matrix([[
    lo**j-1,hi**j-1,1,1-S.Rational(1,2)**j
    ] for j in range(1,5)])
weights=S.Matrix([16-8*root,16+8*root,2,8])
assert S.simplify(V.det()+root/4096)==0
assert all(S.simplify(z)==0 for z in V*weights-
           S.Matrix([-2,-4,-6,-8]))
assert all(v.is_positive for v in weights)
assert S.simplify(weights[0]+weights[1]-32)==0
print('EXACT k=4 TRANSFER POLYNOMIAL: H, J, R3, R2, R1 verified')
print('ABSOLUTE REMAINDER COEFFICIENT SUM = 1704864')
print('LIMITING PRIMAL MATRIX DET = -sqrt(2)/4096')
print('LIMITING PRIMAL WEIGHTS = (16-8sqrt(2), 16+8sqrt(2), 2, 8)')
print('SHARP FIRST ORDER COEFFICIENT = 32 (algebra verified)')
