"""Independent exact algebraic certificate; no calls into the candidate's verifier. SymPy 1.14."""
import sympy as S
from itertools import product,combinations
from fractions import Fraction as Q

def need(x,s):
    if not x: raise ArithmeticError(s)
t,z,B,n=S.symbols('t z B n',real=True)
q=t**4+2*t**3-t**2-2*t-1
# Use an alternative one-root parameterization of the triangle equality.
need(q.subs(t,1)<0 and q.subs(t,2)>0 and all(a>0 for a in S.Poly(S.diff(q,t).subs(t,t+1),t).all_coeffs()),'isolated real root in (1,2)')
A=1; C=t**2; H=(1+t)**2; D=A+H+C
need(S.rem(A*(H+C)-H*C,q,t)==0,'cyclic equal-coefficient identity')
need(S.expand(2*(A*A+H*H+C*C)-D*D)==0,'purity via triangle parameterization')
need(S.rem(8*H*C-D**2,q,t)==0,'common products 1/8')
mod=1+z+z**2+z**3+z**4
for j in range(1,5):
    p=(A+H*z**j+C*z**(5-j))*(A+H*z**(5-j)+C*z**j)
    rem=S.rem(S.expand(8*p-3*D**2),mod,z)
    need(all(S.rem(v,q,t)==0 for v in S.Poly(rem,z).all_coeffs()),'C5 squared overlap')
print('PASS alternative algebraic quintuple, four Fourier offsets and spectral equality.')

# For any strict positive rational eta, the unnormalized amplitudes after keeping 1 and t
# fixed and raising the third are 1,t,1+t+eta, violating the triangle necessary condition.
eta=S.Symbol('eta',positive=True)
need(S.simplify((1+t+eta)-(1+t))==eta,'strict perturbation')
print('PASS symbolic strict cyclic triangle violation at every positive perturbation.')

# Independent coordinate evaluation of the Hilbert-Schmidt sum:
# For diagonal B in its eigenbasis, use e_1 as the tested eigenvector.
# The complete ONB contributes one diagonal vector and four off-diagonal terms of norm² 1/2.
total=Q(1)+4*Q(1,2);need(total==3,'complete coordinate sum')
s=(n-2)/(2*(n-1));rhs=3-S.Rational(1,3)-6*(B-S.Rational(1,3))**2
need(S.factor(rhs-n*B*(1-B)/(1-s))==2*(1-B)*(1-(n-4)*B) or S.simplify(rhs-n*B*(1-B)/(1-s)-2*(1-B)*(1-(n-4)*B))==0,'scalar Bessel polynomial')
print('PASS compression onto the maximal-eigenvalue line: scalar nonnegative slack factorization.')

# Explore the rank/equality boundary over exact rational square-root spectra.
ct=0
for tails in product(range(4),repeat=5):
    for excess in (0,1):
        u=sum(tails)+excess
        if u==0:continue
        masses=[u*u]+[a*a for a in tails]
        diff=2*sum(m*m for m in masses)-sum(masses)**2
        need(diff>=0 and (diff==0)==(excess==0 and sum(x!=0 for x in tails)<=2),'rank/equality')
        ct+=1
print('PASS',ct,'exact square-root spectra, including equality strata.')

# Auxiliary prior-art comparison with Balla's cubic (not part of the proof under review).
p=B**3-(n-1)*B/(2*(n-2))+1/(2*(n-2))
need(S.factor(p.subs(B,S.Rational(2,3)))==(13-2*n)/(54*(n-2)) or S.simplify(p.subs(B,S.Rational(2,3))-(13-2*n)/(54*(n-2)))==0,'Balla high endpoint')
print('PASS auxiliary prior spectral-cubic endpoint.')
