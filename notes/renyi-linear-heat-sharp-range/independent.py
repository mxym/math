#!/usr/bin/env python3
"""Symbolic adversarial check: local heat score and apparent Shannon singularity."""
import sympy as S
z,k,l,a=S.symbols('z k l a',positive=True)
d=2*k/l
m=k-d/2
def chk_zero(v):
    if S.cancel(v)!=0:raise RuntimeError(S.factor(v))
def E(val):
    coeffs=S.Poly(S.expand(val*z**2),z)
    moments=[1/((k-1)*(k-2)),1/(k-1),1,k,k*(k+1)]
    if coeffs.degree()>4:raise RuntimeError('unhandled moment')
    return S.factor(sum(c*moments[i] for (i,),c in coeffs.terms()))
# Rather than the author's A,B covariance, differentiate local score p=Delta u/u.
L1=(m/z-1)/a
score=S.expand(4*z*(S.diff(L1,z)+L1**2)+2*d*L1)
score_dt=S.expand(4*z*S.diff(score,z,2)+(2*d+8*z*L1)*S.diff(score,z))
hp=S.factor(a*E(score)/(1-a))
shpp=S.factor(a/(1-a)*(a*(E(score**2)-E(score)**2)+E(score_dt)))
T=S.factor(-d*shpp/hp**2)
J=m*(m+d-2);H=m**2
b=S.factor(k-2*m+H/(k-1))
def V(e,f):return k-(e+f)/(k-1)+e*f/(k-1)**2/(k-2)
static=a*d/2*(V(J,J)+(2/a-1)*V(J,H))/b**2
chk_zero(T-static);chk_zero(hp-4*b/a)
chk_zero(S.limit(T,k,S.oo)-2*(2-a)-2*(a-1)/l)
chk_zero(T.subs(l,1)-2)
# At alpha=1 the Shannon Bochner formula supplies an independent removable limit:
hess2=E((-2-2*m/z)**2+(d-1)*(-2+2*m/z)**2)
chk_zero(shpp.subs(a,1)+2*hess2)
print('PASS: independent heat-score computation at symbolic order, gamma shape and shell ratio; normalized large-d limit; Shannon/ Gaussian limits.')
