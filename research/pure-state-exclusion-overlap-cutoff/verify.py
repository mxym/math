"""Exact symbolic checkpoints, not an SDP or a numerical test. Tested with SymPy 1.14."""
import sympy as S
from itertools import combinations

def require(x,label):
    if not x: raise ArithmeticError(label)
    print('PASS:',label)

# Algebra in the genuine real embedding of Q(sqrt(2),sqrt(D^2-1/2)).
h=S.Rational(1,2); a=(1-1/S.sqrt(2))/2; D=1-a
b=(D+S.sqrt(D**2-h))/2; c=D-b
def eq(x,y): return S.simplify(S.expand(x-y))==0
require(eq(a+b+c,1) and eq(a*(b+c),S.Rational(1,8)) and eq(b*c,S.Rational(1,8)), 'five weights: sum and both product constraints')
require(all(S.simplify(x).is_positive for x in (a,c-a,b-c,b-h)), 'strict weight ordering and b>1/2')
require(eq(a**2+b**2+c**2,h) and eq((b-a-c)**2,4*a*c),'purity and triangle equality polynomial')
z=S.symbols('z'); f=S.expand((a+b*z+c*z**4)*(a+b*z**4+c*z))
e=S.Poly(f,z,extension=True);mod=S.Poly(S.cyclotomic_poly(5,z),z,domain=e.domain)
require(eq(e.rem(mod).as_expr(),S.Rational(3,8)), 'all four nontrivial fifth-root offsets: squared overlap 3/8')

# Verify the square identity for the standard real orthonormal basis in Herm(3).
I=S.eye(3); hs=[S.zeros(3) for _ in range(3)]
for j,H in enumerate(hs):H[j,j]=1
for j,k in combinations(range(3),2):
    E=S.zeros(3);E[j,k]=1
    hs.extend([(E+E.T)/S.sqrt(2),S.I*(E-E.T)/S.sqrt(2)])
require(S.Matrix([[(X*Y).trace() for Y in hs] for X in hs])==S.eye(9) and sum((X**2 for X in hs),S.zeros(3))==3*I,'real Hilbert-Schmidt ONB and its sum of squares')
n,x=S.symbols('n x'); s=(n-2)/(2*(n-1))
rhs=S.Rational(8,3)-6*(x-S.Rational(1,3))**2-n/(1-s)*(x-x**2)
require(S.factor(rhs-2*(1-x)*(1-(n-4)*x))==0,'qutrit matrix inequality polynomial, all n')

# Check the exterior rank argument coefficientwise in a representative case,
# including overlap of two unordered index pairs in the square.
T=S.symbols('T'); y=S.symbols('y:5');u=sum(t*t for t in y)
require(S.expand(2*(T*T+sum(t**4 for t in y))-(T+u)**2-(T-u)**2+4*sum(j*j*k*k for j,k in combinations(y,2)))==0,'purity factorization for five tail entries')

# Projective zonal specialization: no reliance on a sampling approximation.
K=10*x**2-8*x+1
require(S.expand(S.jacobi(2,1,0,2*x-1)-K)==0 and S.factor(3+(n-1)*K.subs(x,s)+n*(n-6)/(2*(n-1)))==0,'classical projective Jacobi polynomial and all-ones eigenvalue')
lo=(4-S.sqrt(6))/10; hi=(4+S.sqrt(6))/10
require(all(eq(K.subs(x,r),0) for r in (lo,hi)) and all(S.simplify(k*lo+(3-k)*hi-1).is_zero is False for k in range(4)), 'six-state equality: both roots and all four multiplicity patterns')
