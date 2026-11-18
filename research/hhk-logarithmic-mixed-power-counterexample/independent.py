"""Verify the identities symbolically, without calling the author's checker."""
import sympy as s
a,b,x=s.symbols('a b x',real=True); D=lambda u,v:s.diag(u,v)
B=s.Matrix([[x,1],[1,x]])
F,G,T=D(1,a),D(1,b),D(0,-1)
L=F*B+B*G*T;R=F*T*B+B*G
def x2(expr):return s.factor(s.expand(expr).subs(x**2,1/(b-a)))
def require(expr): 
    if s.simplify(expr)!=0:raise ValueError(expr)
require(x2(L.det())-(-1-a*(1-b)));require(x2(R.det())-(1-b*(1-a)))
# Opposite determinant signs choose different O(2) trace-dual branches.
require(R.trace()-(L[0,0]-L[1,1]))
require((R[0,1]-R[1,0])**2-(L[0,1]+L[1,0])**2-4*a*(b-1))
print('PASS symbolic ordered products, determinant signs reduced to explicit factors, two orthogonal trace-dual branches, and exact gap.')
