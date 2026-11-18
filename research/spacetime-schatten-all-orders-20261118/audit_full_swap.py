"""Independent audit of the two-qubit spacetime Schatten family.
Requires SymPy. Checks matrix identities as polynomials for all x, not at
selected samples; no calls to the primary checker. Runs under python -O.
"""
from itertools import product
import sympy as s
def check(t,n):
    if not t: raise ValueError(n)
x=s.symbols('x',real=True)
dim=4; idx=lambda q,e:2*q+e
U=s.Matrix([[1,0,0,0],[0,s.Rational(7,25),0,s.Rational(24,25)],
            [0,-s.Rational(24,25),0,s.Rational(7,25)],[0,0,1,0]])
check(U.T*U==s.eye(4),"unitarity")
E=s.eye(4); p=E[:,0]; v=(4*E[:,1]+3*E[:,3])/5
rho=(1-x)*(p*p.T)+x*(v*v.T)
F=s.zeros(dim**2)
for i,j in product(range(dim),repeat=2):F[i*dim+j,j*dim+i]=1
lift=s.kronecker_product(s.eye(dim),U)
# Full-system MAP operator, then trace over the old and new environments.
full=lift*F*lift.T*s.kronecker_product(rho,s.eye(dim))
T=s.zeros(4)
for a,b,c,d in product(range(2),repeat=4):
    T[2*a+b,2*c+d]=sum(full[4*idx(a,e)+idx(b,f),4*idx(c,e)+idx(d,f)]
                         for e,f in product(range(2),repeat=2))
A=s.Matrix(2,2,lambda i,j:sum(T[2*i+k,2*j+k] for k in range(2)))
B=s.Matrix(2,2,lambda i,j:sum(T[2*k+i,2*k+j] for k in range(2)))
pi=s.diag(1,0); ps=s.Matrix([4,3])/5
check(A==(1-x)*pi+x*(ps*ps.T),"initial marginal")
check(B==(1-x)*pi+x*s.diag(s.Rational(16,25),s.Rational(9,25)),"final marginal")
check(T.trace()==1,"trace")
T0=T.subs(x,0); T1=T.subs(x,1)
check(T0==s.diag(1,0,0,0),"anchor")
check(T1==s.Matrix([[112,0,84,0],[0,288,0,216],[384,0,288,0],[0,-84,0,-63]])/625,"T1")
check(s.expand((T.T*T).trace()-(1-s.Rational(1026,625)*x*(1-x)))==0,"Frobenius polynomial")
# Separate by FINAL time slot: B=0 block is generically rank two, B=1 block rank one.
P=T.extract([0,2],[0,2]); Q=T.extract([1,3],[1,3])
check(s.expand(P.det()-s.Rational(288,625)*x*(1-x))==0,'P determinant')
check(Q.det()==0 and s.expand((Q.T*Q).trace()-s.Rational(9,25)*x*x)==0,'Q singular value')
# For a real 2x2 P with det≥0 its trace norm squared is tr(P^TP)+2detP.
# Thus ||T_x||_1 = sqrt(1-18x/25+9x²/25)+3x/5.
tr1sq=s.factor((P.T*P).trace()+2*P.det())
check(s.expand(tr1sq-(1-s.Rational(18,25)*x+s.Rational(9,25)*x*x))==0,"exact endpoint norm")
check(s.expand((1-s.Rational(18,25)*x)**2-(T.T*T).trace()-s.Rational(18,625)*x*(7-39*x))==0,"p=2 excess")
check(s.Rational(63,625)-s.Rational(7,512)>s.Rational(1,12),"constants")
print('All symbolic identities verified, including T, both full marginals,')
print('Frobenius polynomial, trace norm formula and finite-p=2 certificate.')
