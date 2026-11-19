"""Independent polynomial coefficient replay, using SymPy (tested with 1.14.0)."""
import sympy as S
def eq(v):
    if S.expand(v)!=0: raise ArithmeticError(S.factor(v))
b,c,g,h,V,y=symbols=S.symbols('b c g h V y')
r=S.Rational
m=[1,0,V,c*V,3*V**2+(3*c**2-1)*V/2,10*c*V**2+(3*c**2-2)*c*V]
def integ(p):
    f=S.Poly(p,y)
    return S.expand(sum(f.nth(i)*m[i] for i in range(f.degree()+1)))
def coeffs(p):
    return S.Poly(p,V)
# Central case: derive from the quartic, without supplying its moment equations.
K=S.symbols('K');s=7*c/3; l=b*b-r(1,4)
T=(y*y-s*y-3*V+K)*((y-b)**2-r(1,4))
q=coeffs(integ(T)); u=coeffs(integ(y*T))
eq(q.nth(2)); eq(u.nth(2)); eq(q.nth(0)-K*l)
Kb=S.solve(q.nth(1),K)[0]; eq(Kb-(2*b-c)*(6*b-5*c)/6)
eq(u.nth(1).subs(K,Kb)+(2*b-c)*(12*b*b-12*b*c+2*c*c-3)/6)
# Outer case: use determinant elimination; derive both inputs directly from roots.
A=(y-h)*(y-g+b)*((y-b)**2-r(1,4))
f=integ(A); w=S.cancel(integ(y*A)/V)
W=S.Poly(S.resultant(f,w,V),b)
if W.degree()!=5:raise ArithmeticError('unexpected elimination degree')
eq(W.nth(5)-2*(2*c-3*h)); H=2*c/3
eq(W.nth(4).subs(h,H)-(14*c-6*g-3)*(14*c-6*g+3)/6)
for G in (7*c/3+r(1,2),7*c/3-r(1,2)):
    eq(W.nth(3).subs({h:H,g:G})+2*c*(c-3)*(c+3)/9)
print("PASS: exact central quartic orthogonality and all three outer-resultant coefficient tests, both signs.")
