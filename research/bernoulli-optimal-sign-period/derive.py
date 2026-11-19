import sympy as s
d,D,z,y=s.symbols('d D z y',nonzero=True)
p=(1-d/D)/2
v=s.factor(p*(1-p))
b=v*(1-2*p)/6
c=-v*(1-2*p)*(1-12*v)/120
h=v*(1-6*v)/24
a=6/(5*d); delta=-1/D
S=delta*y+a*b*y**3

def gauss(poly):
    pol=s.Poly(poly,y)
    return s.factor(sum(c0*s.factorial2(k-1)/v**(k//2) for (k,),c0 in pol.terms() if k%2==0))
g0=gauss(b*y**3*S)
g1=gauss(b*y**3*(z*b*y**3+a*c*y**5-S**3/6)+c*y**5*S+h*y**4*b*y**3*S)
root=s.factor(s.solve(g1,z)[0])
claimed=2*(120*d**2+95*D**2-296)/(125*d*(d**2-D**2))
print(g0,root,s.simplify(root-claimed))
