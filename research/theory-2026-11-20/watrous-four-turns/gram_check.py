"""Independently expand the filtered three-component Gram matrix over Gaussian-symbolic coefficients."""
import sympy as s
ar,ai,br,bi,yr,yi,x,z = s.symbols('ar ai br bi yr yi x z',real=True)
j=s.I; alpha=ar+j*ai; beta=br+j*bi; y=yr+j*yi; C=lambda v:s.conjugate(v).expand(); ex=lambda v:s.expand_complex(v).expand(); re=lambda v:ex(v).as_real_imag()[0].expand();im=lambda v:ex(v).as_real_imag()[1].expand()
# Alice first gram on (a,n,d); Bob coarse gram on (b,h,m).
ga=s.Matrix([[1,0,alpha],[0,1,beta],[C(alpha),C(beta),2]])
gb=s.Matrix([[x,y,0],[C(y),z,0],[0,0,1]])
e=s.eye(3); a,n,d,b,h,m=[e[:,i] for i in (0,1,2,0,1,2)]; p=2*b+beta*h
kron=s.kronecker_product
u0=kron(a,b)+(kron(a+n,p)-kron(d,h))/2;u1=kron(n,b)+kron(a,p);u2=kron(a+n,b)+kron(a,m)
U=s.Matrix.hstack(u0,u1,u2); G=U.conjugate().T*kron(ga,gb)*U
L=2*x+beta*y; H=2*C(y)+beta*z; V=br**2+bi**2
N=ex(3*x+4*re(beta*y)+V*z-1); D20=ex(G[2,0]-G[1,2]);D01=ex(G[0,1]-G[1,2]);D00=ex(G[0,0]-G[1,1])
def ck(a,b): 
    if ex(a-b)!=0:raise ArithmeticError(ex(a-b))
ck(G[1,1]-G[2,2],N)
ck(D20,L-C(L)-(alpha+beta)*y/2)
ck(2*D01-N,1+x+2*(beta*y-C(beta*y))-C(alpha)*H)
ck(2*D00+N,3*x-4*re(alpha*y)+(1-re(C(alpha)*beta)-V)*z-1)
# Check eliminations including the complex cross constraint.
ck(re(2*D20),-re((alpha+beta)*y));ck(im(-2*D20),im((alpha-3*beta)*y))
ck(re(2*D01-N),1+x-2*re(alpha*y)-re(C(alpha)*beta)*z)
ck(im(2*D01-N),4*im(beta*y)+2*im(alpha*y)-im(C(alpha)*beta)*z)
ck((2*D00+N)-N-4*re(2*D20),(1-re(C(alpha)*beta)-2*V)*z)
print('Exact direct Fourier Gram, both real/imaginary constraints and all diagonal reductions: PASS.')
