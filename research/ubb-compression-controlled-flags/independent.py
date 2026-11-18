"""Analytical illustration, over Q(i) using SymPy. Not a topological proof."""
from sympy import Matrix, eye, zeros, I, Rational as R, diag, re
def need(ok,label):
    if not ok: raise RuntimeError(label)
d=6
id=eye(d)
a,b=R(3,5),R(4,5)
def two(i,j,T):
    M=eye(d)
    for r,h in enumerate((i,j)):
        for c,k in enumerate((i,j)): M[h,k]=T[r,c]
    return M
def ip(X,Y):
    return (X.H*Y).trace().expand()
P=two(0,d-1,Matrix([[a,b*I],[b*I,a]]))
Q=two(2,d-1,Matrix([[a,b],[-b,a]]))
L=diag(I,-1,I,1,-I,1)
D=diag(1,1,1,1,1,a)
w=diag(3,0,0,0,0,-5)
def V(T):
    t=P.H*T*Q
    return P*L*(t-2*ip(w,t)/ip(w,w)*w)*Q.H
# Reflection followed by matrix-unitary multiplications is complex-linear and HS isometric.
X0=eye(d+1)
X0[d-1,d-1]=a;X0[d,d]=a;X0[d,d-1]=-b;X0[d-1,d]=b
X=diag(P,1)*X0*diag(Q.H,1)
Y=diag(P*L,1)*X0*diag(Q.H,1)
A=X[:d,:d];B=Y[:d,:d]
need(X.H*X==eye(d+1)==Y.H*Y,'full unitarity')
need(X[:,d:]==Y[:,d:] and X[d:,:]==Y[d:,:], 'fixed entry complement')
need(V(A)==B,'HS gate maps corners')
need(A*A.H==B*B.H and (A.H*A).T==(B.H*B).T,'corresponding marginals')
need(A*A.H!=(A.H*A).T,'two sides should differ in this example')
s=ip(A,A)
need(s==R(134,25) and (id-A*A.H).rank()==1 and (id-A.H*A).rank()==1,'defect bounds')
xs=[];ys=[]
for e in (+1,-1):
    u=D.copy();u[d-1,d-1]+=e*b*I
    xs.append(P*u*Q.H);ys.append(P*L*u*Q.H)
need(all((x.H*x).applyfunc(lambda v:v.expand())==id for x in xs+ys),'unitary roundings')
need(((xs[0]+xs[1])/2-A).applyfunc(lambda v:v.expand())==zeros(d) and ((ys[0]+ys[1])/2-B).applyfunc(lambda v:v.expand())==zeros(d),'averages')
test=[re(ip(y,V(x))) for x in xs for y in ys]
need(sum(test)/4==s and max(test)/d>=s/d>=R(5,6),'average of four real parts')
need(all((V(x).H*V(x)).applyfunc(lambda v:v.expand())!=id for x in xs),'roundings not exactly Bell for these choices')
# Direct normal Jacobian at an ordered eigenflag for the limit section, not the author's formula:
# [H,K]_{ji}; for each real elementary off-diagonal generator, compute components by commutators.
from itertools import permutations
from math import factorial
for n in range(2,5):
    c=tuple(range(n))
    pairs=[(i,j) for j in range(n) for i in range(j)]
    basis=[]
    for i,j in pairs:
        for z in [1,I]:
            T=zeros(n);T[j,i]=z;T[i,j]=-T[j,i].conjugate();basis.append(T)
    cnt=0
    for perm in permutations(range(n)):
        H=diag(*perm);cols=[]
        for K in basis:
            Co=H*K-K*H
            parts=[(I*(c[i]-c[j])*Co[j,i]).as_real_imag() for i,j in pairs]
            cols.append(Matrix([v for p in parts for v in p]))
        J=Matrix.hstack(*cols)
        need(J.det()>0, 'limit normal Jacobian not positive');cnt+=1
    need(cnt==factorial(n),'permutation count')
print('PASS: complex block and transposed marginals, nonlocal HS reflection, four overlaps',
      [x/d for x in test], 'averaging to', s/d,
      '; directly computed normal Jacobians through d=4')
