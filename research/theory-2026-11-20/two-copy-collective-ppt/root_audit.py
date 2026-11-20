from itertools import combinations_with_replacement, product
from pathlib import Path
import json
from sympy import Matrix, I, sqrt, eye, ones, diag, kronecker_product, expand

root=Path(__file__).parent
w=(-1+I*sqrt(3))/2
u=(-13+3*I*sqrt(3))/14
H=eye(3)+(u-1)*ones(3)/3
Z=diag(1,w,w**2).applyfunc(expand)
ZB=(Z.H*H*Z**2).applyfunc(expand)
F=Matrix(9,9,lambda i,j:int(i==3*(j%3)+j//3))
def exact(A): return A.applyfunc(expand)
Ms=[]
for A in (7*Z.H,7*ZB):
    B=exact(kronecker_product(A,A)); Ms.extend((exact(B+B.H),exact(I*sqrt(3)*(B-B.H))))
Ms.append(49*(3*F-eye(9)))
Tc=[Matrix.zeros(9) for _ in Ms]
for l,a,b,k,c in json.loads((root/'witness21.json').read_text())['terms']:
    val=c*(I*sqrt(3))**k
    Tc[l][a,b]=val
    if a!=b: Tc[l][b,a]=val.conjugate()
X=Matrix(3,3,lambda i,j:int(i==(j+1)%3)); T=kronecker_product(X,X)
R=kronecker_product(T,T)
K=sum((kronecker_product(M,N+F*N*F) for M,N in zip(Ms,Tc)),Matrix.zeros(81))
K=exact(K+R.T*K*R+R*K*R.T)
v=[]; diag_q=[]; typ=[]
for a,b in combinations_with_replacement(range(3),2):
    e=eye(9)[:,3*a+b];e2=eye(9)[:,3*b+a]
    v.append(e if a==b else e+e2);diag_q.append((2**a+2**b)%7);typ.append(0)
    if a!=b: v.append(e-e2);diag_q.append(diag_q[-1]);typ.append(1)
vecs={}
for i,j in combinations_with_replacement(range(9),2):
    a=kronecker_product(v[i],v[j]);b=kronecker_product(v[j],v[i])
    vecs.setdefault(((diag_q[i]+diag_q[j])%7,typ[i]+typ[j]),[]).append(a if i==j else a+b)
values=[]
for key,ls in sorted(vecs.items()):
    W=Matrix.hstack(*ls)
    b=exact(W.T*K*W)
    if exact(b-b.H)!=Matrix.zeros(b.rows): raise ValueError('not self-adjoint')
    for n in range(1,b.rows+1):
        d=expand(b[:n,:n].det())
        if not d.is_Integer or d<=0: raise ValueError((key,n,d))
        values.append(int(d))
if len(values)!=45 or min(values)!=290: raise ValueError((len(values),min(values)))
print("Direct SymPy exact constructor: 45 positive integer Sylvester minors, minimum",min(values))
