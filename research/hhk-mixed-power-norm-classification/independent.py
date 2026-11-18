"""Independent exact checks: no third-party dependencies, finite differences or author code."""
from fractions import Fraction as F
from itertools import product
def ck(x,msg):
    if not x: raise ValueError(msg)
def det(M):return M[0][0]*M[1][1]-M[0][1]*M[1][0]
def transpose(M):return list(zip(*M))
def mul(M,N):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*N)] for row in M]
def tr(M):return M[0][0]+M[1][1]
def m(u,k,c): # A=diag(1,(1/k)^4), power u/4
    r=F(1,k)
    return [[F(3),2*(1+r**(4-u))],[2*(1+r**u),c*(r**u+r**(4-u))]]
def char(M,z): return z*z-z*tr(M)+det(M)
q=F(79,20)
L,R=m(2,8,-8),m(3,8,-8)
RR=mul(transpose(R),R)
ck(char(L,q)==-F(3481,25600),'large eigenvalue of L')
ck(q*q-RR[0][0]==F(4238311,1638400) and char(RR,q*q)==F(193986147,81920000),'right upper bound')
print('PASS exact rational operator-norm bracket.')
# Singular-value derivatives independently from sum and product of squared singular values.
# At H+uE = [[3,2+2u],[2,cu]], Tr(M^*M)'=8; det(M)'=3c-4.
# Squared singular values at zero are 16 and 1; SVD derivatives are recovered from these two polynomial data.
for c in map(F,range(-13,14)):
    dsum=8; dprod=-8*(3*c-4)
    dl1=(16*dsum-dprod)/15; dl2=dsum-dl1
    ck(dl1/8==(4+c)/5 and dl2/2==(4-4*c)/5,'SVD derivative')
for T in [F(1),F(6,5),F(2),F(7,2),F(399,100),F(401,100),F(9),F(10)**6]:
    c=-(4*(T+1)+5)/(T-4)
    ck(T*(4+c)/5+(4-4*c)/5==-1,'Schatten derivative / p')
    ck((c>F(8,3))==(T<4),'positivity split')
print('PASS independent trace-determinant singular-value linearization.')
# Compare finite rational cases by eliminating square roots: use ||M||_p^p for p=4 and square it for p=1,3.
def score(M,p):
    K=mul(transpose(M),M);T=tr(K);d=abs(det(M))
    if p==1:return T+2*d
    if p==3:return (T+2*d)*(T-d)**2
    if p==4:return T*T-2*d*d
    raise ValueError(p)
for p in (1,3,4):
    T=F(4)**(p-1);c=-(4*(T+1)+5)/(T-4)
    for k in (128,256,1024):
        ck(score(m(2,k,c),p)>score(m(3,k,c),p),'finite Schatten counterexample')
print('PASS nine exact finite inequalities for p=1,3,4.')
# Spectral tilt at general x,y from the implicit characteristic equation:
# P(lambda,h)=lambda^2−(x−y+h)lambda+(x−y)h−xy.
for a,b in product(range(1,17),repeat=2):
    x,y=F(a,7),F(b,11)
    for lam,der in [(x,y/(x+y)),(-y,x/(x+y))]:
        ck(lam*lam-(x-y)*lam-x*y==0,'root')
        ck((2*lam-(x-y))*der-lam+(x-y)==0,'root derivative')
print('PASS 512 exact signed-eigenvalue derivative identities for the rotating pair.')
