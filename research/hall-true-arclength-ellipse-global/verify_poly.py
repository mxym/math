"""Exact lower certificate for the full arclength ellipse, not an empirical quadrature."""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import comb
import sys
L=8
T=40
ZERO=F(0)
HALF=F(1,2)
qend=F(7,10)

def fail(c,msg):
    if not c:raise ArithmeticError(msg)
def put(P,k,v):P[k]=P.get(k,ZERO)+v
def scale(P,v):return {k:v*x for k,x in P.items() if x}
def plus(P,Q,v=1):
    for k,x in Q.items():put(P,k,v*x)
    return P
def mul(P,Q):
    R={}
    for k,x in P.items():
        for j,y in Q.items():put(R,k+j,x*y)
    return {k:x for k,x in R.items() if x}
def val(P,x):return sum(a*x**k for k,a in P.items())
def sg(n):return 1 if not n%2 else -1
binhalf=[F(1)]
for i in range(1,L+2):
    binhalf.append(binhalf[-1]*(i-F(3,2))/i)
fail(binhalf[1:]==[-abs(a) for a in binhalf[1:]],'sqrt branch')
def gw(j):
    return {a+b:binhalf[a]*binhalf[b] for a in range(L+1) for b in range(L+1) if a-b==j}
g={j:gw(j) for j in range(-L,L+1)}

# U(k,M)=constant term z^M(1-rho/z)^k/(1-rho*z)^k.
@lru_cache(None)
def U(k,M):
    if k<0:return U(-k,-M)
    if k==0:return {0:F(M==0)}
    return {2*a-M:sg(a)*comb(k,a)*comb(k+a-M-1,a-M) for a in range(max(0,M),k+1)}
@lru_cache(None)
def V(k,M):
    if k==0:
        return {abs(M): F(1 if M>0 else -1,2*abs(M))} if M else {}
    R={}
    for n in range(1,T+1):
        for sign,poly in [(1,U(k,M-n)),(-1,U(k,M+n))]:
            for j,x in poly.items():put(R,j+n,F(sign,2*n)*x)
    return R
@lru_cache(None)
def W(M):
    m=abs(M);R={}
    for n in range(1,T+1):put(R,2*n+m,F(1,2*n*(n+m)))
    if m:
        put(R,m,-sum(F(1,4*n*(m-n)) for n in range(1,m)))
    return R
@lru_cache(None)
def triangle(M,A,B):
    # Real part of E e^(2iMm) e^(2iB beta) I_{A,B}(pi/2-beta), excluding pi^2/8 constant.
    delta=F(M==0)
    if not A and not B:
        return scale(W(M),HALF)
    if not B:
        P=scale(U(-A,M),-F(sg(A),4*A*A))
        put(P,0,delta/(4*A*A))
        return plus(P,V(0,M),F(1,2*A))
    if not A:
        P=scale(U(B,M),F(1,4*B*B));put(P,0,-sg(B)*delta/(4*B*B));return plus(P,V(B,M),F(1,2*B))
    if A==B:
        P=scale(U(B,M),-F(1,4*B*B));put(P,0,sg(B)*delta/(4*B*B));return plus(P,V(0,M),-F(sg(B),2*B))
    P=scale(U(B-A,M),-F(sg(A),4*A*(A-B)))
    put(P,0,sg(B)*delta/(4*B*(A-B)))
    return plus(P,U(B,M),-F(1,4*A*B))

def bivariate():
    P=defaultdict(dict);h={}
    for i in range(L+1):
        for j in range(i,L+1):
            for l in range(j,L+1):h[(i,j,l)]=mul(mul(g[i],g[j]),g[l])
    for j in g:
        for k in g:
            for l in g:
                f=h[tuple(sorted((abs(j),abs(k),abs(l))))]
                H=triangle(j+k+l,-j+k+l,2*l)
                for b,y in H.items():
                    if y:plus(P[b],f,y)
    return P
def clear(P):
    D=max(P)
    R={}
    for b,row in P.items():
        fac=[comb(D-b,j)*2**b for j in range(D-b+1)]
        for a,x in row.items():
            if x:
                for j,c in enumerate(fac):put(R,a+b+2*j,x*c)
    return {e:c for e,c in R.items() if c},D
def bernstein(P,t0,t1):
    n=max(P)
    # Dilation/translation via expanding each (t0+(t1-t0)x)^e.
    power=[sum(c*comb(i,j)*t0**(i-j) for i,c in P.items() if i>=j)*(t1-t0)**j for j in range(n+1)]
    return [sum(power[j]*F(comb(i,j),comb(n,j)) for j in range(i+1)) for i in range(n+1)]
def halfsplit(B):
    L=[B[0]];R=[B[-1]]
    while len(B)>1:
        B=[(x+y)/2 for x,y in zip(B,B[1:])];L.append(B[0]);R.append(B[-1])
    return L,R[::-1]
def positive(B,depth=0):
    if min(B)>0:return (1,depth)
    if depth>=10:raise ArithmeticError(('uncertified Bernstein box',depth,min(B),B[0],B[-1]))
    U,V=halfsplit(B);i,a=positive(U,depth+1);j,b=positive(V,depth+1);return i+j,max(a,b)

def main():
    # High-q branch using pi < 22/7 and pi > 157/50.
    r=2*qend/(1+qend*qend)
    bound=F(22,7)**3/32-3*F(157,50)/16*sum(r**(2*n)/n**2 for n in range(1,11))
    fail(bound<F(1,4),'high eccentricity')
    # Pre-verified bounds used in the elementary error analysis.
    fail(r<F(16,17) and (2-F(54,100))**6<12,'Fourier error constants')
    P=bivariate()
    # Fourier truncation of the square root and beta resonance.
    put(P[0],L+1,-450*abs(binhalf[L+1])); put(P[T+1],0,-F(51,T+1))
    R,D=clear(P)
    smallest=min(R);fail(smallest==4,'quartic vanishing order')
    P4={i-4:c for i,c in R.items()}
    fail(P4[0]==F(37,6),'leading coefficient: wrong angular normalization')
    B=bernstein(P4,0,qend)
    boxes,depth=positive(B)
    print('sqrt truncation',L,'beta truncation',T,'rho denominator power',D,'degree after q^4',max(P4))
    print('q^4 coefficient',P4[0],'positive Bernstein intervals',boxes,'maximum subdivision depth',depth)
    print('q >= 7/10: strict upper < 1/4 by 10 positive dilogarithm terms')
    print('PASS: exact polynomial lower bound strictly positive for 0<q<=7/10.')
if __name__=='__main__':main()
