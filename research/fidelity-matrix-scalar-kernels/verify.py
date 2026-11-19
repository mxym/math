"""Exact, standard-library arithmetic checks for the constructions in PROOF.md.
Finite replay is not a proof of the universal quantifiers."""
from fractions import Fraction as Q
from math import ceil,isqrt
from itertools import product

def need(b):
    if not b: raise ArithmeticError("check failed")
def dot(u,v):
    return sum(a*b for a,b in zip(u,v))
def det(A):
    a,b,c,d=A
    return a*d-b*c
def trprod(A,B):
    a,b,c,d=A; w,x,y,z=B
    return a*w+b*y+c*x+d*z
def qblock(r,U):
    a,b,c,d=U
    return ((1+r*a)/2,r*b/2,r*c/2,(1+r*d)/2)
ops=[(1,0,0,-1),(0,1,1,0),(-1,0,0,1),(0,-1,-1,0)]
z=[1,-1,1,-1]
def eo(a,b):
    return (a,b)              # a+b*sqrt(17)
def eadd(x,y):return tuple(a+b for a,b in zip(x,y))
def emul(x,y):return eo(x[0]*y[0]+17*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def esc(k,x):return tuple(k*a for a in x)
def eneg(x):return esc(-1,x)
def esum(xs):
    v=eo(0,0)
    for x in xs:v=eadd(v,x)
    return v
rvals=[Q(1,64),Q(1,7),Q(1,2),Q(4,5),Q(37,38),Q(999,1000)]
for r in rvals:
    A=[qblock(r,U) for U in ops]
    need(all(B[0]+B[3]==1 and B[1]==B[2] and B[0]>0 and det(B)==(1-r*r)/4>0 for B in A))
    X=[[trprod(B,C)+2*det(B) for C in A] for B in A]
    for i,j in product(range(4),repeat=2):
        need(X[i][j]==[1,1-r*r/2,1-r*r,1-r*r/2][(i-j)%4])
    for pi in range(1,151):
        for pj in range(1,17):
            p=Q(pi,pj);eps=Q(1,1+ceil(p))
            need(0<eps<1 and max(0,p-2)*eps-(1-eps)<0)
r=Q(4,5)
A=[qblock(r,U) for U in ops]
eps=Q(1,2)
published=[(9,0,0,1),(5,4,4,5),(1,0,0,9),(5,-4,-4,5)]
for i in range(4):
    need(tuple(eps*x for x in A[i])==tuple(Q(x,20) for x in published[i]))
Rs=[eo(1,0),eo(0,Q(1,5)),eo(Q(3,5),0),eo(0,Q(1,5))]
expected=[eo(1,0),eo(Q(21,50),Q(1,10)),eo(Q(16,25),0),eo(Q(21,50),Q(1,10))]
for i,j in product(range(4),repeat=2):
    rr=Rs[(i-j)%4]
    need(emul(rr,rr)==eo(trprod(A[i],A[j])+2*det(A[i]),0))
    R=eadd(eo(1-eps,0),esc(eps,rr))
    need(emul(R,R)==expected[(i-j)%4])
for i in range(4):
    need(esum(esc(z[j],expected[(i-j)%4]) for j in range(4))==esc(z[i],eo(Q(4,5),Q(-1,5))))
need(4**2<17)
print("A: full-rank states and 96 qubit fidelities; 2400 rational exponent certificates; ordinary eigenvalue (4-sqrt(17))/5. PASS")
# Walsh entries of normalized H are +-1/sqrt(n); choose n a square so all Gram computations are rational.
# Encode the symbolic kernels by 3 coordinates = (D, f(within), f(cross)).
def sigtest(C,n):
    signs=[1]*n+[-1]*n
    cc=[sum(signs[i]*signs[j] for i,j in product(range(2*n),repeat=2) if C[i][j]==k)
        for k in range(3)]
    need(cc==[2*n,2*n*(n-1),-2*n*n])
for n in [4,16,64]:
    L=isqrt(n)
    cols=[tuple(Q(1-2*((i&j).bit_count()%2),L) for i in range(n)) for j in range(n)]
    for i,j in product(range(n),repeat=2): need(dot(cols[i],cols[j])==int(i==j))
    bases=[tuple(int(i==j) for i in range(n)) for j in range(n)]+cols
    for a,b in [(Q(0),Q(1,3)),(Q(1,5),Q(3,5)),(Q(9,10),Q(99,100))]:
        s=b-a
        # Common flags and private labels, including contribution of identical states.
        C=[[None]*(2*n) for _ in range(2*n)];C2=[row[:] for row in C]
        for i,j in product(range(2*n),repeat=2):
            typ=0 if i==j else 1 if i//n==j//n else 2
            v=a+(b-a)*int(i//n==j//n)+(1-b)*int(i==j)
            w=a+s*abs(dot(bases[i],bases[j]))+(1-a-s)*int(i==j)
            need(v==(1,b,a)[typ] and w==(1,a,a+s/L)[typ]); C[i][j]=typ;C2[i][j]=typ
        sigtest(C,n);sigtest(C2,n)
    for a,b in [(Q(0),Q(1,10)),(Q(0),Q(9,10)),(Q(9,10),Q(99,100))]:
        m=ceil((b-a)*L/(1-b));h=(b-a)/m
        need(m>=1 and h<=(1-b)/L and (m-1)<(b-a)*L/(1-b)<=m)
        need(a+m*h==b)
print("B: 3 real mutually unbiased bases pairs; 9 pairs of flagged ensembles, both signed Gram identities, 9 uniform meshes. PASS")
