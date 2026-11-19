"""Exact finite regression checks accompanying the analytic review. No dependencies."""
from fractions import Fraction as Q

def ck(v):
    if not v:
        raise ArithmeticError("independent rational identity failed")

def mink(a,b):
    return -a[0]*b[0]+sum(x*y for x,y in zip(a[1:],b[1:]))

def csp(x):
    return (1+x*x)/(1-x*x),2*x/(1-x*x)

def dot(a,b):
    return sum(i*j for i,j in zip(a,b))

def cp(q):
    return (1-q*q)/(1+q*q),2*q/(1+q*q)

# Choose p=(1,0,0), v any rational unit direction in the transverse sphere;
# by homogeneity and transverse rotations this suffices for the metric calculation.
g=0
for D in range(3,9):
    for i in range(1,20):
        C,S=csp(Q(i,20)); n=D+1
        center=(C,0,0,S)+tuple(0 for _ in range(n-4))
        radial=(S,0,0,C)+tuple(0 for _ in range(n-4))
        tang=[radial]+[tuple((C if k in (1,2) else S) if j==k else 0 for j in range(n)) for k in list(range(1,3))+list(range(4,n))]
        ck(mink(center,center)==-1)
        det=1
        for j,e in enumerate(tang):
            target=1 if j==0 else C*C if j in (1,2) else S*S
            ck(mink(center,e)==0 and mink(e,e)==target)
            ck(all(mink(e,f)==0 for f in tang[:j])); det*=target
        ck(det==C**4*S**(2*(D-3)))
        g+=1
print("Fermi metric determinants:",g)

# Cotangent half-angle substitution: after integrating, tan(sum of two
# primitive arctangents) is sqrt(B)/sin(theta). Verify without radicals.
angles=0
for i in range(1,51):
    v=Q(i,51); cosθ,sinθ=cp(v)
    for j in range(1,30):
        k=Q(j,31); A=(1+k*k)/(1-k*k); B=A*A-1
        norms=[k/v,k*v]
        ck(norms[0]*norms[1]<1)
        u=(norms[0]+norms[1])/(1-norms[0]*norms[1])
        ck(u*u*sinθ*sinθ==B)
        ck(1-cosθ*cosθ==sinθ*sinθ)
        angles+=1
print("Angular primitive (positive arctangent branch):",angles)

# Compute exact Gram data for simplex projections e_i -(1/N)1 in Q^N,
# with independent sign choices; divide dot products by their common norm^2.
pairs=0
for N in range(4,20):
    D=N-1
    rows=[tuple((-1)**i*(Q(int(i==k))-Q(1,N)) for k in range(N)) for i in range(N)]
    G=[[dot(u,v)/dot(u,u) for v in rows] for u in rows]
    for i in range(N):
        for j in range(N):
            ck(sum(G[i][k]*G[k][j] for k in range(N))==Q(N,D)*G[i][j])
            if i!=j:
                ck(G[i][j]**2==Q(N-D,D*(N-1)))
                pairs+=1
print("Signed regular-simplex ordered pair checks:",pairs)
