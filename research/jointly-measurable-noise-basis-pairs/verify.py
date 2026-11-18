#!/usr/bin/env python3
"""Check both explicit parents on complex basis pairs using only integers.
Use the realification of Gaussian integer matrices; no spectral solver,
floating arithmetic, external library, or assertions disabled by -O.
The proof, not the finite examples, establishes the universal theorem.
"""
from itertools import combinations

def ck(cond,msg):
    if not cond: raise ArithmeticError(msg)

def zero(n): return [[0]*n for _ in range(n)]
def eye(n,c=1): return [[c*int(i==j) for j in range(n)] for i in range(n)]
def tr(A): return list(map(list, zip(*A)))
def plus(A,B): return [[u+v for u,v in zip(a,b)] for a,b in zip(A,B)]
def mul(c,A): return [[c*u for u in a] for a in A]
def prod(A,B):
    Bt=tr(B)
    return [[sum(x*y for x,y in zip(a,b)) for b in Bt] for a in A]
def total(xs,n):
    A=zero(n)
    for X in xs:A=plus(A,X)
    return A

def check(d):
    n=2*d; I=eye(n)
    # U=I-2zz*/N.  The block of its realification at (a,b) represents
    # multiplication by a Gaussian integer /N. Denominators of P,Q are L.
    z=[(1+i%3,(-1)**i*(i%2+1)) for i in range(d)]
    N=sum(x*x+y*y for x,y in z); L=N*N; W=zero(n)
    for a,(xa,ya) in enumerate(z):
        for b,(xb,yb) in enumerate(z):
            u=N*(a==b)-2*(xa*xb+ya*yb); v=-2*(ya*xb-xa*yb)
            W[a][b]=W[d+a][d+b]=u;W[d+a][b]=v;W[a][d+b]=-v
    ck(prod(tr(W),W)==eye(n,L),'unitary')
    P=[];Q=[]
    for a in range(d):
        p=zero(n);p[a][a]=p[d+a][d+a]=1
        P.append(mul(L,p));Q.append(prod(prod(W,p),tr(W)))
    for E in (P,Q):
        ck(total(E,n)==eye(n,L),'PVM total')
        for i,X in enumerate(E):
            for j,Y in enumerate(E):
                ck(prod(X,Y)==(mul(L,X) if i==j else zero(n)),'PVM products')
    def kernel(E,i,X):
        out=zero(n)
        for j,k in combinations([a for a in range(d) if a!=i],2):
            D=plus(E[j],mul(-1,E[k]));out=plus(out,prod(prod(D,X),D))
        return out
    G0rows=[];G1rows=[];Hrows=[]
    for i,p in enumerate(P):
        aa=[];bb=[];hh=[]
        for j,q in enumerate(Q):
            pq=prod(p,q);qp=tr(pq)
            g0=plus(mul(L*L,plus(p,q)),mul(d,plus(prod(pq,p),prod(qp,q))))
            g1=mul(2*L,plus(pq,qp))
            # D G_ij = (g0 + sqrt(d) g1)/L^3. Verify its positive squares
            # coefficient by coefficient using powers of sqrt(d) reduced.
            xs=(mul(L,p),mul(L,q)); ys=(pq,qp)
            s0=total((plus(prod(tr(x),x),mul(d,prod(tr(y),y))) for x,y in zip(xs,ys)),n)
            s1=total((plus(prod(tr(x),y),prod(tr(y),x)) for x,y in zip(xs,ys)),n)
            ck(s0==mul(L,g0) and s1==mul(L,g1),'parent squares')
            aa.append(g0);bb.append(g1);hh.append(plus(kernel(P,i,q),kernel(Q,j,p)))
        G0rows.append(aa);G1rows.append(bb);Hrows.append(hh)
    # Compare both parent marginals exactly, keeping the coefficient of
    # sqrt(d) separate. Scaled H has denominator 2(d-1)(d-2)L^3.
    for G0,G1,H,E in [(G0rows,G1rows,Hrows,P),
                       (tr(G0rows),tr(G1rows),tr(Hrows),Q)]:
        for a in range(d):
            u,v,h=(total(M[a],n) for M in (G0,G1,H))
            ck(v==mul(4*L*L,E[a]),'sqrt(d) marginal')
            ck(mul(d-2,plus(u,mul(-(2*d+2)*L*L,E[a])))==h,'noise marginal')
    def grand(M):return total((X for row in M for X in row),n)
    ck(grand(Hrows)==mul(2*(d-1)*(d-2)*L**3,I),'noise normalization')
    ck(grand(G0rows)==mul(4*d*L**3,I) and grand(G1rows)==mul(4*L**3,I),'parent normalization')
    return d*d
cells=sum(check(d) for d in range(3,8))
print('PASS: complex rational Householder bases, d=3,...,7; both parents normalized, both marginal lists and',cells,'operator square identities exact.')
# A universal identity for a single matrix unit X in the P basis:
# (d-1) sum_i K_i(X) is d-1 on a diagonal entry and -1 on
# an off-diagonal one. Test all such coefficients with counted pairs.
for d in range(3,21):
    for a in range(d):
        for b in range(d):
            v=sum((d-2)*(int(j==a)-int(k==a))*(int(j==b)-int(k==b))
                  for j,k in combinations(range(d),2))
            ck(v==(d-2)*((d if a==b else 0)-1),'Kraus coefficient')
print('PASS: all diagonal and off-diagonal map coefficients, d=3,...,20.')
