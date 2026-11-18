"""Audit local identities and explicit slack, not the huge n-by-n witness via enumeration."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations,combinations
from math import factorial,prod,comb
from random import Random

def chk(x):
    if not x: raise AssertionError("check failed")
def linprod(rows,d):
    ret={(0,)*d:1}
    for row in rows:
        nxt=defaultdict(int)
        for e,c in ret.items():
            for a,x in enumerate(row):
                if x:
                    f=list(e);f[a]+=1;nxt[tuple(f)]+=x*c
        ret=nxt
    return ret
def fischer(poly):
    return sum(c*c*prod(factorial(k) for k in e) for e,c in poly.items())
def evaluate(poly,z):
    return sum(c*prod(v**k for v,k in zip(z,e)) for e,c in poly.items())
def eyecheck(rows,z,y):
    n,d=len(rows),len(z)
    A=[[sum(x*y for x,y in zip(r,s)) for r in rows] for s in rows]
    per=der=0
    for p in permutations(range(n)):
        mon=prod(A[i][p[i]] for i in range(n))
        inv=sum(p[i]>p[j] for j in range(n) for i in range(j))
        per+=mon;der+=inv*mon
    P=linprod(rows,d);chk(per==fischer(P))
    F={t:defaultdict(int) for t in combinations(range(d),2)}
    for i,j in combinations(range(n),2):
        left=linprod([r for h,r in enumerate(rows) if h not in (i,j)],d)
        for (a,b),D in F.items():
            m=rows[i][a]*rows[j][b]-rows[i][b]*rows[j][a]
            for e,c in left.items(): D[e]+=c*m
    chk(2*der==comb(n,2)*per-sum(map(fischer,F.values())))
    Pz=evaluate(P,z)
    if Pz:
        xyz=sum((z[a]*y[b]-z[b]*y[a])*evaluate(poly,z) for (a,b),poly in F.items())
        rhs=sum((2*i-n+1)*Q(sum(x*b for x,b in zip(r,y)),sum(x*b for x,b in zip(r,z))) for i,r in enumerate(rows))
        chk(xyz==Pz*rhs)
def constants():
    n=1000;M=10**22
    # Rational upper bound on delta=2*10**(-2*M), used only as a loose additive bound.
    eps=Q(1,10**30)
    # For M>=100, 2*delta*M*3**(M-1) < 1 follows from 4*M*(3/100)**M.
    # This decreases for M>=1; exact finite comparison at 100 suffices.
    chk(4*100*Q(3,100)**100<1)
    eta=Q(1,100);rho=Q(1,10**8);ri=Q(1,10**22)
    g_loss=Q(22,7)/200+Q(3,100)+100*(2*Q(22,7)/M+eps)
    chk(g_loss<Q(46,1000));chk(Q(314,100)/4-Q(46,1000)==Q(739,1000))
    chk(2*Q(11,10)/M-eta*rho**2/2 < -Q(4,10**19))
    chk(eps+Q(3,2)*102*ri < Q(2,10**20))
    chk((ri/2)**6>Q(1,10**138))
    chk(102**2*rho/(Q(69,100)*Q(70,100))<Q(1,1000))
    chk(Q(99,100)*Q(73,100)**2 /((1+Q(3,n))*(1+Q(2,n)))>Q(1,2))
    F=lambda j:Q(j*j,10000+j*j)
    weights=[F(j+1)-F(j) for j in range(10000)]+[1-F(10000)]
    chk(sum(weights)==1 and min(weights)>0)
    # mu(N^c)<.01. Since e>2, it suffices that 7.2e-19*n > log2(100*10^138)<4*140.
    chk(2*(Q(4,10**19)-Q(4,10**20))*M*M>4*140)
if __name__=="__main__":
    rr=Random(3017023)
    for n in range(2,8):
        for d in range(2,5):
            for _ in range(3):
                rows=[[rr.randrange(-3,4) for _ in range(d)] for _ in range(n)]
                eyecheck(rows,[1,2,3,4][:d],[5,7,11,13][:d])
    constants()
    print("54 exact small Gram/permutation/Fischer identities; contractions when nonzero; finite-parameter margins passed")
