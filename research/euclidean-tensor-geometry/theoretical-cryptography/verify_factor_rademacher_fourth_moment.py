"""Exact fourth-moment and dimension-parity witness checks (stdlib only)."""
from fractions import Fraction as F
from itertools import combinations, product
from random import Random

if not __debug__:
    raise RuntimeError("Run without -O")

# a=sqrt(2)-1, b=sqrt(2*a), c=sqrt(3), i=sqrt(-1)
# All polynomial coefficients are rational and products reduce by these monic rules.
ZERO=(0,0,0,0)
RULE=({ZERO:1,(1,0,0,0):-2}, {(1,0,0,0):2}, {ZERO:3}, {ZERO:-1})

def norm_polynomial(D):
    o={}
    def process(v,x):
        if not x:
            return
        if max(v)<=1:
            o[v]=o.get(v,0)+x
            return
        h=max(j for j in range(4) if v[j]>=2)
        w=list(v)
        w[h]-=2
        for z,k in RULE[h].items():
            process(tuple(a+b for a,b in zip(w,z)),x*k)
    for v,x in D.items():
        process(v,x)
    return {v:x for v,x in o.items() if x}

class Q:
    def __init__(self,x=0):
        self.d=norm_polynomial(x if isinstance(x,dict) else {ZERO:F(x)})
    def __add__(self,y):
        y=q(y);d=self.d.copy()
        for t,x in y.d.items(): d[t]=d.get(t,0)+x
        return Q(d)
    __radd__=__add__
    def __neg__(self): return Q({v:-a for v,a in self.d.items()})
    def __sub__(self,y): return self+-q(y)
    def __mul__(self,y):
        y=q(y);d={}
        for v,a in self.d.items():
            for w,b in y.d.items():
                t=tuple(x+z for x,z in zip(v,w))
                d[t]=d.get(t,0)+a*b
        return Q(d)
    __rmul__=__mul__
    def conj(self): return Q({v:(-1 if v[3] else 1)*a for v,a in self.d.items()})
    def __eq__(self,y): return self.d==q(y).d
    def rational(self):
        assert all(k==ZERO for k in self.d), self.d
        return self.d.get(ZERO,F(0))

def q(x): return x if isinstance(x,Q) else Q(x)
a,b,c,i=(Q({tuple(int(j==k) for j in range(4)):F(1)}) for k in range(4))
assert a*a+2*a==1 and b*b==2*a and c*c==3 and i*i==-1

def adj(A): return [[q(x).conj() for x in row] for row in zip(*A)]
def mul(A,B): return [[sum(q(x)*y for x,y in zip(r,s)) for s in zip(*B)] for r in A]
def add(A,B,fac=1): return [[q(x)+fac*q(y) for x,y in zip(r,s)] for r,s in zip(A,B)]
def smul(a,A): return [[q(a)*x for x in r] for r in A]
def add_all(L): return [list(map(sum,zip(*r))) for r in zip(*L)]
def eye(d): return [[int(k==h) for h in range(d)] for k in range(d)]
def frob(A): return sum(q(x)*q(x).conj() for row in A for x in row)
def direct_sum(A,B):
    return [list(row)+[0]*len(B[0]) for row in A]+[[0]*len(A[0])+list(r) for r in B]
def bin_meas(As):
    S=add_all([mul(adj(A),A) for A in As]);T=add_all([mul(A,adj(A)) for A in As])
    D=sum(frob(mul(adj(A),A)) for A in As)
    J=sum(frob(mul(adj(X),X)) for signs in product((-1,1),repeat=len(As))
          for X in [add_all([smul(e,A) for e,A in zip(signs,As)])])*F(1,2**len(As))
    return tuple(q(x).rational() for x in (frob(S),frob(T),D,J))

# Generic rectangular complex check, including covariance asymmetry and sign cross terms.
rng=Random(20261128)
cnt=0
for d,e,m in [(3,1,2),(1,3,4),(2,3,4),(3,2,3),(3,3,4)]:
    for _ in range(4):
        L=[[[rng.randrange(-2,3)+i*rng.randrange(-2,3) for _ in range(e)] for _ in range(d)] for _ in range(m)]
        S,T,D,J=bin_meas(L)
        assert D<=min(S,T)<=max(S,T)<=m*D
        if T>S:
            L=[adj(A) for A in L]; S,T=T,S
        pg=kg=Q()
        for A,B in combinations(L,2):
            U=mul(adj(A),B);V=adj(U)
            pg=pg+frob(add(U,V))
            kg=kg+frob(add(U,V,-1))
        assert J-S==pg and S+2*T-2*D-J==kg
        cnt+=1
assert cnt==20
print("20 exact rectangular fourth-moment identities")

def witnesses(U,V,expected):
    n=len(U)
    assert mul(adj(U),U)==eye(n) and mul(adj(V),V)==eye(n)
    S,T,D,J=bin_meas([eye(n),U,V])
    assert (S,T,D,J)==(9*n,9*n,3*n,9*n+expected)
    print("dimension", n, "deficit", expected)

cx=[[0,i],[i,0]];cz=[[i,0],[0,-i]]
witnesses(cx,cz,0)
z1=(1+c*i)*F(1,2); z2=(-q(1)+c*i)*F(1,2)
witnesses([[z1]],[[z2]],3)
witnesses(direct_sum(cx,[[z1]]),direct_sum(cz,[[z2]]),3)

rx=[[0,-1,0,0],[1,0,0,0],[0,0,0,-1],[0,0,1,0]]
rz=[[0,0,-1,0],[0,0,0,1],[1,0,0,0],[0,-1,0,0]]
witnesses(rx,rz,0)
def rot2(cosine,sine):
    return [[cosine,-sine],[sine,cosine]]
u2=rot2(F(1,2),c*F(1,2));v2=rot2(F(-1,2),c*F(1,2))
witnesses(u2,v2,6)
witnesses(direct_sum(rx,u2),direct_sum(rz,v2),6)

def rot3(u):
    x,y,z=u
    skew=[[0,-q(z),y],[z,0,-q(x)],[-q(y),x,0]]
    return add(skew,[[q(v)*w for w in u] for v in u])
u3=rot3([1,0,0]);v3=rot3([a,b,0])
witnesses([[1]],[[1]],12)
witnesses(u3,v3,12)
print("PASS")
