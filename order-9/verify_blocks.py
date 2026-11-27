#!/usr/bin/env python3
"""Exact orthogonal-sum witnesses, in Q(i) and Q(zeta_35), without floats."""
from collections import Counter
from itertools import combinations, product

def polyprod(a,b):
    h=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): h[i+j]+=x*y
    return h

def xnm1(n):
    return [-1]+[0]*(n-1)+[1]

def exact_div(a,b):
    a=a[:];q=[0]*(len(a)-len(b)+1)
    assert b[-1]==1
    for s in range(len(q)-1,-1,-1):
        q[s]=a[s+len(b)-1]
        for j in range(len(b)): a[s+j]-=q[s]*b[j]
    assert not any(a)
    return q

class Cyc:
    def __init__(self,n,P):
        self.n=n;self.P=P;self.d=len(P)-1
        assert P[-1]==1
        self.zero=self.c(0);self.one=self.c(1)
        self.roots=[self.one];X=(0,1)+(0,)*(self.d-2)
        for _ in range(1,n):
            self.roots.append(self.mul(self.roots[-1],X))
        assert self.mul(self.roots[-1],X)==self.one
        assert len(set(self.roots))==n
    def c(self,x):
        return (x,)+(0,)*(self.d-1)
    def mul(self,x,y):
        h=[0]*(2*self.d-1)
        for i,a in enumerate(x):
            if a:
                for j,b in enumerate(y):
                    if b: h[i+j]+=a*b
        for i in range(len(h)-1,self.d-1,-1):
            if h[i]:
                for j,a in enumerate(self.P[:-1]):
                    if a: h[i-self.d+j]-=h[i]*a
        return tuple(h[:self.d])
    def bar(self,x):
        return self.add(*(tuple(c*q for q in self.roots[(-i)%self.n]) for i,c in enumerate(x)))
    def add(self,*xs):
        return tuple(map(sum,zip(*xs))) if xs else self.zero
    def phase(self,n,k):
        assert self.n%n==0
        return self.roots[((self.n//n)*k)%self.n]
    def dot(self,a,b):
        return self.add(*(self.mul(self.bar(x),y) for x,y in zip(a,b)))

F=Cyc(4,[1,0,1])
G=Cyc(35,exact_div(polyprod(xnm1(35),xnm1(1)),polyprod(xnm1(5),xnm1(7))))
assert G.d==24

def e(K,n,i):
    return tuple(K.c(int(i==j)) for j in range(n))

def scalar(K,x,v):
    return tuple(K.mul(x,a) for a in v)

def sum_vec(K,vs):
    return tuple(K.add(*cs) for cs in zip(*vs))

def zero_case(n):
    return tuple(tuple((j-i)%n for j in range(n)) for i in range(n))

def Hplus(K,n,s):
    return [[tuple(K.phase(n,k*a+s[k]*b) for k in range(n)) for b in range(n)]
            for a in range(n)]

P4=Hplus(F,4,(0,1,3,2))
R0=Hplus(G,5,(0,1,2,4,3))
R=R0[1:]+R0[:1]
W=R[4]
B4=[e(F,4,i) for i in range(4)]

def puncture(T,rotate=False,basis=B4):
    assert len(T)==5 and all(len(r)==5 for r in T)
    assert all(set(r)==set(range(5)) for r in T)
    assert all({T[i][j] for i in range(5)}==set(range(5)) for j in range(5))
    assert all(T[i][i]==4 for i in range(5))
    ans={}
    for i,j in product(range(5),repeat=2):
        if i==j: continue
        s=T[i][j]
        if rotate and i in (0,1) and j in (3,4):
            assert s in (0,1)
            ans[i,j]=sum_vec(F,[B4[0],scalar(F,F.c((-1)**s),B4[1])])
        else:
            ans[i,j]=basis[s]
    return ans

T=((4,3,2,1,0),(2,4,3,0,1),(1,0,4,3,2),(0,2,1,4,3),(3,1,0,2,4))
T0=tuple(tuple(4 if i==j else (j-i)%5-1 for j in range(5)) for i in range(5))

def p6rotate():
    out={}
    for i,j in product(range(4),repeat=2):
        s=i^j
        if i<2 and j<2:
            v=sum_vec(F,[B4[0],scalar(F,F.c((-1)**s),B4[1])])
        else:
            v=B4[s]
        # Integer multiple 3 of Householder W on coordinates 0,1,2; fixes last ray.
        sm=F.add(*v[:3])
        hh=tuple(F.add(F.mul(F.c(3),v[i]),F.mul(F.c(-2),sm)) for i in range(3))
        out[i,j]=hh+(F.mul(F.c(3),v[3]),)
    return [[out[i,j] for j in range(4)] for i in range(4)]

def shiftbasis(v):
    components=[scalar(G,G.mul(G.phase(7,j),G.dot(w,v)),w) for j,w in enumerate(W)]
    return sum_vec(G,components)

S_classical=[[W[(b+a+1)%5] for a in range(5)] for b in range(5)]
S_max=[[shiftbasis(R[a][b]) if a<4 else W[b] for a in range(5)] for b in range(5)]

def fill(P,T,S):
    A={}
    for i,j in product(range(9),repeat=2):
        if i<4 and j<4:A[i,j]=(0,P[i][j])
        elif i<4:A[i,j]=(1,R[i][j-4])
        elif j<4:A[i,j]=(1,S[i-4][j])
        elif i==j:A[i,j]=(1,W[i-4])
        else:A[i,j]=(0,T[i-4,j-4])
    return A

def ray(x,y):
    if x[0]!=y[0]:return False
    K=(F,G)[x[0]]
    u,v=x[1],y[1]
    su=tuple(i for i,z in enumerate(u) if z!=K.zero)
    sv=tuple(i for i,z in enumerate(v) if z!=K.zero)
    if su!=sv:return False
    z=su[0]
    return all(K.mul(u[i],v[z])==K.mul(v[i],u[z]) for i in su[1:])

def check(i,P,T,S,want):
    A=fill(P,T,S)
    gram=0
    for a in range(9):
        for side in (0,1):
            row=[A[a,b] if side==0 else A[b,a] for b in range(9)]
            assert Counter(t for t,_ in row)=={0:4,1:5}
            for x,(_,u) in enumerate(row):
                t=row[x][0];K=(F,G)[t]
                assert K.dot(u,u)!=K.zero
                for s,v in row[x+1:]:
                    if s==t:assert K.dot(u,v)==K.zero
                gram+=9-x
    assert gram==810
    group={k:k for k in A}
    def root(x):
        while group[x]!=x: x=group[x]
        return x
    pairs=0
    for j,k in combinations(A,2):
        if ray(A[j],A[k]):group[root(k)]=root(j)
        pairs+=1
    assert pairs==3240
    part=Counter(root(x) for x in A)
    counts=Counter(A[x][0] for x in part)
    assert (counts[0],counts[1])==want
    assert len(part)==i
    print(f"blocks {i}: U,V={want}; 810 Gram entries, 3240 pairs; multiplicities {sorted(Counter(part.values()).items())}")

check(34,p6rotate(),puncture(T0),S_classical,(9,25))
check(61,P4,puncture(T0,basis=P4[0]),S_max,(16,45))
check(67,P4,puncture(T,rotate=True),S_max,(22,45))
print("blocks negative control: replace the second maximum square by its aligned basis square")
check(41,P4,puncture(T0,basis=P4[0]),S_classical,(16,25))
