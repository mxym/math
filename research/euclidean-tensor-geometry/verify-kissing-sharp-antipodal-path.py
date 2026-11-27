"""Exact, dependency-free check of the sharp antipodal path certificate.
Run: python3 verify-kissing-sharp-antipodal-path.py
Arithmetic is in Q[u]/(16u^4-16u^3-4u^2+10u-5), with rational intervals.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext
from itertools import permutations

M = (F(-5), F(10), F(-4), F(-16), F(16))
def P(*x): return tuple(F(i) for i in x) + (F(0),)*(4-len(x))
O, Z, u = P(1), P(0), P(0,1)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a,neg(b))
def scale(a,c): return tuple(x*c for x in a)
def mul(a,b):
    v=[F(0)]*7
    for i,x in enumerate(a):
        for j,y in enumerate(b): v[i+j]+=x*y
    for k in range(6,3,-1):
        d=v[k]/16
        for i in range(5): v[k-4+i]-=d*M[i]
    return tuple(v[:4])
def sm(x): return __import__('functools').reduce(add,x,Z)
def hor(c,t):
    s=F(0)
    for v in reversed(c): s=s*t+v
    return s
def interval(a,l,h):
    x=y=F(0)
    for v in reversed(a):
        z=[x*l,x*h,y*l,y*h];x=min(z)+v;y=max(z)+v
    return x,y
l,h=F(-82,100),F(-81,100)
assert hor(M,l)>0>hor(M,h)
assert interval([i*M[i] for i in range(1,5)],l,h)[1]<0
for _ in range(90):
    m=(l+h)/2
    if hor(M,m)>0:l=m
    else:h=m
def positive(a): return interval(a,l,h)[0]>0
def det(A):
    n=len(A);terms=[]
    for p in permutations(range(n)):
        a=O
        for i,j in enumerate(p): a=mul(a,A[i][j])
        inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        terms.append(neg(a) if inv%2 else a)
    return sm(terms)
def tr(A): return list(zip(*A))
def mm(A,B): return [[sm(mul(x,y) for x,y in zip(r,c)) for c in tr(B)] for r in A]
# N_j/D = (1-1/D)(-1)^j + T_j(u)/D.
D=scale(sub(O,mul(u,u)),4);assert positive(sub(D,O))
T=[O,u]
for _ in range(2,11): T.append(sub(scale(mul(u,T[-1]),2),T[-2]))
N=[add(scale(sub(D,O),(-1)**j),T[j])for j in range(11)]
assert N[0]==D
assert mul(scale(sub(O,u),4),add(D,N[1]))==D
for j in (2,5): assert scale(N[j],2)==D
for j in (1,3,4,6,7,8,9): assert positive(sub(D,scale(N[j],2)))
assert positive(sub(scale(N[10],2),D)) and positive(sub(D,N[10]))
for j in range(1,11): assert positive(sub(D,N[j]))
assert positive(sub(neg(N[1]),scale(D,F(86238,100000))))
assert positive(sub(scale(D,F(86240,100000)),neg(N[1])))
assert positive(sub(scale(mul(N[1],N[1]),3),scale(mul(D,D),2)))
assert positive(sub(scale(mul(D,D),3),scale(mul(N[1],N[1]),4)))
# R columns support shifted copies of (1,v,v,1).
v=sub(O,scale(u,2));A=mul(v,sub(v,O));B=neg(v);C=mul(v,v)
H=[[A,B,O],[B,C,B],[O,B,A]]
R=[[Z for _ in range(3)]for _ in range(6)]
for j in range(3):
    for k,p in enumerate([O,v,v,O]):R[j+k][j]=p
Q=mm(mm(R,H),tr(R))
for j in (1,2,3):assert positive(det([r[:j] for r in H[:j]]))
for i in range(6):
    for j in range(i+1,6):
        if j-i in (1,2,5):assert positive(Q[i][j])
        else:assert Q[i][j]==Z
G=[[N[abs(i-j)]for j in range(6)]for i in range(6)]
assert all(x==Z for r in mm(tr(R),G)for x in r)
assert positive(det([r[:3]for r in G[:3]]))
# The rank-three Gram saturates the dual pairing exactly; intervals are only
# for strict signs, not substituted for algebraic equalities.
assert sm(mul(Q[i][j],G[i][j])for i in range(6)for j in range(6))==Z
with localcontext() as ctx:
    ctx.prec=25
    def d(x):return Decimal(x.numerator)/Decimal(x.denominator)
    m=(l+h)/2;print('u ~',d(m),'a* ~',d(1-1/(4*(1-m))))
    print('dot products at steps 1..10:',*[round(d(hor(n,m)/hor(D,m)),10)for n in N[1:]])
print('PASS: primal contacts; PSD dual support; three recurrence relations; strict and closed path thresholds.')
