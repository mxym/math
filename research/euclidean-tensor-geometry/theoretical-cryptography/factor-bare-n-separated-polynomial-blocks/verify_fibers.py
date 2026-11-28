"""Fixed finite-fiber algebra examples, with polynomial identities over Q."""
from fractions import Fraction as F
from math import isqrt
from itertools import permutations

def trim(p):
    a=list(map(F,p))
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(p,q):
    a=[F(0)]*max(len(p),len(q))
    for i,v in enumerate(p):a[i]+=v
    for i,v in enumerate(q):a[i]+=v
    return trim(a)
def mul(p,q):
    a=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):a[i+j]+=x*y
    return trim(a)
def minus(p,q):return add(p,[-x for x in q])
def square(p):return mul(p,p)
def ev(p,x):
    z=F(0)
    for c in reversed(p):z=z*x+c
    return z
def prime(n):return n>=2 and all(n%i!=0 for i in range(2,isqrt(n)+1))
def graph(nodes,labels):
    return {(x,y,k) for x,y in permutations(nodes,2)
            for k,(u,v) in enumerate(labels) if ev(u,x)==ev(v,y)}

# Pell edge with both degrees 2, and an unrelated quadratic block.
x,z,y,w=29,41,31,3907
N=x*x*z*y*w*w;S=6*x+10*y
vs=[x,z,y,w];labels=[([-1,0,2],[0,0,1]),([1,2,4],[0,1])]
assert all(map(prime,vs)) and graph(vs,labels)=={(x,z,0),(y,w,1)}
Y=[F(S,10),F(-6,10)]
V=add([1],add(mul([2],Y),mul([4],square(Y))))
A=mul([0,0,1],mul(Y,square(V)))
h=[-1,0,2]     # z^2=h(X)
D=minus([N*N],mul(square(A),h))
assert len(D)-1==16 and ev(D,x)==0 and ev(A,x)*z==N and ev(A,x)*(-z)!=N
for t in range(-20,220):
    a=ev(A,t);u=ev(h,t)
    # Matrix of (A z -N) in basis 1,z over the specified fiber.
    B=[[-N,a*u],[a,-N]]
    assert B[0][0]*B[1][1]-B[0][1]*B[1][0]==ev(D,t)
roots=[t for t in range(2,1001) if ev(D,t)==0]
assert roots==[29]
print("Pell plus non-binomial block: norm degree / exact roots in [2,1000]",len(D)-1,roots)

# At X=5, w=z-7 is a nonzero nilpotent: w^2=X-5. The specialization
# has one geometric value rather than two, yet the norm detects it.
N=35;h=[-5,1];xx=[0,1];a=[-N,7]
D=minus(square(a),mul(square(xx),h))
assert ev(D,5)==0 and len(D)-1==3
for i in range(-19,251):
    m=[[ev(a,i),i*ev(h,i)],[i,ev(a,i)]]
    assert m[0][0]*m[1][1]-m[0][1]*m[1][0]==ev(D,i)
assert [i for i in range(2,36) if ev(D,i)==0]==[5]
print("nonreduced fiber: specialization, norm degree",5,len(D)-1)

# 5 -> 7 with a square-root edge, then 7 -> 101 via a monic-output quadratic.
U=[5,7,101,11];labels=[([-1,10],[0,0,1]),([3,0,2],[0,1])]
assert all(map(prime,U)) and graph(U,labels)=={(5,7,0),(7,101,1)}
print("two-stage fractional-degree path / isolated anchor",U[:3],U[3])
