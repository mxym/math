"""Exact finite-constant and small quadratic overlap checks."""
from fractions import Fraction as F
from collections import Counter
from itertools import product
from random import Random

if not __debug__:
    raise RuntimeError("Run without -O")

# Strict elementary numerical inequalities for delta=667/5000.
D=F(667,5000)
s6=F(24494897,10**7);s2=F(14142135,10**7)
assert s6*s6<6 and s2*s2<2
rho=F(37137,50000)  # 0.74274
assert ((1-D)*s6+(1-3*D)*s2)/4>rho
h=F(2837,20000)
hw=2*rho*rho
assert hw.numerator**h.denominator > hw.denominator**h.denominator*2**h.numerator
ell=F(317,200)
assert 3**ell.denominator < 2**ell.numerator

# For k=2 floor(7n/50) and s=2k+2, sufficient margin is A n^2-B n-C.
A=F(98,625)*h-F(3,1250)-ell/80
B=F(56,25)*h+F(3,50)+F(28,25)+1
C=F(35,8)
assert (A,B,C)==(F(1479,50000000),F(312218,125000),F(35,8))
n=100000
assert A*n*n-B*n-C>0 and 2*A*n-B>0
assert 8+2*5<=32 and 2**(32//4)>33
assert (F(34,33))**4<2
print("finite 13.34% margin passed")

def linear(A,x):
    y=0
    for j,c in enumerate(A):
        if (x>>j)&1:y^=c
    return y
def dot(x,y):return (x&y).bit_count()%2
def loss_radical(A,B):
    d=len(A)
    k=[sum((dot(a,b)^dot(x,y))<<j for j,(b,y) in enumerate(zip(A,B))) for a,x in zip(A,B)]
    K=[z for z in range(1<<d) if all(not dot(a,z) for a in k)]
    return (len(K).bit_length()-1,K)
def span(A):
    S={0}
    for a in A:S|={x^a for x in S}
    return S
def inj(k,d):
    def dfs(A,S):
        if len(A)==d:
            yield tuple(A);return
        for z in range(1,1<<k):
            if z not in S:yield from dfs(A+[z],S|{x^z for x in S})
    return dfs([],{0})
def gram(A):
    return tuple(sum(dot(x,y)<<j for j,y in enumerate(A)) for x in A)

seen=0;injs=0
for k in range(1,5):
    for d in range(1,min(3,k)+1):
        cnt=Counter(map(gram,inj(k,d)))
        assert sum(cnt.values())==__import__("math").prod(2**k-2**a for a in range(d))
        assert max(cnt.values())*2**(d*(d-1)//2) <=4*sum(cnt.values())
        injs+=sum(cnt.values())
        rng=Random(123456+k*10+d)
        M=list(inj(k,d))
        for _ in range(60):
            A,B=rng.choice(M),rng.choice(M)
            rad,K=loss_radical(A,B)
            assert len(K)==1<<rad
            q=[(linear(A,x).bit_count()-linear(B,x).bit_count())%4 for x in range(1<<d)]
            assert all(q[z]%2==0 for z in K)
            for x in range(1<<d):
                a=b=0
                for y in range(1<<d):
                    ch=(q[y]+2*dot(x,y))%4
                    a+=(ch==0)-(ch==2);b+=(ch==1)-(ch==3)
                succeed=all(2*dot(x,y)==q[y] for y in K)
                assert a*a+b*b==((1<<(d+rad)) if succeed else 0)
            seen+=1
assert seen==540
print("quadratic Gauss rank samples",seen,"ordered embedding census",injs)
print("PASS")
