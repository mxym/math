"""Fail-closed standard-library exact finite checks, not a proof by sampling."""
from fractions import Fraction as Q
from collections import Counter
from itertools import product
from math import comb,factorial

def need(x,name):
    if not x: raise ArithmeticError(name)

def stencil(orders):
    u=Counter()
    for i in product(*(range(k+1) for k in orders)):
        c=1
        for k,j in zip(orders,i):c*=(-1)**(k-j)*comb(k,j)
        u[i]+=c
    return u

def physical(v,a=Q(1,3),h=Q(1,100)):
    s,x,z=(h*u for u in v);d=a+s+z;e=a+s-z;b=1-2*a-2*s
    need(d>0 and d*e>x*x and b>0 and d+e+b==1,'strict density')
    return [[d,x,Q(0)],[x,e,Q(0)],[Q(0),Q(0),b]]

def trace_power(A,n):
    M=[[Q(i==j) for j in range(3)] for i in range(3)]
    for _ in range(n):
        M=[[sum(M[i][k]*A[k][j] for k in range(3)) for j in range(3)]for i in range(3)]
    return sum(M[i][i] for i in range(3))

def trial(S,target):
    need(sum(S.values())==0,'zero mass')
    marg=Counter()
    for (s,x,z),c in S.items():marg[s]+=c
    need(all(k==0 for k in marg.values()),'entire scalar block cancels for any function')
    points={u:physical(u) for u in S}
    mid=Counter()
    for u,c in S.items():
        for v,d in S.items():mid[tuple(Q(i+j,2) for i,j in zip(u,v))]+=c*d
    for m in range(7):
        value=sum(c*trace_power(physical(k),m) for k,c in mid.items())
        need(value==(Q(target,64)*Q(1,100)**6 if m==6 else 0),'direct matrix power/value')
    return len([k for k,v in S.items() if v])

def scalar(m):
    a=Q(1,3);h=Q(1,120)
    def f(t):return t**m
    def phi(x,y):
        z=(x+y)/2;return f(z)+2*f((1-z)/2)
    def row(k):
        return [(a+j*h,(-1)**(k-j)*comb(k,j)) for j in range(k+1)]
    def pair(r,s):return sum(c*d*phi(x,y) for x,c in row(r) for y,d in row(s))
    mixed=pair(1,m-1)
    need(pair(m-1,m-1)==0 and mixed==Q(factorial(m),2**m)*h**m*(1+2*Q(-1,2)**m) and mixed!=0,'zero-norm scalar contrast')

def main():
    plus=stencil((0,3,0)); minus=stencil((2,1,0));minus.subtract(plus);minus.subtract(stencil((0,1,2)))
    p=trial(plus,1440);m=trial(minus,-96)
    for n in (3,4,5):scalar(n)
    print(f'PASS: positive/negative cubic stencils use {p}/{m} nonzero-coefficient full-rank qutrits; powers 0 through 5 cancel and sixth values are 1440 and -96 after normalization. Scalar Gram obstructions in degrees 3,4,5 verified exactly.')
if __name__=='__main__': main()
