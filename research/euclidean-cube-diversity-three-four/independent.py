"""Rational, no-Taylor sign certificates for the d=3,4 cube threshold proof.
The proof differs from its author's 2048-cell three-region sign certificate.
In each case F is concave in the first quarter and decreasing in the second.
Uses only Python standard library; active also under python -O.
"""
from fractions import Fraction as Q
from math import isqrt, comb
from functools import lru_cache

def check(p, message):
    if not p: raise ArithmeticError(message)
def floor(x,b): return Q((x*b).__floor__(),b)
def ceil(x,b): return Q((x*b).__ceil__(),b)
@lru_cache(None)
def root(x,b):
    a=Q(isqrt((x*b*b).__floor__()), b)
    return a, a if a*a==x else a+Q(1,b)
@lru_cache(None)
def decay(x,p=12,b=10**9):
    m=2**p
    check(0<=x<m,'nonnegative lower exponential bound required')
    # 1-x/m <= e^(-x/m) <= (1+x/m)^(-1). All bounds positive.
    v,w=1-x/m, 1/(1+x/m)
    for _ in range(p):
        v,w=floor(v*v,b),ceil(w*w,b)
    return v,w
def brack(s,d,upper):
    b=10**20; ans=Q(-1)
    for k in range(d):
        r,R=root(Q(k+1),b)
        v=decay(s*r,25,b)[1]/r if upper else decay(s*R,25,b)[0]/R
        ans+=comb(d-1,k)*v
    return ans
def derivs(d,sl,su,l,u):
    # Sum H' and H'' over the binomial Hamming layers; k=0 nonsingular form separate.
    alo=decay(su*u)[0]; ahi=decay(sl*l)[1]
    L,U,T,V=-su*ahi,-sl*alo,sl*sl*alo,su*su*ahi
    for k in range(1,d):
        r=root(k+l*l,10**8)[0]; R=root(k+u*u,10**8)[1]
        z=comb(d-1,k); c=decay(su*R)[0]; C=decay(sl*r)[1]
        L+=z*(k*c/R**3-su*C*(u/r)**2)
        U+=z*(k*C/r**3-sl*c*(l/R)**2)
        T+=z*(sl**2*c*(l/R)**3-3*k*C*u/r**5-3*su*k*C*u/r**4)
        V+=z*(su**2*C*(u/r)**3-3*k*c*l/R**5-3*sl*k*c*l/R**4)
    return L,U,T,V
def run(d,a,b):
    sl,su=Q(a,100000),Q(b,100000)
    x,y=brack(sl,d,False),brack(su,d,True)
    check(x>0>y, 'root bracket')
    print('dimension',d,'bracket signs, times 1e9:',(x*10**9).__floor__(),(y*10**9).__ceil__())
    n=512; left=[]; right=[]
    for i in range(n//2):
        l,u=Q(i,n),Q(i+1,n)
        A=derivs(d,sl,su,l,u); B=derivs(d,sl,su,1-u,1-l)
        if u<=Q(1,4):
            left.append(B[3]-A[2])   # upper bound F''(t)
        else:
            right.append(-A[0]-B[0]) # upper bound F'(t)
    check(len(left)==len(right)==128,'partition')
    check(max(left)<-Q(1,8) and max(right)<-Q(1,80),'concavity/decrease')
    print("upper bounds F''([0,1/4]) and F'([1/4,1/2]), times 1e6:",
        (max(left)*10**6).__ceil__(),(max(right)*10**6).__ceil__())
if __name__=='__main__':
    run(3,83811,83812);run(4,116444,116445)
    print('PASS. In each dimension, 128 + 128 closed cells cover the entire half edge.')
