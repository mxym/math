"""Exact finite checks supporting the written proof. Python standard library only."""
from fractions import Fraction as F
from itertools import product
from math import comb

def eq(a,b):
    if a!=b:
        raise ArithmeticError((a,b))
def pos(x):
    if x<=0:
        raise ArithmeticError(x)

def factor(p,L,s):
    """Tilted marginal via direct two-region integration in (x,y).
    Original density proportional to exp(-x-y) and normalization of Z tilt p.
    Region x >= M*y/L: integrate x from M*y/L to infinity (then y).
    Other region y >= L*x/M: integrate y first (then x).
    """
    M=1-L
    r= p-s
    # Positive region: exponent in integrand -r*x -(1+(1-p)*M/L)*y .
    # Check sign directly: exp((1-p)(L*x-M*y)/L).
    term_pos=p/(r*(1+(1-p)*M/L+r*M/L))
    # Negative region: exp((1-p)(M*y-L*x)/M).
    term_neg=p/(p*(1-s+(1-p)*L/M+p*L/M))
    return term_pos+term_neg

def mixture(p,L,s):
    M=1-L
    A=L/(1-M*p)
    return A*p/(p-s)+(1-A)/(1-M*s)

grid=[F(i,j) for j in range(2,11) for i in range(1,j)]
grid=sorted(set(grid))
nc=0
for p,L,q in product(grid,grid,[F(1,3),F(2,3),F(9,10),F(99,100),F(0)]):
    s=p*q
    eq(factor(p,L,s),mixture(p,L,s))
    M=1-L
    A=L/(1-M*p)
    eq(A/p+(1-A)*M,M+L/p)
    nc+=1
for p,n in product(grid,list(range(2,13))):
    M=(1-p)**3/4; L=1-M
    A=L/(1-M*p); B=M/(1-L*p)
    pos(1-A**n-B**n)
    # finite choice of s certified by exact growth and rational arithmetic
    for j in range(1,80):
        s=p*(1-F(1,2**j))
        D=(p/(p-s))**n+(1/(1-s))**n-factor(p,L,s)**n-factor(p,M,s)**n
        if D>0:break
    else:raise ArithmeticError((n,p))

p,s,L,n=F(4,7),F(9,16),F(1,2),2
P,U=(p/(p-s))**n,(1/(1-s))**n
Q=factor(p,L,s)**n
D=P+U-2*Q
for a,b in zip((P,U,Q,D,p/(1-p)*D),(4096,F(256,49),F(1081600,529),F(311040,25921),F(414720,25921))):
    eq(a,b)
d=F(1,126);v=s*(1+d)
eq(v,F(127,224))
K=(p/(p-v))**n+(1/(1-v))**n+P*U
eq(K,F(17422205952,461041))
eq(1512*d,12)
pos(D-K/4096)
ratio=comb(2*n,n)*F(2,1)/((2*p+1)*(2*p+2))
eq(ratio,F(98,55))
eq(64*55**7-98**7,10623301675328)
print(f'{nc} joint-integral/mixture evaluations and {11*len(grid)} weighted witnesses passed.')
print(f'P={P} U={U} Q={Q} D={D} Jprime={p/(1-p)*D}')
print(f'K={K}  D-K/4096={D-K/4096}>0;  triangle has strictly smaller gap.')
