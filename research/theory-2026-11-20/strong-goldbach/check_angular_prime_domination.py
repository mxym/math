"""Exact guards for the numerical branches and reserve; not an analytic proof checker."""
from fractions import Fraction as F
from itertools import combinations,product
def need(f,s):
    if not f: raise ArithmeticError(s)
th=F(7,32); alpha=F(1001,1000); v=F(531,1000)
lo,hi=F(64,1000),F(18,100)
need((1+lo)/2>v and (1-(F(3,2)-2*th)*hi)/(1+th)>v and 1-(alpha*th+3*hi)/2>v,'large-t1')
need(lo<min((1-th)/(4-3*th),(1-alpha*th)/4),'mu')
need(min(((5-4*th)-(3-4*th)*lo)/(8-6*th),(5-alpha*th-3*lo)/8,1-2*lo)>F(57,100)>(1+lo)/2,'w')
def score(a):
    den=sum(a)**2; d=sum(a)
    return sum((-1)**j*sum(max(0,d-2*sum(sub))**2 for sub in combinations(a,j)) for j in range(len(a)+1))/F(den)
n=0
for rank in (2,3):
    for a in product(range(1,17),repeat=rank):
        if tuple(sorted(a))!=a: continue
        v=tuple(F(y,sum(a)) for y in a)
        expected=4*v[0]*(1-v[0]) if rank==2 else 8*v[0]*v[1] if v[-1]>F(1,2) else 2-4*sum(t*t for t in v)
        need(expected==score(a) and expected>=0,'physical score'); n+=1
# Machin pi=16 atan(1/5)-4 atan(1/239); alternating upper/lower
piup=16*sum((-1)**j*F(1,5)**(2*j+1)/(2*j+1) for j in range(7))-4*(F(1,239)-F(1,3*239**3))
# log(2)=2atanh(1/3)
loglo=2*sum(F(1,3)**(2*j+1)/(2*j+1) for j in range(9))
i3lo=4*loglo-piup**2/6
need(F(12,53)*(2+i3lo)>F(7,10),'reserve')
need(3*(2+i3lo)-9>F(38,100),'residual')
print('Exact checks passed:',n,'true rank profiles; worst-exponent packing margins; HH > 0.70 and residual HL > 0.38.')
