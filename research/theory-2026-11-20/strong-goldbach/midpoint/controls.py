"""Exact discrete controls on divisor complement algebra (not the analytic proof).
Here integer lengths replace normalized logs since only subsets and complements
are tested; a piecewise-linear symmetric profile substitutes for the smooth one.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement

def check(ok):
    if not ok: raise ArithmeticError("control failed")

def f(z):
    return min(Q(1),max(Q(0),(Q(51,100)-z)/Q(2,100)))

def raw(xs):
    poly=[1]
    for x in xs:
        a=poly+[0]*x
        for i,c in enumerate(poly): a[i+x]-=c
        poly=a
    t=sum(xs)
    return sum(c*f(Q(k,t)) for k,c in enumerate(poly) if c)

def main():
    n=0
    for j in range(1,8):
        for xs in combinations_with_replacement(range(1,9),j):
            u=raw(xs); n+=1
            if j==1: check(u==1)
            elif j%2==0 or Q(max(xs),sum(xs))>=Q(51,100):
                check(u==0)
            if j==3:
                z=sum(f(Q(x,sum(xs))) for x in xs)-2
                check(z>=0 and -u==2*z)
    for j,result in [(3,1),(5,-3),(7,10),(9,-35)]:
        check(raw((1,)*j)==-2*result)
    print(n,"discrete profiles; balanced J ranks 3,5,7,9 = 1,-3,10,-35")
if __name__=="__main__": main()
