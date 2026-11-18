"""Finite two-magnitude author checks, using exact binomial fiber counts."""
from itertools import product
from collections import Counter
from math import comb,gcd

def need(p,msg):
    if not p:raise ArithmeticError(msg)
def bvec(n):return [comb(n,j) for j in range(n+1)]
def checkfinite():
    count=0
    for n,m in product(range(1,15),repeat=2):
        x,y=bvec(n),bvec(m)
        for a in range(1,9):
            for b in range(a+1,11):
                if gcd(a,b)!=1:continue
                masses=Counter()
                for i,v in enumerate(x):
                    for j,w in enumerate(y):masses[a*i+b*j]+=v*w
                K=len(masses)
                need(K*max(masses.values())**2<4**(n+m),'finite violation')
                need(K==(n+1)*(m+1)-max(n-b+1,0)*max(m-a+1,0),'fiber count')
                count+=1
    print('PASS finite two-type distributions:',count)

if __name__=='__main__':checkfinite()
