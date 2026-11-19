"""Exact check of the two-level exchange identity, including ties and empty slots."""
from itertools import combinations_with_replacement
from functools import lru_cache
from math import comb
@lru_cache(None)
def balanced(n,k):
    if k>n:return 0
    if k==0:return 1
    if n<=1:return n
    return grouped((n//2,n-n//2),k)
@lru_cache(None)
def grouped(pair,k):
    if not k:return 1
    x,y=pair
    if k==1:return x+y
    a,b=k//2,(k+1)//2
    return balanced(x,k)+balanced(y,k)+balanced(x,a)*balanced(y,b)+(balanced(x,b)*balanced(y,a) if a!=b else 0)
def two_level(pair1,pair2,k):
    a,b=k//2,(k+1)//2
    return grouped(pair1,k)+grouped(pair2,k)+grouped(pair1,a)*grouped(pair2,b)+(grouped(pair1,b)*grouped(pair2,a) if a!=b else 0)
def check():
    num=zeros=leaves=0
    for x1,x2,x3,x4 in combinations_with_replacement(range(9),4):
        def U(i,a,j,b):return balanced(i,a)*balanced(j,b)-balanced(i,b)*balanced(j,a)
        for k in range(4,x1+x2+x3+x4+1):
            direct=two_level((x1,x4),(x2,x3),k)-two_level((x1,x2),(x3,x4),k)
            expansions=0
            for d in {k//2,(k+1)//2}:
                b=(k-d)//2;c=k-d-b
                # Equal middle labels have just one order when not distinguished.
                for u,U1 in [(0,d),(d,0)]:
                    for v,V in {(b,c),(c,b)}:
                        expansions+=U(x1,u,x3,v)*U(x2,V,x4,U1)
            if k%4==2:
                t=k//4;expansions+=U(x1,t,x3,t+1)*U(x2,t,x4,t+1)
            if direct!=expansions or min(direct,expansions)<0:raise ArithmeticError((x1,x2,x3,x4,k,direct,expansions))
            num+=1;zeros+=x1==0;leaves+=x1==0 and x2==1
    print("Four-capacity integer identity:", num,"cases,",zeros,"with an empty slot,",leaves,"with a virtual (0,1) child; PASS.")
if __name__=="__main__":check()
