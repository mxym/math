"""Exact independent certificate for the stated three-deletion-channel comparison."""
from collections import Counter
from itertools import combinations
from math import comb, prod

def hist(y):
    T=len(y)+3
    v=int(y,2)
    hosts=Counter()
    def blank(x,i):
        return ((x>>i)<<(i+1))|(x&((1<<i)-1))
    for i,j,k in combinations(range(T),3):
        w=blank(blank(blank(v,i),j),k)
        a,b,c=(1<<i),(1<<j),(1<<k)
        for u in (0,a,b,a|b,c,c|a,c|b,c|a|b):
            hosts[w|u]+=1
    if sum(hosts.values()) != 8*comb(T,3):
        raise ArithmeticError("normalization")
    return Counter(hosts.values())
n=64
a=hist('01'*32)
b=hist('01'*16+'10'*16)
pos={k:k*(a[k]-b[k]) for k in a.keys()|b.keys() if a[k]!=b[k]}
P=prod(k**t for k,t in pos.items() if t>0)
Q=prod(k**(-t) for k,t in pos.items() if t<0)
if not P>Q:
    raise ArithmeticError("not a strict counterexample")
print('alternating', sorted(a.items()))
print('doubled', sorted(b.items()))
print('PASS strict comparison of exact integer products with lengths 64 and 67')
