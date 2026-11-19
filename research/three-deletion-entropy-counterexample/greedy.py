"""Separate enumeration: list each host once, then count all its embeddings by DP."""
from itertools import combinations_with_replacement,product
from collections import Counter
from math import comb,prod

def host_words(y,k):
    n=len(y)
    for t in range(k+1):
        for gaps in combinations_with_replacement(range(n),t):
            mult=Counter(gaps)
            u=''.join(('1' if a=='0' else '0')*mult[i]+a for i,a in enumerate(y))
            for tail in product('01',repeat=k-t):
                yield u+''.join(tail)
def embeddings(x,y):
    k=len(x)-len(y);row=[1]+[0]*k
    for i,a in enumerate(x):
        nxt=[0]*(k+1)
        for d,v in enumerate(row):
            if d<k:nxt[d+1]+=v
            j=i-d
            if 0<=j<len(y) and a==y[j]:nxt[d]+=v
        row=nxt
    return row[k]
def run(y):
    k=3; hist=Counter(embeddings(x,y) for x in host_words(y,k))
    total=sum(j*c for j,c in hist.items())
    if min(hist)<=0 or total!=8*comb(67,3) or sum(hist.values())!=50184:
        raise ArithmeticError('canonical host enumeration or mask mass')
    return hist,prod(j**(j*c) for j,c in hist.items())
if __name__=='__main__':
    a,q=run('01'*32);b,r=run('01'*16+'10'*16)
    if q//r!=49091150926384:raise ArithmeticError('Q ratio')
    print('Greedy host enumeration + banded subsequence DP')
    print('A',sorted(a.items()));print('B',sorted(b.items()))
    print('floor(Q(A)/Q(B)) =',q//r)
