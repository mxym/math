"""Finite fail-closed stress tests. Integer arithmetic only, including log sign tests.
Standard library only. This is not a global maximization or a proof over all r,n."""
from math import comb
from itertools import combinations_with_replacement
from collections import Counter
from functools import cache

def need(t,msg):
    if not t: raise RuntimeError(msg)

@cache
def row(m):
    return tuple(comb(m,j) for j in range(m+1))

@cache
def factors(k):
    p=2; e={}
    while p*p<=k:
        while k%p==0:
            e[p]=e.get(p,0)+1;k//=p
        p+=1
    if k>1:e[k]=1
    return e

@cache
def lrow(m):
    # coefficients in the prime-logarithm expansion of 2^m L_m(k)
    b=row(m);mu=Counter()
    for c in b:
        for p,e in factors(c).items():mu[p]+=c*e
    return [{p:(1<<m)*factors(c).get(p,0)-e for p,e in mu.items()} for c in b]

@cache
def loglower(p,bits):
    # 2^bits log2 p lies in [floor, floor+1), from length of p^(2^bits).
    return pow(p,1<<bits).bit_length()-1

def nonneg(exps):
    exps={p:e for p,e in exps.items() if e}
    if not exps:return True
    for bits in (6,10,14,18):
        lo=sum(e*(loglower(p,bits)+(e<0)) for p,e in exps.items())
        hi=sum(e*(loglower(p,bits)+(e>0)) for p,e in exps.items())
        if lo>=0:return True
        if hi<0:return False
    raise ArithmeticError(f'unresolved sign: {exps}')

def convint(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out

def signs_count(js,r):
    dist=[1]
    for u in js:
        b=[0]*(r+1);b[u]+=1;b[r-u]+=1;dist=convint(dist,b)
    return dist

def check(n,r,js):
    c=signs_count(js,r); m=n-1;den=1<<n
    need(sum(c)==den and c==c[::-1],'unnormalized or asymmetric')
    bc=row(m)
    for j in range(1,m//2+1):
        need(sum(c[(n-j)*r+1:])<=2*sum(bc[:j]),'bad sign tail')
    ex=Counter()
    for s,hits in enumerate(c):
        if not hits:continue
        v= lrow(m if s%r else n)[s//r]
        scale=hits*(2 if s%r else 1) # scores share denominator 2^n
        for k,a in v.items():ex[k]+=scale*a
    need(nonneg(ex),f'negative mixed score, {n,r,js,ex}')
    return 1 if all(a==0 for a in ex.values()) else 0

def main():
    need(not nonneg({2:1,3:-1}),'negative sign control')
    need(nonneg({2:-3,3:2}),'positive sign control')
    case=eq=bound=0
    for n in range(1,9):
      for k in range(1,n):
        v=Counter()
        for p,a in lrow(n)[k].items():v[p]+=a
        for t in (k-1,k):
          for p,a in lrow(n-1)[t].items():v[p]-=a
        # scale is 2^n for the midpoint inequality.
        need(nonneg(v),'grid midpoint');bound+=1
      for r in range(1,13):
        seen=0
        for js in combinations_with_replacement(range(r//2+1),n):
            eq+=check(n,r,js);case+=1;seen+=1
        need(seen==comb(n+r//2,n),'incomplete amplitude inventory')
    print(f'PASS: {case} pure sign-amplitude profiles for 1≤n≤8,1≤r≤12; {eq} exact zero scores; {bound} midpoint checks; two sign controls.')
if __name__=='__main__':main()
