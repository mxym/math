"""Finite certificate tests: no external data and no input parameters."""
from fractions import Fraction as Q
from itertools import combinations
from math import gcd, isqrt, prod

def prime(n):
    return n>=2 and all(n%i for i in range(2,isqrt(n)+1))

def edges(S,vs):
    return [(p,q,(q-1)//p) for p in vs for q in vs
            if q>p and (q-1)%p==0 and (q-1)//p in S]

def components(vs,es):
    blocks=[{v} for v in vs]
    for p,q,_ in es:
        a=next(b for b in blocks if p in b); b=next(b for b in blocks if q in b)
        if a is not b:
            blocks.remove(b);a.update(b)
    return sorted(tuple(sorted(b)) for b in blocks)

def forms(root,es):
    ll={root:(Q(1),Q(0))}
    for _ in range(len(es)):
        for p,q,m in es:
            if p in ll and q not in ll:
                a,b=ll[p];ll[q]=m*a,m*b+1
            if q in ll and p not in ll:
                a,b=ll[q];ll[p]=a/m,(b-1)/m
    return ll

def bisect_fixed(ll,ee,N):
    ceil=lambda t: -((-t.numerator)//t.denominator)
    left=max([2]+[ceil((2-b)/a) for a,b in ll.values()])
    right=min([N]+[((N-b)/a).__floor__() for a,b in ll.values()])
    def val(t): return prod((a*t+b)**ee[v] for v,(a,b) in ll.items())
    while left<=right:
        m=(left+right)//2
        if val(m)==N:return m
        if val(m)<N:left=m+1
        else:right=m-1
    return None

pr=[n for n in range(2,44) if prime(n)]
subsets=trees=anchored=0
for s in range(1,5):
    for vs in combinations(pr,s):
        subsets+=1
        es=edges({1,2,4,6,10},vs)
        for b in components(vs,es):
            sub=[r for r in es if r[0] in b]
            for tree in combinations(sub,len(b)-1):
                if len(components(b,tree))!=1:continue
                trees+=1
                for x in b:
                    anchored+=1
                    ll=forms(x,tree)
                    assert set(ll)==set(b)
                    assert all(a>0 and a*x+h==v for v,(a,h) in ll.items())
                    if x==min(b):
                        assert all(abs(h/a)<=len(b)*2**len(b) for a,h in ll.values())
print("small prime subsets / component spanning trees / all anchor choices",subsets,trees,anchored)

for vs,S,tree,root,ee in [
    ([3,5,31],{6,10},[(3,31,10),(5,31,6)],3,{3:3,5:2,31:1}),
    ([5,7,29,1741],{4,60,348},[(5,1741,348),(29,1741,60),(7,29,4)],5,{5:2,7:1,29:3,1741:1})]:
    assert all(prime(p) for p in vs) and set(edges(S,vs))==set(tree)
    ll=forms(root,tree); value=prod(v**ee[v] for v in vs)
    assert bisect_fixed(ll,ee,value)==root
    assert bisect_fixed(ll,ee,value+1) is None
    if root==5:
        a,b=ll[7];assert b/a==Q(-5,29)
print("two mixed-direction / reversed-tree fixtures exact; negative shift",-Q(5,29))

# Pocklington step: for each prime r | F | n-1 the congruences force
# the r-primary part of F to divide ell-1 for EVERY prime ell|n.
# If F>sqrt(n), such a proper prime divisor <=sqrt(n) cannot exist.
def pock(n,factors,w,cert):
    F=prod(r**e for r,e in factors)
    assert F*F>n and (n-1)%F==0 and pow(w,n-1,n)==1
    for r,e in factors:
        assert (r in cert or (r<3000 and prime(r))) and gcd(pow(w,(n-1)//r,n)-1,n)==1
    cert.add(n)
p=9223372036978232701;q=(1<<80)*p+1
cert=set()
for n,fs,a in [
    (28919629177,[(401,1),(1481,1)],2),
    (4858497701737,[(28919629177,1)],2),
    (19433990806949,[(4858497701737,1)],2),
    (38867981613899,[(19433990806949,1)],2),
    (p,[(38867981613899,1)],2),
    (q,[(2,80)],3)]:
    pock(n,fs,a,cert)
assert edges({2**i for i in range((p*q).bit_length())},[p,q])==[(p,q,2**80)]
print("power-of-two label exponent / anchor bits / other-prime bits / Pocklington steps",80,p.bit_length(),q.bit_length(),len(cert))
