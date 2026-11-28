"""Finite exact word-ball checks, including independent exponent enumeration."""
from fractions import Fraction as F
from itertools import product

def balls(S,r):
    S={F(v) for v in S};moves=S|{1/v for v in S};b={F(1)}
    out=[b]
    for _ in range(r):
        b=b|{q*v for q in b for v in moves};out.append(b)
    return out

def reference(S,r):
    ans=set()
    for coeff in product(range(-r,r+1),repeat=len(S)):
        if sum(map(abs,coeff))>r:continue
        v=F(1)
        for c,s in zip(coeff,S):v*=s**c
        ans.add(v)
    return ans

def val(v,p):
    a,b=v.numerator,v.denominator;n=0
    while a%p==0:a//=p;n+=1
    while b%p==0:b//=p;n-=1
    return n

# In the last list six distinct valuation coordinates occur although rank is two.
u,v=F(15,14),F(77,65)
cases=[([],[]),([F(1)],[]),([F(3,2),F(9,4),F(27,8)],[3]),
       ([u,v,u*v,u*u],[2,11])]
allcounts=[]
for S,coords in cases:
    layers=balls(S,6);B=max([1]+[max(a.numerator.bit_length(),a.denominator.bit_length()) for a in S])
    cnt=[]
    for r,b in enumerate(layers):
        assert b==reference(S,r)
        proj={tuple(val(a,p) for p in coords) for a in b}
        assert len(proj)==len(b)<=((2*r*B+1)**len(coords))
        cnt.append(len(b))
    allcounts.append(cnt)
print("word ball sizes for radii 0..6",allcounts)
# More labels need not imply higher rank. Also check all inverses are retained.
assert F(14,15) in balls([u,v],1)[1] and F(65,77) in balls([u,v],1)[1]
print("rank-two example label support primes",sorted({2,3,5,7,11,13}))
