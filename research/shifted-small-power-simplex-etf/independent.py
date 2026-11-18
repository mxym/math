"""Independent finite diagnostics; no source-verifier import, no floating point."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from collections import Counter
def require(condition,label):
    if not condition:raise AssertionError(label)
def masks(n,r):
    return [sum(1<<i for i in A) for A in combinations(range(n),r)]
def inside(s):return comb(s,2)
graphs=tuples=0
for n in range(2,7):
    pairs=list(combinations(range(n),2))
    allbits=(1 << len(pairs))-1
    test=[]
    for ell in range(2,n+1):
        k,r=divmod(n,ell);M=(ell-r)*inside(k)+r*inside(k+1)
        # For a balanced complete multipartite graph the complement components
        # are cliques, with this list of component orders.
        clq=[sum(1<<j for j,(x,y) in enumerate(pairs) if C>>x&1 and C>>y&1) for C in masks(n,ell+1)]
        test.append((ell,M,clq,sorted([k]*(ell-r)+[k+1]*r)))
    for g in range(allbits+1):
        graphs+=1
        nedges=(allbits^g).bit_count()
        for l,M,clq,balance in test:
            if any((c&g)==c for c in clq):continue
            require(nedges>=M,'Turan integer gap')
            if nedges!=M:continue
            tuples+=1
            # Complement neighbor + self sets are exactly balanced disjoint blocks.
            h=[{i} for i in range(n)]
            for j,(x,y) in enumerate(pairs):
                if not g>>j&1:h[x].add(y);h[y].add(x)
            require(all(B==C or B.isdisjoint(C) for B in h for C in h),'equality complete multipartite')
            require(sorted(map(len,{frozenset(B) for B in h}))==balance,'balanced sizes')
print(f'PASS {graphs} labeled graphs (2..6 vertices), {tuples} equality graph/part-count instances.')
arith=0
for ell in range(2,27):
  for n in range(ell,6*ell+1):
    k,r=divmod(n,ell);M=ell*k*(k-1)//2+k*r;b=4*ell**2*(M+1)
    q=Q(1,8*ell**2*(M+1)**2);eta=Q(1,b*b)
    require((1-2*q*b)*(M+1)==M,'one surplus nonedge endpoint')
    require(ell**2*eta<1,'no (ell+1)-clique margin')
    require(b>2*M*ell*(ell-1) and 2*ell*(ell-1)*eta<1,'compensation and positive D')
    require(q<=Q(1,2),'cross power comparison')
    # Exact signed Gram contact for a balanced simplex, all diagonal weights.
    multiplicities=[k+1]*r+[k]*(ell-r)
    require(sum(inside(c) for c in multiplicities)==M,'model cost')
    arith+=1
print(f'PASS {arith} parameter choices, exact endpoint/strict margins and balanced model cost.')
etf=0
for d in range(2,16):
  for l in range(d,d*(d+1)//2+1):
    a2=Q(l-d,d*(l-1))
    for t2 in [Q(0),Q(1,7),a2,Q(1)]:
        s=(d*t2-1)/Q(d-1)
        require((1+(l-1)*s)/l==(t2-a2)/(1-a2),'projective affine identity')
    require((d*a2-1)/Q(d-1)==-Q(1,l-1),'ETF contact')
    etf+=1
print(f'PASS {etf} formal (d,l) projector identities; these checks do not assert ETF existence.')
