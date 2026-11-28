"""Graph checks on two explicit, already factored finite fixtures."""
from fractions import Fraction as Q
from math import isqrt, prod

P=(5,11,23,47)
assert all(p>1 and all(p%d for d in range(2,isqrt(p)+1)) for p in P)
eqs=(lambda x,y:y*y-(2*x+1)**2,lambda x,y:y-3*x-8)
A={p:{q for q in P if p!=q and any(f(p,q)==0 or f(q,p)==0 for f in eqs)} for p in P}
assert eqs[0](5,11)==eqs[0](11,23)==eqs[1](5,23)==eqs[0](23,47)==0
assert {11,23}<=A[5] and 47 in A[23]
assert 7 not in P
seen={5}
while seen != seen.union(*(A[p] for p in seen)):
    seen=seen.union(*(A[p] for p in seen))
assert seen==set(P)

P=(2,5,7,11,23,47)
funcs=(lambda x:x*x+x+1,lambda x:Q(x-1,3),lambda x:2*x+1,lambda x:Q(x-1,2))
assert all(p>1 and all(p%d for d in range(2,isqrt(p)+1)) for p in P)
assert prod(P)==832370 and prod(P).bit_length()==20
A={p:{f(p) for f in funcs if f(p) in P and f(p)!=p} for p in P}
assert 7 in A[2] and 2 in A[7]
assert all(funcs[1](funcs[0](x))-x==Q(x*(x-2),3) for x in range(-5,25))
M=0
for src in P:
    steps={src:0}
    work=[src]
    for p in work:
        for q in sorted(A[p]):
            if q not in steps:
                work.append(q)
                steps[q]=1+steps[p]
    assert set(steps)==set(P)
    M=max(M,max(steps.values()))
assert M==5 and (20-1).bit_length()==5
print("PASS two fixed prime graphs: multivalued labelled 3-edge circuit; directed nonlinear 2-edge circuit and diameter 5.")
