"""Closed enumeration below a fixed small bound. No input or external dependency."""
from itertools import combinations
from math import isqrt
X=8192
P=[i for i in range(2,X+1) if all(i%j for j in range(2,isqrt(i)+1))]
# Enumerate positive multiples to build support; use the unit-slope gap criterion.
support=[[] for _ in range(X+1)]
for p in P:
    for n in range(p,X+1,p): support[n].append(p)
A=[0,0,0]
for n,S in enumerate(support):
    if len(S)<2: continue
    gap=max(y-x for x,y in zip(S,S[1:]))
    for c in range(3): A[c] += gap <= n.bit_length()**c
# Independent enumeration of increasing prime-power products and graph reachability.
B=[0,0,0]
def traverse(start,n,S):
    if len(S)>=2:
        for c in range(3):
            width=n.bit_length()**c
            reached={S[0]}
            while True:
                grow=reached|{q for q in S if any(abs(q-p)<=width for p in reached)}
                if len(grow)==len(reached): break
                reached=grow
            B[c] += len(reached)==len(S)
    for j in range(start,len(P)):
        p=P[j]
        q=n*p
        if q>X: break
        while q<=X:
            traverse(j+1,q,S+(p,))
            q*=p
traverse(0,1,())
assert A==B
assert A[0]==sum(2**i*3**j<=X for i in range(1,X.bit_length()+1)
                for j in range(1,X.bit_length()+1))
# Fixed scaffold: every chosen subset remains connected in prime indices.
w=5
verts=list(range(23,53)); anchors=verts[::w]
rest=[x for x in verts if x not in anchors]
configs=0
for subset in combinations(rest,3):
    I=sorted(anchors+list(subset))
    assert max(v-u for u,v in zip(I,I[1:]))<=2*w
    configs+=1
print("PASS: X",X,"unit-gap counts c=0,1,2",A,"scaffold subsets",configs)
