"""Exact finite lemmas for the partner-regular vertex obstruction. Python >= 3.10."""
from itertools import combinations, product

if not __debug__:
    raise RuntimeError('Run without Python optimization so all exact assertions are checked.')

def par(a,b): return (a&b).bit_count() & 1
def echelon(rows):
    basis={}
    for a in rows:
        while a:
            j=a.bit_length()-1
            if j not in basis: basis[j]=a; break
            a ^= basis[j]
    return basis
def nullspace(basis,n):
    out=[]
    for k in range(n):
        if k in basis: continue
        s=1<<k
        for j,r in sorted(basis.items()):
            if par(r,s): s |= 1<<j
        out.append(s)
    return out
def double(v): return (0,2,3,1)[v]  # omega over F4
def plane(f): return tuple(f(u) for u in (1,2))
P=[plane(lambda u,i=i:u<<(2*i)) for i in range(3)]
P += [plane(lambda u:u*21), plane(lambda u:u+(double(u)<<2)+(double(double(u))<<4)),
      plane(lambda u:u+(double(double(u))<<2)+(double(u)<<4))]
edges=[(a,6) for a in range(6)]+list(combinations(range(6),2))
off=edges[6:]; Y=[]
for a,b in off:
    ys=[v for v in range(1,64) if all(not par(v,u) for u in (*P[a],*P[b]))]
    assert len(ys)==3
    Y.append(ys[:2]) # any two distinct nonzeros are a basis
def form(a,i,b,j):
    # omega((x_ai,y_ai),(x_bj,y_bj)) as a linear form in the 180 x bits
    return (Y[a][i] << (6*(2*b+j))) ^ (Y[b][j] << (6*(2*a+i)))
def intersect(e,f): return bool(set(e)&set(f))
axes=tuple(product((0,1), repeat=2))
vanish=[form(a,0,a,1) for a in range(15)]
for a,b in combinations(range(15),2):
    if intersect(off[a],off[b]): vanish += [form(a,i,b,j) for i,j in axes]
V=echelon(vanish); T=nullspace(V,180)
assert len(V)==152 and len(T)==28
assert all(not par(t,r) for t in T for r in vanish)
def restrict(r): return sum(par(t,r)<<k for k,t in enumerate(T))
forms={(a+6,b+6):[restrict(form(a,i,b,j)) for i,j in axes]
       for a,b in combinations(range(15),2) if not intersect(off[a],off[b])}
basis=echelon(r for block in forms.values() for r in block)
piv=sorted(basis,reverse=True)
def compress(r):
    s=0
    for k,j in enumerate(piv):
        if (r>>j)&1: r ^= basis[j]; s ^= 1<<k
    assert not r; return s
blocks={ab:list(map(compress,rs)) for ab,rs in forms.items()}
assert len(blocks)==45 and len(piv)==7
def table(rs,assignment):return tuple(par(r,assignment) for r in rs)
def det(A):a,b,c,d=A; return a*d ^ b*c
feasible=[x for x in range(1<<len(piv)) if all(det(table(rs,x))==1 for rs in blocks.values())]
assert feasible==[47]
def nonzeros(xs): return (*xs,xs[0]^xs[1])
def pair_matrix(a,b):
    if a>=6:return table(blocks[a,b],feasible[0])
    return tuple(par(P[a][i],Y[b-6][j]) for i,j in axes)
links={}
for a,b in combinations(range(21),2):
    if intersect(edges[a],edges[b]): continue
    M=pair_matrix(a,b); assert det(M)==1
    rows=[M[0]+2*M[1],M[2]+2*M[3]]
    # three nonzero column labels 1,2,3; matched label uniquely pairs to zero
    p=tuple(next(j for j in range(1,4) if not par(r,j))-1 for r in nonzeros(rows))
    assert tuple(sorted(p))==(0,1,2)
    links[a,b]=p;links[b,a]=tuple(p.index(i) for i in range(3))
tri=[(a,b,c) for a,b,c in combinations(range(21),3)
     if (a,b) in links and (a,c) in links and (b,c) in links]
flat=sum(all(links[c,a][links[b,c][links[a,b][j]]]==j for j in range(3)) for a,b,c in tri)
assert len(tri)==flat==105
print('180 lift bits: zero-pairing rank 152, nullity 28; disjoint Gram quotient rank 7')
print('All 128 Gram signatures tested: exactly 1 is locally invertible; 105/105 triangle holonomies are identity')
# An independent tiny verification of the Petersen graph argument.
duads=list(map(frozenset,combinations(range(5),2)))
def perfect(left):
    if not left: yield frozenset();return
    a=min(left)
    for b in sorted(left-{a}):
        if duads[a]&duads[b]: continue
        for rest in perfect(left-{a,b}): yield rest|{(a,b)}
pm=list(perfect(set(range(10))))
assert len(pm)==6 and all(a&b for a,b in combinations(pm,2))
print('Petersen graph: 6 perfect matchings; all 15 distinct pairs intersect. PASS')
