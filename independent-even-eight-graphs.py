from itertools import combinations, permutations, product
from collections import Counter
from math import factorial

if not __debug__: raise RuntimeError('run without -O')

G0=((40,80,224,193,130,5,14,28),(168,112,224,65,130,7,14,21),(56,112,224,193,131,7,14,28))
E8=list(combinations(range(8),2))

def tri_free_growth(n, alpha):
    old=[()]
    for j in range(n):
        new=[]
        for G in old:
            for nb in range(1<<j):
                if nb.bit_count()>alpha:continue
                good=True
                for i in range(j):
                    if nb>>i&1 and ((G[i]&nb) or G[i].bit_count()==alpha):
                        good=False;break
                if not good:continue
                C=[x for x in range(j) if not nb>>x&1]
                if any(not any(G[u]>>v&1 for u,v in combinations(S,2))
                       for S in combinations(C,alpha)):continue
                new.append(tuple((G[i]|((nb>>i&1)<<j)) for i in range(j))+(nb,))
        old=new
    return old

def isos(A,B):
    r=tuple(a.bit_count() for a in A);s=tuple(b.bit_count() for b in B)
    out=0
    for p in permutations(range(len(A))):
        if any(r[i]!=s[p[i]] for i in range(len(A))):continue
        if all((A[i]>>j&1)==(B[p[i]]>>p[j]&1) for i,j in combinations(range(len(A)),2)):out+=1
    return out

label=tri_free_growth(8,3)
classes=Counter(tuple(sorted(x.bit_count() for x in G)) for G in label)
for g in G0:
    d=tuple(sorted(x.bit_count() for x in g))
    a=isos(g,g)
    assert a and classes[d]==factorial(8)//a
assert len(classes)==3
print('recreated full labelled Ramsey graphs',len(label),'per types',classes,flush=True)

P=list(permutations(range(4)))
E4=list(combinations(range(4),2))
IM=[[sum((v>>p[j]&1)<<j for j in range(4)) for v in range(16)] for p in P]
nontriv=[(S,T) for t in range(1,5) for S in combinations(range(4),4-t) for T in combinations(range(4),t)]
valid=0;Charts=set()
for pp in range(1<<6):
    oG=[0]*4
    for j,(x,y) in enumerate(E4):
        if pp>>j&1:oG[x]|=1<<y;oG[y]|=1<<x
    if any((oG[x]>>y&1) and (oG[x]&oG[y]) for x,y in E4):continue
    edges=[(x,y) for x,y in E4 if oG[x]>>y&1]
    st=[(sum(1<<i for i in S),T) for S,T in nontriv
        if all(not(oG[x]>>y&1) for x,y in combinations(T,2))]
    nc=0
    for M in product([z for z in range(16) if z.bit_count()>1],repeat=4):
        if any(M[x]&M[y] for x,y in edges):continue
        if any(all(not (S&M[x]) for x in T) for S,T in st):continue
        valid+=1
        c=min((sum((oG[p[x]]>>p[y]&1)<<k for k,(x,y) in enumerate(E4)),
               *[I[M[p[k]]] for k in range(4)]) for p in P for I in IM)
        Charts.add(c)
assert (valid,len(Charts))==(1836,8)
print('unique 4-set graphs, fixed labels for independent set',valid,'classes',len(Charts),flush=True)
