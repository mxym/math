"""Exact finite checks (standard library only; checks remain active under -O)."""
from collections import Counter
from itertools import permutations, combinations
from math import comb

def eq(a,b):
    if a!=b: raise ValueError((a,b))

def gaps(extensions,marks):
    x,y,z=marks
    return Counter((p.index(y)-p.index(x),p.index(z)-p.index(y)) for p in extensions)

vs=('o','A1','A2','B1','B2')
constraints=(('o','A1'),('o','B1'),('A1','A2'),('B1','B2'),('A1','B2'))
ext=[p for p in permutations(vs) if all(p.index(x)<p.index(y) for x,y in constraints)]
F=gaps(ext,('o','A1','B2'))
D=gaps([p[::-1] for p in ext],('B2','A1','o'))
S=gaps(ext,('A1','o','B2'))
R=Counter((p.index('A1'),p.index('B2')) for p in ext) # ranks one-based after deleting o
eq(len(ext),5)
eq(F,Counter({(1,3):2,(2,1):1,(1,2):1,(2,2):1}))
eq(D,Counter({(j,i):v for (i,j),v in F.items()}))
eq((D[3,1]*D[1,2],D[2,1]*D[2,2]),(2,1))
eq((S[-2,3]*S[-1,4],S[-2,4]*S[-1,3]),(2,1))
eq((R[1,3],R[1,4],R[2,3],R[2,4]),(1,2,1,1))
for p in ext: print(''.join(x[0] for x in p[1:]),(p.index('A1'),p.index('B2')-p.index('A1')))
print('signed diagonal 2 vs 1; absolute-rank diagonal 1 vs 2; dual verified.')
s=0
for k in range(1,8):
    for l in range(1,8):
        a,b=l+1,k+1
        U=range(1,1+a+b)
        C=Counter()
        for AA in combinations(U,a):
            BB=set(U).difference(AA)
            i,j=AA[0],max(BB)
            if i<j:C[i,j-i]+=1
        eq(sum(C.values()),comb(a+b,a)-1)
        eq((C[k,l+2],C[k+1,l],C[k,l+1],C[k+1,l+1]),(l+1,1,l,1))
        s+=sum(C.values())
print(f'49 parameter pairs, {s} valid labelled-chain shuffles, all four counts verified.')
