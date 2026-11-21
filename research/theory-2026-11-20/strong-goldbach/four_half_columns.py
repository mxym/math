"""Column-first capped incidence, rational nullspaces by primitive integer Gauss elimination.
Run with python3 -O. No third-party modules and no assert-dependent checks.
"""
from itertools import product
from math import gcd, prod
from functools import reduce
from hashlib import sha256

def prim(r):
    g=reduce(gcd,r,0)
    return [v//g for v in r] if g else r

def kernel(A,n=6):
    A=[list(r) for r in A]
    piv=[]
    for x in range(n):
        t=len(piv)
        j=next((s for s in range(t,len(A)) if A[s][x]),None)
        if j is None: continue
        A[t],A[j]=A[j],A[t]
        A[t]=prim(A[t])
        for s in range(len(A)):
            if s!=t and A[s][x]:
                a,b=A[t][x],A[s][x]
                A[s]=prim([a*y-b*z for y,z in zip(A[s],A[t])])
        piv.append(x)
    den=prod(abs(A[j][x]) for j,x in enumerate(piv))
    basis=[]
    for z in range(n):
        if z in piv: continue
        v=[0]*n
        v[z]=den
        for j,x in enumerate(piv): v[x]=-A[j][z]*den//A[j][x]
        basis.append(prim(v))
    return basis

levels=[[],[],[],[]]
coeffs={}
def test(cols):
    rows=list(zip(*cols))
    if sum(rows[0])<1 or sum(rows[1])!=2 or len(set(rows))!=6: return
    tag=''.join(str(x) for r in rows for x in r)
    levels[0].append(tag)
    eig=kernel([tuple(x-(r==c+2) for r,x in enumerate(col)) for c,col in enumerate(cols)])
    if len(eig)!=2: return
    u,v=eig
    cross=lambda i,j:u[i]*v[j]-u[j]*v[i]
    if not cross(0,1): return
    for i in range(6):
        line=[cross(i,j) for j in range(6)]
        if sum(x>0 for x in line)<2 or sum(x<0 for x in line)<2: return
    left=kernel(cols+[(1,)*6])
    if len(left)!=1 or not left[0][2]: return
    l=left[0]
    levels[1].append(tag)
    if any(2*(row[0]+row[1])+sum(row[2:]) for row in eig):return
    levels[2].append(tag)
    vals=[l[i] for i in (2,3,4,5,1,0)]
    prefix=[sum(vals[:k]) for k in range(1,6)]
    if min(prefix)>=0 or max(prefix)<=0: return
    levels[3].append(tag)
    coeffs[tag]=l

choices=[]
for target in range(2,6):
    M=[]
    for col in product(range(3),repeat=6):
        if col[target]:continue
        if sum(bool(col[j]) for j in range(6) if j<2 or j>target)>1:continue
        M.append(col)
    choices.append(M)

def generate(cols,cap):
    j=len(cols)
    if j==4:
        test(cols);return
    for col in choices[j]:
        if any(x>y for x,y in zip(col,cap)):continue
        generate(cols+[col],tuple(y-x for x,y in zip(col,cap)))

generate([], (2,)*6)
expected=[
(16609,'4ada98bb881f0a69aba8954f59d892f8e3d12d226425ebd85b6f63c231c2dc03'),
(902,'437c68cb327280661851b6b944b2d38b672becb0bc7ca1eea2834b59cfd37fed'),
(20,'496198b394f416d1c061160ec34a91515f9c416f92d4e5c2f4935eb42dafa879'),
(4,'ac3b9c72d5945abadc8a0088a110210f4c231edc8e631d8129aed9ad7de0ca1c')]
for title,ids,want in zip(('raw','rank-gale','equal','terminal'),levels,expected):
    got=(len(ids),sha256(('\n'.join(sorted(ids))+'\n').encode()).hexdigest())
    print(title,*got)
    if got!=want or len(ids)!=len(set(ids)):raise SystemExit('ledger mismatch')
for code,l in sorted(coeffs.items()): print(code,*l)
