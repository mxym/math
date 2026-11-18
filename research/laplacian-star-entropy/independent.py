"""Independent finite regression, Python standard library. Exact integer arithmetic, no assert."""
from itertools import combinations
from math import prod,lcm
def ck(ok,s):
    if not ok:raise ArithmeticError(s)
def lap(n,edges):
    L=[[0]*n for _ in range(n)]
    for i,j in edges:
        L[i][i]+=1;L[j][j]+=1;L[i][j]-=1;L[j][i]-=1
    return L
def mv(m,v):
    return tuple(sum(x*y for x,y in zip(r,v)) for r in m)
def times(A,B):
    t=list(zip(*B))
    return [[sum(a*b for a,b in zip(r,c)) for c in t] for r in A]
def trace(A):return sum(r[i] for i,r in enumerate(A))
def char(L):
    # Faddeev--LeVerrier: calculate det(tI-L) from the full adjacency Laplacian.
    n=len(L);R=[r[:] for r in L];c=[1]
    for i in range(1,n+1):
        z,rem=divmod(-trace(R),i);ck(rem==0,'coeff');
        c.append(z)
        if i==n:break
        for j in range(n):R[j][j]+=z
        R=times(L,R)
    return tuple((-1)**i*x for i,x in enumerate(c))
def encode(i,j):return(min(i,j),max(i,j))
def conn(n,E):
    s={0}
    for i in range(n):
        for a,b in E:
            if a in s or b in s:s|={a,b}
    return len(s)==n
def kelmans(n,E,u,v):
    A={i for i in range(n) if i not in (u,v) and encode(i,u) in E}
    B={i for i in range(n) if i not in (u,v) and encode(i,v) in E}
    new=E-{encode(v,w) for w in B-A}|{encode(u,w) for w in B-A}
    return new
def threshold(n,E):
    V=set(range(n))
    while len(V)>1:
        for u in V:
            d=sum(encode(u,w) in E for w in V-{u})
            if d in (0,len(V)-1):
                V.remove(u);break
        else:return False
    return True
raw=comps=trees=steps=0
for n in range(2,6):
    U=list(combinations(range(n),2));G={}
    for mask in range(1<<len(U)):
        e=frozenset(w for i,w in enumerate(U) if mask>>i&1)
        G[e]=char(lap(n,e))
    for E,poly in G.items():
        raw+=1
        if not conn(n,E):continue
        comps+=1;s=frozenset((0,i) for i in range(1,n));p=frozenset((i,i+1) for i in range(n-1))
        if len(E)==n-1:
            trees+=1
            ck(all(x<=y<=z for x,y,z in zip(G[s],poly,G[p])),'tree order')
            degrees=[sum(i in edge for edge in E) for i in range(n)]
            ck((poly==G[s])==(max(degrees)==n-1),'tree star equality')
            ck((poly==G[p])==(max(degrees)<=2),'tree path equality')
        for u in range(n):
            for v in range(n):
                if u==v:continue
                W=kelmans(n,E,u,v)
                if W==E:continue
                steps+=1;ck(all(x>=y for x,y in zip(poly,G[W])),'Kelmans')
                if encode(u,v) in E:ck(conn(n,W),'connectivity')
        W=E;u=0
        while sum(u in e for e in W)<n-1:
            for v in range(1,n):
                if encode(u,v) in W:
                    new=kelmans(n,W,u,v)
                    if new!=W:break
            else:raise ArithmeticError('universal')
            W=new
        while True:
            for a,b in combinations(range(1,n),2):
                new=kelmans(n,W,a,b);reverse=kelmans(n,W,b,a)
                if W!=new and W!=reverse:break
            else:break
            W=new
        ck(conn(n,W) and threshold(n,W) and len(W)==len(E),'endpoint')
print(f'PASS: {raw} labeled graphs on n=2..5; {comps} connected; {trees} trees; {steps} nonidentity directed Kelmans checks, using exact full-matrix coefficients.')
words=0;strict=0
for n in range(2,13):
    N=n-1
    for w in range(1<<max(n-2,0)):
        births=[j for j in range(1,N) if w>>(j-1)&1]
        # Build simple graph from its edges and independently an *ordered-pair counting* model.
        E=[(a,b) for b in births+[N] for a in range(b)]
        mu=[0]*N;joint={}
        for j in births:
            for i in range(1,j+1):
                for l,r in [(i,j),(j,i)]:
                    mu[l]+=1
                    joint[l,r]=joint.get((l,r),0)+1
        L=lap(n,E); M=2*len(E)
        vals=[0]+[1+mu[j] for j in range(1,N)]+[n]
        ck(sum(vals)==M and mv(L,[1]*n)==(0,)*n,'trace or zero')
        for j in range(1,n):
            v=[1]*j+[-j]+[0]*(n-1-j)
            ck(mv(L,v)==tuple(vals[j]*a for a in v),'auxiliary degrees not exact eigenvalues')
        words+=1
        if not births:continue
        strict+=1
        s=sum(births)
        ck(sum(joint.values())==2*s and all(v in (1,2) for v in joint.values()),'endpoint multiplicity')
        ck(sum(v==2 for v in joint.values())==len(births),'loop multiplicity')
        ck(prod(a**a for a in mu)<=(2*s)**s*2**len(births),'endpoint entropy')
        # Compare entropy denominators via least common multiple. zeros do not contribute.
        M0=2*N;d=lcm(M,M0)
        ck(M**d*(n**n)**(d//M0)>M0**d*prod(a**a for a in vals)**(d//M),'Shannon comparison')
        for z in (2,3,7):
            ck(sum(a**z for a in vals)*M0**z<(n**z+n-2)*M**z,('Renyi',z))
print(f'PASS: {words} threshold words through graph order 12; {strict} nonstar words: exact matrix eigenvector, endpoint, Shannon, and three integer-order Renyi checks.')
p=[]
for k in range(1,8):
    s=k*(k+1)//2;num=6*s*32**(3*s);den=2**(3*k)*27**(3*s)
    ck(num>den,'small k constant');p.append(num//den)
ck(32**9>4*27**9 and 2**16>3**10, 'large k and sparse constants')
print('PASS: all nine strict rational bounds; small-k ratio floors',p)
