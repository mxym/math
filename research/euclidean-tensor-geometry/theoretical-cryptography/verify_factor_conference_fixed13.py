from fractions import Fraction as F
from collections import defaultdict,Counter
from math import lcm,gcd
from itertools import product
import json
import sys
if not __debug__:
    raise RuntimeError("Run in normal mode, without python -O")
def reduced(A,c=None):
    T=[list(map(F,x)) for x in A]; h=len(T); cols=[];i=0
    for j in range(c or len(T[0])):
        k=next((k for k in range(i,h) if T[k][j]),None)
        if k is None:continue
        T[i],T[k]=T[k],T[i];v=T[i][j];T[i]=[x/v for x in T[i]]
        for k in range(h):
            if k!=i and T[k][j]:
                v=T[k][j];T[k]=[a-v*b for a,b in zip(T[k],T[i])]
        cols.append(j);i+=1
        if i==h:break
    return T,cols
def integ(a):
    p=lcm(*(v.denominator for v in a))
    z=tuple(int(v*p) for v in a);g=gcd(*z)
    return tuple(x//g for x in z)
def solve(U0):
    n=len(U0)
    H=[[(45*int(i==j)-sum(U0[i][k]*U0[k][j] for k in range(n)))//2
        for j in range(n)] for i in range(n)]
    R,cols=reduced(H); assert len(cols)==14
    U=[]
    for j in set(range(n))-set(cols):
        rhs=[F(0)]*n;rhs[j]=F(1)
        for i,c in enumerate(cols):rhs[c]=-R[i][j]
        U.append(integ(rhs))
    A=[[H[i][j] for j in cols]+[int(k==t) for t in range(len(cols))]
       for k,i in enumerate(cols)]
    R2,c=reduced(A,len(cols));assert len(c)==len(cols)
    inv=[r[len(cols):] for r in R2];den=lcm(*(v.denominator for row in inv for v in row))
    inv=[[int(z*den) for z in row] for row in inv]
    dot=lambda a,b:sum(x*y for x,y in zip(a,b))
    group=defaultdict(list)
    for b in product((1,-1),repeat=n//2):
        group[tuple(dot(v[n//2:],b) for v in U)].append(b)
    xs=[]
    for a in product((1,-1),repeat=n//2-1):
        a=(1,)+a;key=tuple(-dot(v,a) for v in U)
        for b in group[key]:
            x=a+b; cut=[x[i] for i in cols]
            coeff=[dot(row,cut) for row in inv]
            if dot(coeff,cut)!=den:continue
            xx=[dot(x,U0[j]) for j in cols]
            if dot(coeff,xx):continue
            xs.append((x,cut,coeff,xx))
    nrow=len(xs); gra=[0]*nrow
    for i,(x,y,a,xx) in enumerate(xs):
      for j in range(i):
        x2,y2,b,z=xs[j]
        if dot(a,y2)==0 and abs(dot(b,xx))==den:
            gra[i]|=1<<j;gra[j]|=1<<i
    out=[];stats=[0]*15
    deg=Counter(r.bit_count() for r in gra)
    def enum(P,C):
        stats[len(C)]+=1
        if len(C)==14:
            xdata=[xs[i] for i in C]
            X=[a[0] for a in xdata]
            R=[[(-dot(a[3],b[2]))//den for b in xdata] for a in xdata]
            assert all(R[i][i]==0 and all(i==j or R[i][j] in (-1,1) for j in range(14)) for i in range(14))
            assert all(R[i][j]==R[j][i] for i in range(14) for j in range(14))
            out.append((X,R))
            return False
        while P.bit_count()+len(C)>=14:
            b=P&-P;i=b.bit_length()-1;P^=b
            if enum(P&gra[i],C+[i]):return True
        return False
    enum((1<<nrow)-1,[])
    return nrow,deg,stats,out
raw=json.load(sys.stdin)
DATA,ANTI,FGRAPH=raw["plus"],raw["anti"],raw["F"]
assert (len(DATA),len(ANTI),len(FGRAPH))==(61,35,16)
ALL=(1<<46)-1
def loadmask(X,R):
    adj=[0]*46
    def edge(i,j):
        adj[i]|=1<<j;adj[j]|=1<<i
    for i in range(14):
        for j in range(i):
            if R[i][j]==-1:edge(i,j)
        for j in range(16):
            if X[i][j]==-1:
                edge(i,14+2*j);edge(i,15+2*j)
    for i in range(8,16):edge(14+2*i,15+2*i)
    return adj
def moved(U,B):
    ad=[0]*46
    def edge(i,j):
        ad[i]|=1<<j;ad[j]|=1<<i
    for i in range(16):
      for j in range(i):
        u=14+2*i;v=14+2*j
        if (FGRAPH[i]>>j)&1:
            if U[i][j]==-2:
                for a in (u,u+1):
                  for b in (v,v+1):edge(a,b)
        else:
            if (B[i]>>j)&1:
                edge(u,v);edge(u+1,v+1)
            else:edge(u,v+1);edge(u+1,v)
    return ad
def subset(adj,left,k):
    if k==1:return bool(left)
    while left.bit_count()>=k:
        b=left&-left
        left^=b
        if subset(adj,left&adj[b.bit_length()-1],k-1):return True
    return False
def dephase(adj,i):
    N=adj[i];keep=ALL^(1<<i)
    return [(m^N^(ALL if (N>>j)&1 else 0))&keep&~(1<<j)
        for j,m in enumerate(adj)]
def is_good(adj,i):
    keep=ALL^(1<<i)
    ad=dephase(adj,i)
    if subset(ad,keep,5):return 1
    co=[keep^m^((1<<j)&keep) for j,m in enumerate(ad)]
    if subset(co,keep,5):return -1
    return 0
one_count=0;plus_count=0;red=0;blue=0;good=[];nrows=0;u_with_clique=0
for k,U in DATA:
    nrow,deg,stats,sols=solve(U)
    plus_count+=len(sols)
    nrows+=nrow
    u_with_clique+=bool(sols)
    M=[moved(U,b) for b in ANTI]
    loc=[0,0]
    for ii,(X,R) in enumerate(sols):
      v=loadmask(X,R)
      for jj,w in enumerate(M):
        A=[a|b for a,b in zip(v,w)]
        if one_count==0:
            for i,a in enumerate(A):
                assert all(((a^b)&~((1<<i)|(1<<j))).bit_count()==22
                    for j,b in enumerate(A) if i!=j)
        for t in range(14):
            ans=is_good(A,t)
            one_count+=1
            if ans==0:good.append([k,ii,jj,t])
            elif ans==1:loc[0]+=1
            else:loc[1]+=1
    red+=loc[0];blue+=loc[1]
    if len(sols):print("finished",k,len(sols),*loc)
print("ROWS / NONEMPTY U",nrows,u_with_clique)
print("TOTAL",plus_count,one_count,red,blue,len(good),good[:20])
assert (nrows,u_with_clique)==(1684,37)
assert (plus_count,one_count,red,blue,len(good))==(408,199920,199920,0,0)
