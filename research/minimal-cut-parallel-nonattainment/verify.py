"""Exact finite stress tests; not a proof that the asymptotic nonattainment holds."""
from itertools import combinations
from math import comb


def need(v,s):
    if not v: raise RuntimeError(s)


def adj(n,edges):
    A=[0]*n
    for i,j in edges:
        need(i!=j, 'loop')
        A[i]|=1<<j; A[j]|=1<<i
    return A


def comps(A,S):
    R=((1<<len(A))-1)^S
    out=[]
    while R:
        f=R&-R; c=0
        while f:
            c|=f
            bit=f&-f;f^=bit
            f|=A[bit.bit_length()-1]&R&~c
        out.append(c);R^=c
    return out


def cuts(A,s=0,t=1):
    N=len(A); glo=[];root=[];clean=[];prop=[False]*(1<<N)
    for S in range(1<<N):
        cc=comps(A,S);dis=len(cc)>=2
        # prop[S] means some subset (including S) disconnects the graph. This
        # deliberately tests full inclusion minimality rather than relying on
        # connectivity being monotone under arbitrary vertex deletion.
        sub=S; earlier=False
        while sub:
            bit=sub&-sub;sub-=bit
            if prop[S^bit]: earlier=True;break
        if dis and not earlier:glo.append(S)
        prop[S]=dis or earlier
        if S&(1<<s|1<<t) or not dis:continue
        Cs=next(v for v in cc if v>>s&1)
        if Cs>>t&1: continue
        Ct=next(v for v in cc if v>>t&1)
        if all(A[x]&Cs and A[x]&Ct for x in range(N) if S>>x&1):
            root.append(S)
            if len(cc)==2:clean.append(S)
    return glo,root,clean


def parallel(G,r):
    n=len(G);E=set()
    for a in range(r):
        f=lambda x: x if x<2 else x+a*(n-2)
        for i in range(n):
            for j in range(i):
                if G[i]>>j&1:E.add((f(i),f(j)))
    return adj(2+(n-2)*r,E)


def amplify(G,k):
    n=len(G);r=k//2;E={(0,2+i) for i in range(k)}
    subsets=list(combinations(range(k),r))
    for a,T in enumerate(subsets):
        f=lambda x: 2+k+a*(n-2)+x-2
        for i in range(2,n):
            if G[i]&1:E.update((2+j,f(i)) for j in T)
            if G[i]&2:E.add((1,f(i)))
            for j in range(2,i):
                if G[i]>>j&1:E.add((f(i),f(j)))
    return adj(2+k+len(subsets)*(n-2),E)


# All connected labeled graphs through order 5, all terminal choices by label
# symmetry. Compare parallel and 3-shore-to-2-shore statements.
ct=0
for n in (3,4,5):
    pairs=list(combinations(range(n),2))
    for mask in range(1<<len(pairs)):
        G=adj(n,[p for j,p in enumerate(pairs) if mask>>j&1])
        if len(comps(G,0))!=1:continue
        gg,rt,cl=cuts(G)
        P=parallel(G,2);glob,rr,cl2=cuts(P)
        need(len(cl2)==len(cl)**2,'parallel clean product')
        need([v for v in glob if v in rr]==cl2,'only clean global cuts separating roots')
        for S in gg:
            cc=comps(G,S)
            if len(cc)!=3:continue
            a,b,c=[(d&-d).bit_length()-1 for d in cc]
            X=G[:];X[b]|=1<<c;X[c]|=1<<b
            need(S in cuts(X,a,b)[2],'three full shores')
        ct+=1
print('PASS parallel and three-shore reductions,',ct,'connected labeled graphs with marked 0,1, through order 5')
# A clean vs dirty example (s,t,a,b,c,d,e) = 0,1,2,3,4,5,6.
X=adj(7,[(0,2),(2,5),(5,1),(0,6),(6,4),(4,1),(2,3),(3,4)])
gg,rt,cl=cuts(X);S=(1<<2)|(1<<4)
need(S in rt and S in gg and S not in cl,'three-shore global cut is not clean')
# C4 with a leaf attached to one of the two cut vertices.
P=adj(5,[(0,2),(2,1),(0,3),(3,1),(2,4)])
pg,pr,pc=cuts(P);ps=12
need(ps in pr and ps not in pg and ps not in pc,'rooted separator need not be global')
for G,k in [(adj(4,[(0,2),(2,3),(3,1)]),2),(adj(4,[(0,2),(2,3),(3,1)]),4),(X,2)]:
    M=comb(k,k//2);g=len(cuts(G)[2]);Y=amplify(G,k)
    glob,_,new=cuts(Y)
    need(len(new)>=g**M+M*g**(M-1),'amplification inequality')
    need(set(new)<=set(glob),'global minimality')
    print('PASS gate amplifier: internal order',len(Y)-2,'base count',g,'certified',g**M+M*g**(M-1),'actual clean count',len(new))
p,g=3,3
for k in range(2,99):
    M=comb(k,k//2)
    if (M+g)**p>g**(p+k):break
need((g**M+M*g**(M-1))**p>g**(p*M+k),'strict finite gain')
print('PASS strict gain from a path of 3 internal vertices: k=',k,'M=',M,'internal order=',p*M+k)
