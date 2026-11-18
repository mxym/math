"""Check composition inequalities against all small connected graphs without using their recurrences."""
from itertools import combinations
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


from functools import lru_cache
@lru_cache(None)
def stats(G):
    g,r,h=cuts(G);C=list(G);C[0]|=2;C[1]|=1
    return len(g),len(h),max(len(g),len(cuts(C)[0]))
def combine(A,B,ser):
    a,b=len(A)-2,len(B)-2
    n=2+a+b+ser;w=n-1
    ea=lambda i: 0 if i==0 else w if i==1 and ser else i
    eb=lambda i: w if i==0 and ser else i if i<2 else a+i
    edges=set()
    for G,f in ((A,ea),(B,eb)):
        for i in range(len(G)):
            for j in range(i):
                if G[i]>>j&1:edges.add((f(i),f(j)))
    return tuple(adj(n,edges))
atoms=[]
for n in (2,3,4):
    E=list(combinations(range(n),2))
    for x in range(1<<len(E)):
        G=tuple(adj(n,[e for j,e in enumerate(E) if x>>j&1]))
        if len(comps(G,0))==1:atoms.append(G)
for A in atoms:
    ca,ha,da=stats(A)
    for B in atoms:
        cb,hb,db=stats(B)
        cp,hp,dp=stats(combine(A,B,False)); cs,hs,ds=stats(combine(A,B,True))
        need(hp==ha*hb and hs<=ha+hb+1, 'rooted product or series sum')
        need(dp<=da+db+ha*hb+4 and cs<=ca+cb+1 and ds<=da+db+ha*hb+ha+hb+9,'global/capped recurrences')
print('PASS rooted and global/capped series and parallel bounds for',len(atoms)**2,'ordered pairs of marked connected graphs through order four')
