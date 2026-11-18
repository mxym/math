"""Self-contained alternate check of order-eight coefficient comparisons; Python 3.10+.
No candidate script is imported. All checks below stay on under python -O.
"""
from fractions import Fraction as Q
from collections import defaultdict, Counter
from functools import cache
from itertools import combinations

def need(b,reason):
    if not b: raise ValueError(reason)
def verts(s):
    while s:
        b=s&-s; yield b.bit_length()-1; s ^= b
def eset(G):
    return tuple((i,j) for i,S in enumerate(G) for j in verts(S) if i<j)
def edge(G,i,j):
    need(i!=j and not G[i]>>j&1,"loop/duplicate edge")
    G=list(G);G[i]|=1<<j;G[j]|=1<<i
    return tuple(G)
def reach(G,start,mask):
    seen=0; to=1<<start
    while to:
        u=to&-to;to^=u;seen|=u
        to |= G[u.bit_length()-1]&mask&~seen
    return seen
def biconnected(G):
    n=len(G)
    return n>=3 and all(reach(G,int(v==0),(1<<n)-1-(1<<v)).bit_count()==n-1 for v in range(n))

@cache
def embs(G,H):
    # At each node branch on a domain vertex with smallest remaining candidate set.
    n=len(G);h=len(H)
    init=[sum(1<<j for j in range(h) if H[j].bit_count()>=x.bit_count()) for x in G]
    def search(left,sets):
        if not left:return 1
        u=min(verts(left),key=lambda i:(sets[i].bit_count(),-G[i].bit_count()))
        L=left^(1<<u);count=0
        for a in verts(sets[u]):
            S=sets.copy()
            for v in verts(L):
                S[v]&=~(1<<a)
                if G[u]>>v&1:S[v]&=H[a]
            count+=search(L,S)
        return count
    return search((1<<n)-1,init)
def sig(G):
    # Iso-invariant prefilter only; every collision is decided by exact mappings.
    D=[x.bit_count() for x in G]
    return tuple(sorted((d,tuple(sorted(D[j] for j in verts(G[i])))) for i,d in enumerate(D)))
def unique(iterable):
    buckets=defaultdict(list)
    for G in iterable:
        b=buckets[sig(G)]
        if not any(embs(G,H) for H in b):b.append(G)
    return [G for b in buckets.values() for G in b]
def build():
    # Every connected graph contains some spanning tree; add all remaining edges
    # without forbidding triangles/squares, then filter the resulting list only.
    trees={1:[(0,)]};blocks=[];counts=[]
    for n in range(2,10):
        trees[n]=unique(edge(T+(0,),u,n-1) for T in trees[n-1] for u in range(n-1) if T[u].bit_count()<3)
        layer=trees[n];count=0
        while layer:
            count+=len(layer);blocks.extend(G for G in layer if biconnected(G))
            layer=unique(edge(G,i,j) for G in layer for i,j in combinations(range(n),2)
                       if G[i].bit_count()<3 and G[j].bit_count()<3 and not (G[i]>>j&1))
        counts.append(count)
    return trees,blocks,counts
K=8; BASE=1<<26
@cache
def logscale(code):
    # Low coefficients of the signed-base polynomial, and k*[z^k]log P.
    p=[]
    for _ in range(K+1):
        a=code%BASE
        if 2*a>BASE:a-=BASE
        need(abs(a)<=8192,"overflow of signed encoding")
        p.append(a);code=(code-a)//BASE
    need(code==0 and p[0]==1,"bad polynomial")
    L=[0]
    for k in range(1,K+1):L.append(k*p[k]-sum(L[j]*p[k-j] for j in range(1,k)))
    return tuple(L)
@cache
def direct_weights(G):
    # Direct Mobius sum of logs over all edge subsets, without using any
    # cross-support matching or subtracting proper block counts.
    E=eset(G);m=len(E);n=len(G);L=1<<m;pack=[];sign=[]
    for mask in range(L):
        classes=[1<<j for j in range(n)];r=0
        for i in verts(mask):
            u,v=E[i];S=classes[u];T=classes[v]
            if S!=T:
                Z=S|T;r+=1
                for j in verts(Z):classes[j]=Z
        sign.append(-1 if mask.bit_count()%2 else 1)
        pack.append(sign[-1]*BASE**r)
    # Subset zeta transform: normalized polynomial of every subgraph, evaluated
    # at BASE. Each coefficient has absolute value <=2^m <=8192, so no ambiguity.
    for j in range(m):
        stride=1<<j
        for a in range(0,L,2*stride):
            for b in range(a,a+stride):pack[b+stride]+=pack[b]
    multiplicities=Counter()
    for c,s in zip(pack,sign):multiplicities[c]+=s*sign[-1]
    W=[sum(d*logscale(c)[k] for c,d in multiplicities.items() if d) for k in range(K+1)]
    need(W[:n]==[0]*(n-1)+[(n-1)*(-1)**m],"vanishing/leading sign")
    return [Q(x,max(k,1)) for k,x in enumerate(W)]
def cy(n):return tuple((1<<((i-1)%n))|(1<<((i+1)%n)) for i in range(n))
def named(which):
    if which=='P':
        # Edges of K5 with disjoint ends adjacent
        labels=list(combinations(range(5),2))
        return tuple(sum(1<<j for j,y in enumerate(labels) if set(x).isdisjoint(y)) for x in labels)
    # Canonical Hamiltonian model for Heawood. Confirm exact Moore gap counts below.
    H=cy(14)
    for v in range(0,14,2):H=edge(H,v,(v+5)%14)
    return H
def leading_lower(row,q):
    d=next(i for i,c in enumerate(row) if c!=0)
    return sum(Q(min(x,0),q**(i-d)) for i,x in enumerate(row[d+1:],d+1))+row[d]
expected={
  'P':[list(map(Q,line.split())) for line in ['0 0 0 0 1/5 -1 -104/7 -778/7 -3509/6',
       '0 0 0 1 1 -94/9 -727/6 -1960/3 -7895/2']],
  'H':[list(map(Q,line.split())) for line in ['0 0 0 0 0 1/6 0 -25/2 -255/2',
       '0 0 1 2 7/2 6 -113/3 -702 -20481/4','0 0 0 0 1 4 0 -40 -1847/6']]}
def test(which,trees,blocks):
    odd=which=='P';g=5 if odd else 6;M=named(which);s=(-1)**g
    need(all(S.bit_count()==3 for S in M),"host degrees")
    need(all(not embs(cy(l),M) for l in range(3,g)),"host girth bound")
    need(embs(cy(g),M)==(2*g)*(12 if odd else 28),"host's number of shortest cycles")
    X=(4,) if odd else (3,5);bad=3 if odd else 4
    kept=[G for G in blocks if embs(cy(bad),G)==0]
    need(len(kept)==(87 if odd else 51),"support count")
    U=[Q(0)]*(K+1);V={l:[Q(0)]*(K+1) for l in X}
    for G in kept:
        n=len(G);m=len(eset(G));aut=embs(G,G);w=direct_weights(G)
        l=next((l for l in X if embs(cy(l),G)),0)
        if l:
            if n==m==l:
                for k in range(K+1):V[l][k]-=s*w[k]
            else:
                cap=Q(2*l*2**(n-l),aut)
                for k in range(K+1):V[l][k]-=max(0,s*w[k])*cap
        elif n==m==g:
            need(s*w[g-1]==1 and all(s*t>=0 for t in w),"shortest cycle sign")
            U[g-1]+=Q(1,g)
            if odd:V[4][4]-=2
        else:
            # Already generated all possible abstract spanning trees; filter by
            # exact embeddings into G. No enumeration through edge subsets or CDS.
            t=min(sum(S.bit_count()>1 for S in T) for T in trees[n] if embs(T,G))
            cap=Q(3*2**t,aut);a=Q(embs(G,M),len(M)*aut)
            need(a<=cap,"spanning-tree cap")
            for k in range(K+1):U[k]+=s*w[k]*a-max(0,s*w[k])*cap
    rows=[U,*V.values()];need(rows==expected[which],"row values")
    q=37 if odd else 88
    # At 1/q the normalized geometric tail equals (2*7^9)/(9*(q-7)*q^(9-g)).
    tail=Q(2*7**9,9*(q-7)*q**(9-g));slack=leading_lower(U,q)-tail
    need(slack==(Q(85823,708432858) if odd else Q(2393573,993586176)) and slack>0,"endpoint slack")
    v=[leading_lower(row,q) for row in V.values()];need(min(v)>0,"short ledger endpoint")
    print(which,"supports",len(kept),"q",q,"slack",slack,"short ledgers",*[str(x) for x in v],flush=True)
def chrom_stirling(G,q):
    # Enumerate partitions into independent sets by choosing the color class
    # of the least remaining vertex, then assign falling-factorial label counts.
    n=len(G)
    @cache
    def stable(S):
        if not S:return True
        bit=S&-S;u=bit.bit_length()-1
        return (S&G[u])==0 and stable(S^bit)
    @cache
    def part(S):
        if not S:return (1,)
        root=S&-S;rest=S^root;T=rest;A=[0]*(1+S.bit_count())
        while True:
            if stable(root|T):
                for k,x in enumerate(part(rest^T)):A[k+1]+=x
            if not T:break
            T=(T-1)&rest
        return tuple(A)
    V=part((1<<n)-1);fall=1;z=0
    for k,v in enumerate(V):
        z+=v*fall;fall*=q-k
    return z
def raw_tests():
    P=named('P');H=named('H')
    # Truncating all four vertices of K4 replaces each by a triangle.
    D=[(a,b) for a in range(4) for b in range(4) if a!=b]
    T=tuple(sum(1<<j for j,(c,d) in enumerate(D) if (a==c and b!=d) or (a,b)==(d,c)) for a,b in D)
    K33=tuple([56]*3+[7]*3)
    need(all(x.bit_count()==3 for x in T) and embs(cy(3),T)==4*6 and not embs(cy(4),T),"triangle-allowed cubic fixture")
    need(all(x.bit_count()==3 for x in K33) and not embs(cy(3),K33) and embs(cy(4),K33)>0,"square-allowed cubic fixture")
    for M,G,q,sgn in [(P,K33,37,-1),(P,H,37,-1),(H,P,88,1),(H,T,88,1)]:
        a,b=chrom_stirling(M,q),chrom_stirling(G,q)
        need(a>0 and b>0 and sgn*(a**len(G)-b**len(M))>0,"raw normalized integer comparison")
    print("4 raw endpoint comparisons of integer chromatic counts, including triangle-rich truncated K4: PASS")
if __name__=='__main__':
    trees,blocks,counts=build()
    print("unfiltered simple connected subcubic graphs of each order 2..9:",*counts,flush=True)
    print("unfiltered biconnected supports:",len(blocks),flush=True)
    for which in 'PH':test(which,trees,blocks)
    raw_tests()
    print("PASS")
