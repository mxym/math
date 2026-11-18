"""Direct unlabeled bipartite graph + matrix tests, no external dependencies or assert."""
from collections import Counter
from itertools import product
from math import comb, factorial

def require(p, msg):
    if not p: raise ValueError(msg)

def words(q,n):
    return list(product(range(q),repeat=n))

def sub(u,x):
    uat=0
    for c in x:
        if uat<len(u) and u[uat]==c: uat+=1
    return uat==len(u)

def incidence(q,n,mode,rates=None):
    top=words(q,n); bottom=words(q,n-1) if mode=='one' else [x for i in range(n+1) for x in words(q,i)]
    ix={w:i+len(top) for i,w in enumerate(bottom)}; adj=[{} for i in range(len(top)+len(bottom))]
    for i,w in enumerate(top):
        count=Counter()
        if mode=='one':
            for j in range(n): count[w[:j]+w[j+1:]]+=rates[j] if rates is not None else 1
        else:
            for mask in range(1<<n):
                v=tuple(c for j,c in enumerate(w) if mask>>j&1)
                weight=1
                if rates is not None:
                    for j,c in enumerate(w): weight*=(10-rates[c]) if mask>>j&1 else rates[c]
                count[v]+=weight
        for v,a in count.items():
            if rates is None: a=1
            require(a>0,'unexpected zero weight')
            adj[i][ix[v]]=a; adj[ix[v]][i]=a
    return adj,[0]*len(top)+[1]*len(bottom)

def automorphisms(adj,c):
    # Isomorphisms between two copies with specified initial part colors.
    # Each individualization branches on *every* candidate in the matching target cell.
    # At leaves check every edge/nonedge on the completed bijection.
    def search(a,b):
        while True:
            sig=lambda arr,i:(arr[i],tuple(sorted((arr[j],w) for j,w in adj[i].items())))
            sa=[sig(a,i) for i in range(len(a))]; sb=[sig(b,i) for i in range(len(b))]
            if Counter(sa)!=Counter(sb): return 0
            labels={s:i for i,s in enumerate(dict.fromkeys(sa))}
            aa=[labels[s] for s in sa]; bb=[labels[s] for s in sb]
            stable=len(set(a))==len(set(aa))
            a,b=aa,bb
            if stable: break
        freq=Counter(a)
        if len(freq)==len(a):
            dst={c:i for i,c in enumerate(b)}; perm=[dst[c] for c in a]
            require(len(set(perm))==len(perm),'not bijective')
            for i in range(len(a)):
                if {perm[j]:w for j,w in adj[i].items()}!=adj[perm[i]]: return 0
            return 1
        _,cell=min((s,c) for c,s in freq.items() if s>1); i=a.index(cell); new=max(a)+1
        aa=a.copy(); aa[i]=new; total=0
        for j,x in enumerate(b):
            if x==cell:
                bb=b.copy(); bb[j]=new; total+=search(aa,bb)
        return total
    return search(c,c)

def check(q,n,mode,wanted,rates=None):
    actual=automorphisms(*incidence(q,n,mode,rates))
    require(actual==wanted,(q,n,mode,rates,actual,wanted))
    print(f'q={q} n={n} {mode} rates={rates}: {actual}',flush=True)

if __name__=='__main__':
    for mode in ['all','one']:
        for q,ns in [(2,range(1,7)),(3,range(1,5)),(4,range(1,4))]:
            for n in ns:
                expected=(factorial(q) if n==1 else factorial(q)*(2**comb(q,2) if n==2 else 2))
                check(q,n,mode,expected)
    check(3,0,'all',1)
    check(2,4,'all',4,(3,3));check(2,4,'all',2,(3,7))
    check(3,3,'all',4,(1,3,1));check(3,3,'all',2,(1,2,3));check(3,2,'all',8,(1,2,3))
    check(2,5,'one',4,(2,1,3,1,2));check(2,5,'one',2,(1,3,4,5,2));check(3,3,'one',6,(1,3,2))
    pairs=0
    for q,M in [(2,7),(3,4),(4,3)]:
        for n in range(M+1):
            top=words(q,n); allw=[x for i in range(n+1) for x in words(q,i)]
            uc={u:frozenset(i for i,x in enumerate(top) if sub(u,x)) for u in allw}
            for u in allw:
                for v in allw:
                    require(sub(u,v)==(uc[v]<=uc[u]),('separation',q,n,u,v)); pairs+=1
    print('exact column-order comparisons:',pairs,flush=True)
