from collections import Counter,defaultdict
from itertools import combinations

BUDGET=34
def count(n,E):
    parent=list(range(n));T=[[] for _ in range(n)];basis=[]
    def r(i):
        while parent[i]!=i:i=parent[i]
        return i
    def path(v,w,pa):
        if v==w:return 0
        for t,j in T[v]:
            if t==pa:continue
            q=path(t,w,v)
            if q is not None:return q|(1<<j)
    for i,(u,v) in enumerate(E):
        U,V=r(u),r(v)
        if U!=V:
            parent[U]=V
            T[u].append((v,i));T[v].append((u,i))
        else:
            basis.append((1<<i)|path(u,v,-1))
    span=[0]
    for h in basis:span.extend(v^h for v in span[:])
    cyc=0
    for mask in span[1:]:
        adj=[[] for _ in range(n)]
        a=mask
        while a:
            i=(a&-a).bit_length()-1;a&=a-1
            u,v=E[i];adj[u].append(v);adj[v].append(u)
        V=[i for i,ns in enumerate(adj) if ns]
        if any(len(adj[i])!=2 for i in V):continue
        done={V[0]};visit=list(done)
        while visit:
            for w in adj[visit.pop()]:
                if w not in done:done.add(w);visit.append(w)
        if len(done)==len(V):
            cyc+=1
            if cyc>BUDGET:return cyc
    return cyc
def sig(n,E):
    A=[[0]*n for _ in range(n)]
    for u,v in E:A[u][v]+=1;A[v][u]+=1
    colour=[0]*n
    for _ in range(n):
        rows=[(colour[i],tuple(sorted((A[i][j],colour[j]) for j in range(n) if A[i][j]))) for i in range(n)]
        ix={r:c for c,r in enumerate(sorted(set(rows)))}
        nex=[ix[r] for r in rows]
        if nex==colour:break
        colour=nex
    return tuple(sorted(Counter(rows).items())),A,colour
def iso(x,y):
    _,A,c=x;_,B,d=y;n=len(c)
    pa={};left=set(range(n));right=set(range(n))
    def dfs():
        if not left:return True
        pairs=[]
        for i in left:
            options=[j for j in right if c[i]==d[j] and all(A[i][a]==B[j][b] for a,b in pa.items())]
            if not options:return False
            pairs.append((len(options),i,options))
        _,i,options=min(pairs)
        left.remove(i)
        for j in options:
            pa[i]=j;right.remove(j)
            if dfs():return True
            del pa[i];right.add(j)
        left.add(i)
        return False
    return dfs()
def children(n,E):
    # Make both proposed endpoints as positions on original edge occurrences
    # by first materializing each once-subdivided configuration.
    def add(l,s,t):
        return tuple(sorted(tuple(sorted(e)) for e in l+[(s,t)]))
    for a,b in combinations(range(n),2):
        yield n,add(list(E),a,b)
    for i,(a,b) in enumerate(E):
        old=[e for j,e in enumerate(E) if j!=i]
        p=old+[(a,n),(n,b)]
        for v in range(n):
            yield n+1,add(p,v,n)
        yield n+2,add(old+[(a,n),(n,n+1),(n+1,b)],n,n+1)
        for j in range(i+1,len(E)):
            a1,b1=E[j]
            p1=[e for h,e in enumerate(E) if h not in (i,j)]+[(a,n),(n,b),(a1,n+1),(n+1,b1)]
            yield n+2,add(p1,n,n+1)
def con3(n,E):
    if n<4 or len(E)!=len(set(E)):return False
    adj=[set() for _ in range(n)]
    for a,b in E:adj[a].add(b);adj[b].add(a)
    if min(map(len,adj))<3:return False
    for t in range(3):
        for bad in combinations(range(n),t):
            seen=set(bad);q=[next(j for j in range(n) if j not in seen)];seen.update(q)
            while q:
                growing=adj[q.pop()]-seen
                seen.update(growing);q.extend(growing)
            if len(seen)!=n:return False
    return True
def main():
    live=[(2,((0,1),)*3,3)];rank=2
    yes=set()
    while live:
        kept=0
        seeds=set()
        for n,E,k in live:
            if con3(n,E):kept+=1;yes.add(k)
            if k<BUDGET:seeds.update(children(n,E))
        print(rank,len(live),kept,flush=True)
        bins=defaultdict(list)
        for n,E in sorted(seeds):
            k=count(n,E)
            if k>BUDGET:continue
            p=sig(n,E)
            d=bins[n,k,p[0]]
            if not any(iso(p,q) for _,q in d):d.append((E,p))
        live=[(n,E,k) for (n,k,_),group in bins.items() for E,p in group]
        rank+=1
    print("missing",sorted(set(range(1,BUDGET+1))-yes))
main()
