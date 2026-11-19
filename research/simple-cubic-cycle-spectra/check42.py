from collections import Counter,defaultdict
from itertools import combinations_with_replacement
limit=42

def cycles(n,E):
    parent=list(range(n))
    def comp(i):
        while parent[i]!=i:i=parent[i]
        return i
    tree=[[] for i in range(n)]
    basis=[]
    for i,(a,b) in enumerate(E):
        A,B=comp(a),comp(b)
        if A!=B:
            parent[A]=B
            tree[a].append((b,i))
            tree[b].append((a,i))
        else:
            def path(u,p):
                if u==b:return 0
                for v,j in tree[u]:
                    if v==p:continue
                    k=path(v,u)
                    if k is not None:return k|(1<<j)
            basis.append((1<<i)|path(a,-1))
    cnt=0
    vals=[0]
    for p in basis: vals+= [v^p for v in vals]
    for mask in vals[1:]:
        adj=[set() for i in range(n)]
        active=set()
        for i,(a,b) in enumerate(E):
            if mask>>i&1:
                adj[a].add(b);adj[b].add(a)
                active.update((a,b))
        # Cubic implies any even selected degree is 0 or 2; connected
        # nonempty supports are exactly simple multigraph cycles (including digons).
        todo=[min(active)]
        used=set(todo)
        while todo:
            v=todo.pop()
            for w in adj[v]-used:
                todo.append(w);used.add(w)
        cnt+=len(used)==len(active)
        if cnt>limit:return cnt
    return cnt

def move(n,E,i,j):
    E1=[e for k,e in enumerate(E) if k!=i and k!=j]
    a,b=E[i];c,d=E[j]
    if i==j:E1.extend([(a,n),(n,n+1),(n+1,b)])
    else:E1.extend([(a,n),(n,b),(c,n+1),(n+1,d)])
    E1.append((n,n+1))
    return tuple(sorted(tuple(sorted(e)) for e in E1))

def signature(n,E):
    M=[[0]*n for _ in range(n)]
    for a,b in E:
        M[a][b]+=1
        M[b][a]+=1
    # Iterated canonical colour classes on full multiplicity matrix.
    colour=[0]*n
    for _ in range(n):
        rowkeys=[(colour[i],tuple(sorted((M[i][j],colour[j]) for j in range(n) if M[i][j]))) for i in range(n)]
        order={k:c for c,k in enumerate(sorted(set(rowkeys)))}
        nextc=[order[k] for k in rowkeys]
        if colour==nextc:break
        colour=nextc
    return (tuple(sorted(Counter(rowkeys).items())),M,colour)

def iso(A,B):
    _,M,c=A;_,N,d=B;n=len(c)
    rem=set(range(n));unused=set(range(n));mapped={}
    def rec():
        if not rem:return True
        packs=[]
        for i in rem:
            opts=[j for j in unused if d[j]==c[i] and all(M[i][a]==N[j][b] for a,b in mapped.items())]
            if not opts:return False
            packs.append((len(opts),-sum(M[i][a] for a in mapped),i,opts))
        _,_,i,opts=min(packs)
        rem.remove(i)
        for j in opts:
            unused.remove(j); mapped[i]=j
            if rec():return True
            del mapped[i];unused.add(j)
        rem.add(i)
        return False
    return rec()

def k33_subdivision(n,E):
    for mask in range(1,1<<len(E)):
        g=[set() for _ in range(n)]
        for i,(a,b) in enumerate(E):
            if mask>>i&1:g[a].add(b);g[b].add(a)
        if sorted(len(v) for v in g if v)!=[2]*(sum(bool(v) for v in g)-6)+[3]*6:continue
        for i in range(n):
            if len(g[i])==2:
                a,b=g[i]
                if b in g[a]:break
                g[a].remove(i);g[b].remove(i);g[i].clear()
                g[a].add(b);g[b].add(a)
        else:
            V=[v for v in range(n) if g[v]]
            if len(V)!=6:continue
            L=set(g[V[0]]);R=set(V)-L
            if len(L)==len(R)==3 and all(g[u]==R for u in L) and all(g[u]==L for u in R):
                return [e for i,e in enumerate(E) if mask>>i&1]
    return None

def main():
    n=2
    curr=[(((0,1),)*3,3)]
    hist=Counter()
    witnesses=[]
    while curr:
        simple=[(E,c) for E,c in curr if len(set(E))==len(E)]
        print('order',n,'all',len(curr),'simple',len(simple),flush=True)
        for E,c in simple:
            hist[c]+=1
            if c==42:witnesses.append((n,E,k33_subdivision(n,E)))
        shots=set()
        for E,k in curr:
            for i,j in combinations_with_replacement(range(len(E)),2):shots.add(move(n,E,i,j))
        out=defaultdict(list)
        for E in sorted(shots):
            c=cycles(n+2,E)
            if c>limit:continue
            H=signature(n+2,E)
            key=c,H[0]
            if not any(iso(H,J) for _,J in out[key]):out[key].append((E,H))
        curr=[(E,c) for (c,_),groups in out.items() for E,H in groups]
        n+=2
    print('general missing',sorted(set(range(1,43))-hist.keys()))
    print('42 witnesses',witnesses)
main()
