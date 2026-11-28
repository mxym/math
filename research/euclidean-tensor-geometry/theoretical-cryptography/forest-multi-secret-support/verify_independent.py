#!/usr/bin/env python3
import random
from collections import defaultdict, deque

rng=random.Random(20261128)

def classify_and_build(n, edges, D):
    inc=[[] for _ in range(n)]
    for j,(u,v) in enumerate(edges):
        inc[u].append(j); inc[v].append(j)
    active=[len({x[v] for x in D})==2 for v in range(n)]
    pair=[]; const=[]
    for u,v in edges:
        vals={x[u]^x[v] for x in D}
        pair.append(len(vals)==1)
        const.append(next(iter(vals)) if len(vals)==1 else None)
    covered=[any(pair[j] for j in inc[v]) for v in range(n)]
    bad=[v for v in range(n) if active[v] and not covered[v] and len(inc[v])<=1]
    if bad:
        v=bad[0]
        if not inc[v]: return 0,None
        j=inc[v][0]
        u,w=edges[j]; other=w if u==v else u
        left=sorted({x[v] for x in D}); right=sorted({x[other] for x in D})
        adj={("L",a):set() for a in left}
        adj.update({("R",b):set() for b in right})
        for x in D:
            a=("L",x[v]); b=("R",x[other])
            adj[a].add(b); adj[b].add(a)
        seen=set(); stack=[next(iter(adj))]
        while stack:
            a=stack.pop()
            if a in seen: continue
            seen.add(a); stack.extend(adj[a]-seen)
        assert len(seen)==len(adj) and not pair[j]
        return 0,None
    if all(not active[v] or covered[v] for v in range(n)):
        def shares(x,r=0):
            return tuple(x[u] if pair[j] else 0 for j,(u,v) in enumerate(edges))
        return 1,shares

    H=[j for j in range(len(edges)) if not pair[j]]
    qsign={(v,j):0 for j in H for v in edges[j]}
    for v in range(n):
        if active[v] and not covered[v]:
            js=[j for j in inc[v] if j in H]
            assert len(js)>=2
            qsign[(v,js[1])]=1
    hadj=[[] for _ in range(n)]
    for j in H:
        u,v=edges[j]
        hadj[u].append((v,j)); hadj[v].append((u,j))
    parent=[None]*n; pedge=[None]*n
    for root in range(n):
        if parent[root] is not None: continue
        parent[root]=root; dq=deque([root])
        while dq:
            u=dq.popleft()
            for v,j in hadj[u]:
                if parent[v] is None:
                    parent[v]=u; pedge[v]=j; dq.append(v)
    x0=D[0]
    def shares(x,r):
        h=[0]*n
        pending={v for v in range(n) if parent[v]!=v}
        while pending:
            moved=False
            for v in list(pending):
                u=parent[v]
                if u in pending: continue
                j=pedge[v]; a,b=edges[j]
                g=(qsign[(a,j)]*(x[a]^x0[a]))^(qsign[(b,j)]*(x[b]^x0[b]))
                h[v]=h[u]^g
                pending.remove(v); moved=True
            assert moved
        out=[]
        for j,(u,v) in enumerate(edges):
            if pair[j]: out.append(x[u])
            else: out.append(r^h[u]^(qsign[(u,j)]*(x[u]^x0[u])))
        return tuple(out)
    return 2,shares

def verify(n, edges, D, support, shares):
    if support==0: return
    inc=[[] for _ in range(n)]
    for j,(u,v) in enumerate(edges):
        inc[u].append(j); inc[v].append(j)
    states=range(support)
    for v in range(n):
        owner={}; laws={}
        for x in D:
            vals=[]
            for r in states:
                sh=shares(x,r)
                view=tuple(sh[j] for j in inc[v])
                if view in owner: assert owner[view]==x[v]
                else: owner[view]=x[v]
                vals.append(view)
            sv=tuple(sorted(vals)); key=x[v]
            if key in laws: assert laws[key]==sv
            else: laws[key]=sv

checked={0:0,1:0,2:0}
for _ in range(5000):
    n=rng.randint(1,12)
    edges=[]
    for v in range(1,n):
        if rng.random()<0.82: edges.append((rng.randrange(v),v))
    pts=[tuple(rng.randrange(2) for _ in range(n))
         for _ in range(rng.randint(1,min(64,1<<min(n,10))))]
    D=sorted(set(pts))
    support,shares=classify_and_build(n,edges,D)
    verify(n,edges,D,support,shares)
    checked[support]+=1
print("independent construction/privacy/correctness PASS")
print("instances",sum(checked.values()),"classes",checked)
