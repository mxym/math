#!/usr/bin/env python3
from itertools import combinations

def is_forest(n, edges):
    p=list(range(n))
    def find(a):
        while p[a]!=a:
            p[a]=p[p[a]]
            a=p[a]
        return a
    for u,v in edges:
        a,b=find(u),find(v)
        if a==b:
            return False
        p[a]=b
    return True

def data_for_domain(n, mask, all_edges):
    pts=[x for x in range(1<<n) if mask>>x & 1]
    active=0
    for v in range(n):
        if len({(x>>v)&1 for x in pts})==2:
            active |= 1<<v
    pair=0
    for j,(u,v) in enumerate(all_edges):
        if len({((x>>u)^(x>>v))&1 for x in pts})==1:
            pair |= 1<<j
    return active,pair

def classify(n, edges, active, pair_global, edge_index):
    deg=[0]*n
    covered=0
    nonpair_deg=[0]*n
    for e in edges:
        j=edge_index[e]
        u,v=e
        deg[u]+=1; deg[v]+=1
        if pair_global>>j & 1:
            covered |= (1<<u)|(1<<v)
        else:
            nonpair_deg[u]+=1; nonpair_deg[v]+=1
    if active & ~covered == 0:
        return 1
    bad_terminal=any((active>>v)&1 and not((covered>>v)&1) and deg[v]<=1
                     for v in range(n))
    prediction=0 if bad_terminal else 2
    onebit=all(not((active>>v)&1) or ((covered>>v)&1) or nonpair_deg[v]>=2
               for v in range(n))
    direct=2 if onebit else 0
    assert prediction==direct
    return prediction

total=domains=finite=infinite=0
for n in range(1,5):
    all_edges=list(combinations(range(n),2))
    edge_index={e:i for i,e in enumerate(all_edges)}
    forests=[]
    for em in range(1<<len(all_edges)):
        edges=[e for j,e in enumerate(all_edges) if em>>j&1]
        if is_forest(n,edges):
            forests.append(edges)
    cache=[]
    for dm in range(1,1<<(1<<n)):
        cache.append(data_for_domain(n,dm,all_edges))
    domains += len(cache)
    for active,pair in cache:
        for edges in forests:
            c=classify(n,edges,active,pair,edge_index)
            total+=1
            if c: finite+=1
            else: infinite+=1
print("exact forest enumeration PASS")
print("domains",domains,"instances",total,"finite",finite,"infinite",infinite)
