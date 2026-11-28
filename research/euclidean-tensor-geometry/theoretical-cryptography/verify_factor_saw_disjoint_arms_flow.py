#!/usr/bin/env python3
"""Independent finite max-flow cross-check of the square-grid arm obstruction."""
from collections import Counter, deque
from itertools import product
import sys

if not __debug__:
    raise RuntimeError("run without -O")
DIRS = (1, -1, 1j, -1j)


def flow(cells, starts, sinks, need):
    # Each source/sink is (grid point, edge capacity). The split start is
    # allowed to carry both units only for a single common root.
    order = dict(zip(cells, range(len(cells))))
    src, snk = 2*len(cells), 2*len(cells)+1
    Q = [[] for _ in range(snk+1)]
    def edge(u, v, cap):
        i, j = len(Q[u]), len(Q[v])
        Q[u].append([v, cap, j])
        Q[v].append([u, 0, i])
    for u, i in order.items():
        edge(2*i, 2*i+1, need if starts.get(u,0)>1 else 1)
        for d in DIRS:
            if u+d in order:
                edge(2*i+1, 2*order[u+d], need)
    for u,c in starts.items():
        edge(src,2*order[u],c)
    for u,c in sinks.items():
        edge(2*order[u]+1,snk,c)
    cnt=0
    while cnt<need:
        parent={src:None}; pending=deque([src])
        while pending and snk not in parent:
            u=pending.popleft()
            for k,(v,c,r) in enumerate(Q[u]):
                if c and v not in parent:
                    parent[v]=(u,k)
                    pending.append(v)
        if snk not in parent: break
        v=snk
        while v != src:
            u,k=parent[v]
            _,c,r=Q[u][k]
            Q[u][k][1]=c-1; Q[v][r][1]+=1
            v=u
        cnt+=1
    return cnt


def box(P):
    a=int(min(u.real for u in P))-1; b=int(max(u.real for u in P))+1
    c=int(min(u.imag for u in P))-1; d=int(max(u.imag for u in P))+1
    V={complex(x,y) for x,y in product(range(a,b+1),range(c,d+1))}
    B={u for u in V if u.real in (a,b) or u.imag in (c,d)}
    return V, B


def reach(V, s, T):
    waiting=[s]; seen={s}
    while waiting:
        u=waiting.pop()
        if u in T: return True
        for w in (u+d for d in DIRS):
            if w in V and w not in seen:
                waiting.append(w); seen.add(w)
    return False


def compare_one_ended():
    obstacles = tuple(complex(x,y) for x,y in product(range(3),range(2)))
    n=0
    for mask in range(1<<len(obstacles)):
        O={u for j,u in enumerate(obstacles) if mask>>j&1}
        for t in set(obstacles)-O:
            B,R=box(obstacles); V=B-O
            if not reach(V,t,R):continue
            for z in V-R-{t}:
                dead_b=not reach(V-{t},z,R)
                dead_c=any(not reach(V-{w},z,R|{t}) for w in V-{z,t})
                # A new sink vertex for the outside (1 unit total even with
                # many possible ring endpoints). Choose unoccupied coordinate
                # and give it custom adjacency by using a virtual cell network.
                # Avoid virtual coordinates by forcing t and the chosen rim
                # entry to have capacity 1 each, trying every possible entry.
                live=any(flow(V,{z:2},{t:1,r:1},2)==2 for r in R)
                assert (not live)==(dead_b or dead_c), (O,t,z)
                n+=1
    return n


def main():
    cap=int(sys.argv[1]) if len(sys.argv)>1 else 10
    bylen=[Counter() for _ in range(cap+1)]
    path=[0j,1+0j]; used=set(path)
    hits=[]
    def dfs():
        n=len(path)-1
        a,b=path[0],path[-1]
        V,R=box(path); V-=set(path[1:-1])
        sep=reach(V-{b},a,R) and reach(V-{a},b,R)
        joint=flow(V,{a:1,b:1},dict.fromkeys(R,1),2)==2
        assert not joint or sep
        bylen[n]['joint' if joint else 'sep-only' if sep else 'not-sep']+=1
        if sep and not joint and n==10:
            hits.append(tuple(path))
        if n<cap:
            for d in DIRS:
                z=b+d
                if z in used:continue
                used.add(z); path.append(z); dfs()
                path.pop(); used.remove(z)
    dfs()
    assert [bylen[i]['sep-only'] for i in range(1,11)]==[0]*9+[4]
    assert (bylen[10]['not-sep'],bylen[10]['joint'])==(120,10901)
    assert all(abs(w[-1].real)+abs(w[-1].imag)==2 for w in hits)
    assert len({min(tuple((int(z.real),int(z.imag)) for z in w),
                       tuple((int(z.real),-int(z.imag)) for z in w))
                for w in hits})==2
    assert compare_one_ended()==480
    print("independent vertex-split max-flow cross-check PASS",bylen[-1])

if __name__=='__main__':
    main()
