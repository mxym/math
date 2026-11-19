#!/usr/bin/env python3
"""Small independent edge-set replays; not used to deduce asymptotics."""
from collections import defaultdict
from itertools import combinations,product

def verify(b):
    if not b: raise RuntimeError("failed exact check")

def edge(a,b):return tuple(sorted((a,b)))

def make(n,caps=False):
    g=defaultdict(set); cx={}; typ={}
    def v(t,i,c):
        x=t+str(i);cx[x]=c;typ[x]=t;return x
    def path(seq):
        for x,y in zip(seq,seq[1:]):
            g[x].add(y);g[y].add(x)
    for i in range(n):
        a=v('A',i,2*i);b=v('B',i,2*i);q=v('P',i,2*i);path([a,q,b])
        if i:
            for c in ['A','B']:
                path([c+str(i-1),v(c.lower(),i,2*i-1),c+str(i)])
    if caps:
        for i in (0,n-1):
            path(['A'+str(i),v('C',i,2*i),'B'+str(i)])
    return g,cx,typ

def simple(g,x,dests,forbidden=()):
    used=set(forbidden)|{x};p=[x]
    def go(v):
        if v in dests:yield tuple(p);return
        for b in sorted(g[v]-used):
            p.append(b);used.add(b);yield from go(b);used.remove(b);p.pop()
    yield from go(x)

def disjoint_link(g,n,x,y):
    # The inserted external vertex Q has degree two. DFS finds the whole
    # two-linkage and certifies the use of Q without classifying attachments.
    g['Q']={x,y};g[x].add('Q');g[y].add('Q')
    ends={'A'+str(n-1),'B'+str(n-1)}
    for p in simple(g,'A0',ends,{'B0'}):
        t=p[-1];u=next(iter(ends-{t}))
        for q in simple(g,'B0',{u},p):
            if 'Q' in p or 'Q' in q:
                g[x].remove('Q');g[y].remove('Q');del g['Q']
                return p,q
    raise RuntimeError((x,y))

def local_and_glue():
    n=7;g,c,t=make(n);mid=n-1
    X=[x for x in c if 0<c[x]<mid]
    Y=[y for y in c if mid<c[y]<2*n-2 or c[y]==mid and t[y]=='P']
    samples={}
    for x in X:
        for y in Y:
            a,b=disjoint_link(g,n,x,y)
            verify(not (set(a)&set(b)))
            key='middle' if t[y]=='P' and c[y]==mid else 'straight' if a[-1][0]=='A' else 'swapped'
            samples.setdefault(key,(x,y,a,b))
    verify(len(samples)==3)
    # Glue explicit local witnesses in 3 slabs, compare sorted edge sets and
    # verify connected 2-regular directly after adding 2 end caps.
    nevid=0
    for keys in product(sorted(samples),repeat=3):
        signatures=set()
        for mask in range(8):
            h=defaultdict(set)
            def add(x,y):h[x].add(y);h[y].add(x)
            for j,key in enumerate(keys):
                x,y,P,Q=samples[key]
                default=[tuple(sum(([l+str(i),l.lower()+str(i+1)] for i in range(n-1)),[])+[l+str(n-1)]) for l in ('A','B')]
                for path in (P,Q) if (mask>>j)&1 else default:
                    for a,b in zip(path,path[1:]):add((j,a),(j,b))
                if j:
                    for l in ('A','B'):add((j-1,l+str(n-1)),(j,l+'0'))
            add((0,'A0'),(0,'B0'));add((2,'A6'),(2,'B6'))
            verify(all(len(N)==2 for N in h.values()))
            reached={(0,'A0')};q=list(reached)
            for v in q:
                for w in h[v]-reached:reached.add(w);q.append(w)
            verify(len(reached)==len(h))
            signatures.add(frozenset(edge(x,y) for x in h for y in h[x]))
        verify(len(signatures)==8);nevid+=len(signatures)
    return len(X)*len(Y),nevid

def long_paths():
    g,c,t=make(8,True);cases=0
    for x,y in combinations(c,2):
        a,b=sorted((c[x],c[y]));sw=sum(a<2*i<b for i in range(8))
        if sw<3:continue
        count=0
        for _ in simple(g,x,{y}):
            count+=1
            if count>=2**(sw-1):break
        verify(count>=2**(sw-1));cases+=1
    return cases

def wrapped(r):
    # Same cyclic order on the two arcs: increase on both rails and use the cross-cap.
    g,c,t=make(r);a='A0';b='B'+str(r-1)
    count=0
    for _ in simple(g,a,{b}):
        count+=1
    verify(count>=2**(r-1));return count

if __name__=='__main__':
    branches,cycs=local_and_glue()
    print("all toy short-bridge attachment pairs on a fully subdivided seven-rung slab:",branches)
    print("connected 2-regular choices across all 27 ordered triples of linkage types:",cycs)
    print("long-bridge pairs tested on a fully subdivided capped eight-rung ladder:",long_paths())
    print("open-rail opposite-end paths (2 through 8 rungs):",[wrapped(r) for r in range(2,9)])
    print("Finite gadget checks passed. The all-order assertion uses the written proof.")
