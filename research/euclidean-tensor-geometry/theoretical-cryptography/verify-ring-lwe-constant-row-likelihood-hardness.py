"""Exact finite checks of the fixed crossover, signed shifts, and gap charging.

The script verifies local combinatorics only. It is not a decoder and does not
read input instances. Complexity statements are proved in the companion note.
"""
from itertools import product
from collections import Counter
P=((4,0),(2,2),(4,2),(6,2),(0,4),(2,4),(4,4),(6,4),(8,4),(2,6),(4,6),(6,6),(4,8))
E=((0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(2,6),(2,7),(3,7),(3,8),(4,5),(4,9),(5,6),(5,9),(5,10),(6,7),(6,10),(7,8),(7,10),(8,11),(9,12),(10,11),(10,12),(11,12))

from math import gcd
from random import Random

N, E0, S, W = 0, 8, 12, 4
Q=Counter((c[N],c[E0],c[S],c[W]) for c in product(range(3), repeat=13)
          if all(c[u]!=c[v] for u,v in E))
assert Q == {(a,b,a,b): 1+int(a==b) for a,b in product(range(3),repeat=2)}

def trace(start,end):
    x,y=start; X,Y=end
    swap=abs(X-x)<abs(Y-y)
    if swap: x,y,X,Y=y,x,Y,X
    step=(X>x)-(X<x); D=abs(X-x); old_y=y
    assert D>0
    points=[(x,y)]
    for t in range(1,D+1):
        a=x+t*step
        yy=(2*(D*y+t*(Y-y))+D)//(2*D)
        points.append((a,old_y))
        while old_y!=yy:
            old_y+=(yy>old_y)-(yy<old_y)
            points.append((a,old_y))
    return [(b,a) for a,b in points] if swap else points

scale, radius = 8, 3
centers=[(scale*a,scale*b) for a,b in P]
arms={N:(32,-8),E0:(72,32),S:(32,72),W:(-8,32)}
def distance(p,c):
    return max(abs(a-b) for a,b in zip(p,c))
def in_box(p,c):
    return distance(p,c)<=radius
def edges(path):
    for p,q in zip(path,path[1:]):
        assert sum(abs(a-b) for a,b in zip(p,q))==1
        yield tuple(sorted((p,q)))

active={}
square_vertices=set()
for x,y in centers:
    box=[(x+a,y+b) for a,b in ((-3,-3),(3,-3),(3,3),(-3,3),(-3,-3))]
    border=[]
    for a,b in zip(box,box[1:]):
        border+=trace(a,b)[:-1]
    assert len(border)==len(set(border))==24
    assert square_vertices.isdisjoint(border)
    square_vertices.update(border)
    for edge in edges(border+border[:1]):
        assert edge not in active
        active[edge]=0

walk_vertices=set()
for i,j in E+tuple((i,-1) for i in arms):
    src=centers[i]; dst=centers[j] if j>=0 else arms[i]
    seq=trace(src,dst)
    lo=max(k for k,x in enumerate(seq) if in_box(x,src))
    hi=min(k for k,x in enumerate(seq) if in_box(x,dst)) if j>=0 else len(seq)-1
    path=seq[lo:hi+1]
    assert len(path)>=3 and distance(path[0],src)==radius
    assert j<0 or distance(path[-1],dst)==radius
    assert not any(in_box(x,c) for x in path[1:-1] for c in centers)
    assert all(not in_box(path[0],c) for t,c in enumerate(centers) if t!=i)
    assert all(not in_box(path[-1],c) for t,c in enumerate(centers) if t!=j)
    assert len(path)==len(set(path)) and walk_vertices.isdisjoint(path)
    walk_vertices.update(path)
    for k,edge in enumerate(edges(path)):
        assert edge not in active
        active[edge]=int(j>=0 and k==0)
tile_points=square_vertices|walk_vertices
assert all(-8<=x<=72 and -8<=y<=72 for x,y in tile_points)
assert {p for p in tile_points if -8 in p or 72 in p}==set(arms.values())
assert (len(walk_vertices),len(tile_points),len(active),sum(active.values()))==(408,668,692,24)

m=0
phase6=((0,2,4),(0,0,0),(3,3,3))
for z in range(3):
    for k, ys in enumerate(phase6):
        r=[min((y-2*z)%6,(2*z-y)%6) for y in ys]
        if k==0: assert sorted(r)==[0,2,2]
        if k==1: assert r==[0 if z==0 else 2]*3
        if k==2: assert r==[3 if z==0 else 1]*3
        m+=1

def shift(v,h):
    d=len(v)
    return tuple((-1 if j<h else 1)*v[(j-h)%d]%3 for j in range(d))
masks=((0,1,2,0,1,2),(0,0,0,0,0,0),(1,1,1,2,2,2))
rng=Random(53426)
weights=0
for n in (8,16,32):
    d=n*n
    for h in (1,n):
        o=d//gcd(d,h)
        # Negacyclic order: X^(h o)=-1.
        assert (h*o)%d==0 and (h*o//d)%2==1
    for _ in range(12):
        v=tuple(rng.randrange(3) for _ in range(d))
        for h in (1,n):
            sv=shift(v,h)
            z=tuple((a-b)%3 for a,b in zip(v,sv))
            kinds=[rng.randrange(3) for _ in v]
            r=0
            for t in range(6):
                one=tuple(masks[a][t] for a in kinds)
                r+=sum(a!=b for a,b in zip(shift(one,t),shift(z,t)))
            assert r==sum((4 if k==0 else 0 if k==1 else 3)
                          +(k==1 and a!=0)*6+(k==2 and a==0)*3
                          for k,a in zip(kinds,z))
            weights+=len(z)
    pat=[{j,j+h} for h in (1,n) for j in range(6)]
    assert len({tuple(sorted(u)) for u in pat})==12
    assert all(n+j in pat[6+j] and sum(n+j in p for p in pat)==1 for j in range(6))

charges=0
for size in range(4,23):
    incidence=[]
    for u in range(size):
        for v in range(u+1,min(u+1+3,size)):
            if rng.randrange(2): incidence.append((u,v))
    if not incidence: continue
    delta=max(sum(u in e for e in incidence) for u in range(size))
    choices=[(u,None) for u in range(size)]+[(None,j) for j in range(len(incidence))]
    choices += [(u,j) for j,(v,w) in enumerate(incidence) for u in range(v,w+1)]
    for _ in range(250):
        issues=rng.choices(choices,k=rng.randrange(1,16))
        buses={b for b,_ in issues}
        wires={w for _,w in issues}
        compromised=sum(j in wires or u in buses or v in buses
                        for j,(u,v) in enumerate(incidence))
        assert compromised<=(delta+1)*len(issues)
        charges+=1
print("PASS: crossover colorings, tile edges, phase rows, signed Hamming slots, charge audits:",
      sum(Q.values()),len(active),m,weights,charges)
