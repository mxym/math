#!/usr/bin/env python3
"""Independent affine-incidence arithmetic and explicit keyword-union tree checks."""
from collections import defaultdict
from itertools import combinations, product
from random import Random

if not __debug__:
    raise RuntimeError("enable Python assertions")

class Binary:
    def __init__(self,s,poly):
        self.s=s
        self.p=poly
    def mul(self,a,b):
        z=0
        while b:
            if b&1:
                z^=a
            a<<=1
            if a&self.s:
                a^=self.p
            b>>=1
        return z
    def power(self,a,k):
        r=1
        for _ in range(k):
            r=self.mul(r,a)
        return r

def union_tree(labels):
    labels=list(labels)
    by_layer=[]
    while len(labels)>1:
        assert len(labels)%2==0
        labels=[a|b for a,b in zip(labels[::2],labels[1::2])]
        by_layer.append(labels)
    return labels[0],by_layer

line_intersections=greedy_states=greedy_ties=point_nodes=macro_nodes=0
for c,h,poly in [(2,2,7),(4,1,7),(4,2,19)]:
    s=c**h
    r=s*s
    n=c*r
    FF=Binary(s,poly)
    base=[x for x in range(s) if FF.power(x,c)==x]
    assert len(base)==c and all(FF.power(x,s)==x for x in range(s))
    assert all(x^y in base and FF.mul(x,y) in base for x,y in product(base,repeat=2))

    expansion=[0]
    for _ in range(h):
        z=next(x for x in range(s) if x not in expansion)
        expansion=[x^FF.mul(y,z) for y in base for x in expansion]
        assert len(set(expansion))==len(expansion)
    assert len(expansion)==s
    points=list(product(range(s),repeat=2))
    lines={}
    leaf={}
    for u,v in points:
        x,y=expansion[u],expansion[v]
        for j in base:
            w=y^FF.mul(j,x)
            lines.setdefault((j,w),set()).add((u,v))
            leaf[u,v,j]=frozenset({("p",u,v),("c",j,0),("c",j,1),("l",j,w)})
    assert len(lines)==c*s and set(map(len,lines.values()))=={s}
    for (a,A),(b,B) in combinations(lines.items(),2):
        if a[0]!=b[0]:
            assert len(A&B)==1
            line_intersections+=1
        else:
            assert not A&B

    if n<=64:
        tie=Random(n+313)
        state=[(1,next(f[1:] for f in labels if f[0]=="l"),labels)
               for labels in leaf.values()]
        cost=0
        while len(state)>n//s:
            smallest=min(x[0] for x in state)
            best=10**9
            options=[]
            for i,j in combinations(range(len(state)),2):
                v=len(state[i][2]|state[j][2])
                if v<best:
                    best=v
                    options=[]
                if v==best:
                    options.append((i,j))
            assert best==2*smallest+3
            for i,j in options:
                a,g,_=state[i]
                b,h2,_=state[j]
                assert a==b==smallest and g==h2
                greedy_ties+=1
            i,j=tie.choice(options)
            a,g,W=state[i]
            b,_,Y=state[j]
            state=[x for z,x in enumerate(state) if z not in (i,j)]+[(a+b,g,W|Y)]
            cost+=best
            greedy_states+=1
        assert set(x[0] for x in state)=={s}
        assert cost==n*(s.bit_length()-1)+3*(n-n//s)

    blocks={}
    inner=0
    for u,v in points:
        labels,layers=union_tree(leaf[u,v,j] for j in base)
        inner+=sum(len(Z) for lev in layers for Z in lev)
        point_nodes+=sum(map(len,layers))
        blocks[u,v]=labels
    logc=c.bit_length()-1
    assert inner<=4*n*logc

    outer=[0,0,0]
    for i in range(h):
        z=c**i
        groups=defaultdict(list)
        for (u,v),labels in sorted(blocks.items()):
            assert sum(t[0]=="p" for t in labels)==z*z
            assert all(sum(t[0]=="l" and t[1]==j for t in labels)==z for j in base)
            groups[u//c,v//c].append(labels)
        blocks={}
        within=[[] for _ in range(2*logc)]
        for a,ls in groups.items():
            assert len(ls)==c*c
            result,layers=union_tree(ls)
            blocks[a]=result
            for k,nodes in enumerate(layers):
                within[k].extend(nodes)
        for nodes in within:
            macro_nodes+=len(nodes)
            assert all(sum(t[0]=="l" and t[1]==j for S in nodes for t in S)
                       <=r//z for j in base)
            for S in nodes:
                for f in S:
                    outer["pcl".index(f[0])]+=1
    assert len(blocks)==1
    assert outer[0]==2*h*logc*r
    assert outer[1]==2*c*(r-1)
    assert outer[2]<=4*n*logc
    assert inner+sum(outer)<=8*n*logc+2*c*r+2*h*logc*r

print(f"affine incidence: {line_intersections} cross-direction line pairs; {greedy_states} full greedy states; {greedy_ties} minimum ties checked")
print(f"explicit comparison trees: {point_nodes} point-subtree internal nodes; {macro_nodes} outer internal nodes")
print("verify_independent: PASS")
