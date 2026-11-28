#!/usr/bin/env python3
"""Exact finite checks for the free-abelian three-orbit cycle theorem."""
from itertools import product

def quotient_cases():
    pairs = ((0,1),(0,2),(1,2))
    residual = [0,0]
    min_deg_count=0
    for cross in product(range(3), repeat=3):
        for inner in product(range(3), repeat=3):
            degrees = list(inner)
            for e,s in zip(pairs,cross):
                for i in e:
                    degrees[i]+=s
            if min(degrees)<3:
                continue
            min_deg_count+=1
            if any(s and inner[i] and inner[j]
                   for s,(i,j) in zip(cross,pairs)):
                continue
            if cross.count(2)>=2:
                continue
            assert cross.count(2)==1
            a,b=pairs[cross.index(2)]
            c=3-a-b
            left=sum(s for e,s in zip(pairs,cross) if c in e)
            assert left in (1,2)
            if left==2:
                assert inner[c]>=1 and inner[a]==inner[b]==0
            else:
                if next(s for e,s in zip(pairs,cross) if set(e)=={b,c}):
                    a,b=b,a
                assert inner[a]==0 and inner[b]>=1 and inner[c]>=2
            residual[left-1]+=1
    return min_deg_count,residual

def build(mods,x,d,y):
    vals=list(product(*(range(m) for m in mods)))
    def add(a,b):return tuple((u+v)%m for u,v,m in zip(a,b,mods))
    def link(a,b):
        assert a!=b
        G[a].add(b)
        G[b].add(a)
    G={(i,v):set() for i in range(3) for v in vals}
    zero=(0,)*len(mods)
    for v in vals:
        link((0,v),(1,v));link((0,v),(1,add(v,d)));link((0,v),(2,v))
        link((1,v),(1,add(v,y)));link((2,v),(2,add(v,x)))
    assert set(map(len,G.values()))=={3}
    seen={(0,zero)}
    stack=list(seen)
    while stack:
        a=stack.pop()
        for b in G[a]-seen:
            seen.add(b)
            stack.append(b)
    assert seen==set(G)
    return G,add,zero

def cycle_start(G, start, length):
    path=[start]; used={start}
    def visit():
        if len(path)==length:
            return tuple(path) if start in G[path[-1]] else None
        for v in G[path[-1]]:
            if v in used:
                continue
            used.add(v);path.append(v)
            ans=visit()
            path.pop();used.remove(v)
            if ans is not None:
                return ans
        return None
    return visit()

def set_of_lengths(G,start,lengths):
    return [k for k in lengths if cycle_start(G,start,k) is not None]

def main():
    n,res=quotient_cases()
    print('finite quotient cases with minimum degree:',n,'two residual types:',res)
    small=0
    for d in product(range(3),range(2)):
        if d==(0,0):
            continue
        G,_,zero=build((3,2),(1,0),d,(0,1))
        assert cycle_start(G,(0,zero),4 if d==(0,1) else 8)
        small+=1
    print('order-three times order-two shift residues:',small)
    G,_,z=build((3,2),(1,0),(0,1),(0,1))
    observed=set_of_lengths(G,(2,z),range(3,19))
    assert observed==[3,10,11,12,13,14]
    print('complete marked-orbit length list in the 18-point graph:',observed)
    sample=0
    for m in range(5,33):
        x=(1,0,0);d=(0,1,0);y=(0,0,1)
        G,plus,z=build((3,m,2),x,d,y)
        assert not any(cycle_start(G,(i,z),k) for i in range(3) for k in (4,8))
        nd=(0,m-1,0);t=plus(nd,y)
        P=[(0,z),(1,z),(0,nd),(1,nd),(1,t),(0,t)]
        Px=[(i,plus(v,x)) for i,v in P]
        cycle=P+[(2,t),(2,plus(t,x))]+Px[::-1]+[(2,x),(2,z)]
        assert len(cycle)==len(set(cycle))==16
        assert all(b in G[a] for a,b in zip(cycle,cycle[1:]+cycle[:1]))
        sample+=1
    print('connected sharp cubic examples checked:',sample)

if __name__=='__main__':
    main()
