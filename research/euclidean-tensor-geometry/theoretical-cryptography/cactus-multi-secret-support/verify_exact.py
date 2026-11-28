#!/usr/bin/env python3
"""Construct simultaneous whole views from exact cactus block certificates."""
from collections import Counter
from itertools import permutations, product


def edge(u,v):
    return tuple(sorted((u,v)))


def perimeter(C):
    return tuple(edge(u,v) for u,v in zip(C,C[1:]+C[:1]))


def neighbors(E,v):
    return sorted(w if u==v else u for u,w in E if v in (u,w))


def parse_cases():
    cube=lambda n: tuple(product((0,1), repeat=n))
    words=lambda *ss: tuple(tuple(map(int,s)) for s in ss)
    T=words("000","011","101","110")
    C=words("0000","0111","1001","1010","1100")
    glue=lambda X,Y: tuple(x+y[1:] for x in X for y in Y if x[0]==y[0])
    tri=perimeter((0,1,2))
    sq=perimeter((0,3,4,5))
    return (
        ("singleton-impossible",(),cube(1),0,None),
        ("path-impossible",((0,1),(1,2)),cube(3),0,None),
        ("pair-only",((0,1),(1,2)),words("000","111"),1,None),
        ("path-feasible",((0,1),(1,2)),words("000","010"),2,(True,True)),
        ("mixed-source",tri+sq,glue(T,C),4,(False,False)),
        ("triangle-binary-only",tri+((0,3),),tuple(x+(0,) for x in T),2,(True,False)),
        ("two-ternary-blocks",perimeter((0,1,2,3))+perimeter((0,4,5,6)),
                                      glue(C,C),3,(False,True)),
        ("pair-deleted-triangle",tri+((0,3),),tuple(x+(x[0],) for x in cube(3)),
                                      4,(False,False)),
        ("pair-bridge-two-components",perimeter((0,1,2,3))+
             perimeter((4,5,6,7))+((0,4),),tuple(x+y for x in C for y in C if x[0]==y[0]),
                                      3,(False,True)),
        ("bridge-joined-ternary-blocks",perimeter((0,1,2,3))+
             perimeter((4,5,6,7))+((0,4),),tuple(x+y for x in C for y in C),
                                      3,(False,True)),
        ("triangle-chain",tri+perimeter((0,3,4))+perimeter((4,5,6)),
                                      cube(7),4,(False,False)),
    )


def extract_cycles(H):
    cs={}
    for u,v in H:
        F=H-{edge(u,v)}
        todo=[(u,)]
        seen={u}
        while todo:
            P=todo.pop(0)
            if P[-1]==v:
                cs.setdefault(frozenset(perimeter(P)),P)
                break
            for w in neighbors(F,P[-1]):
                if w not in seen:
                    seen.add(w)
                    todo.append(P+(w,))
    assert sum(map(len,cs))==len(set().union(*cs))
    return tuple(sorted(cs.values()))


def setup(E,D):
    V=range(len(D[0]))
    pair={e for e in E if len({x[e[0]]^x[e[1]] for x in D})==1}
    H=set(E)-pair
    req={v for v in V if len({x[v] for x in D})==2 and all(v not in e for e in pair)}
    cycles=extract_cycles(H)
    rig={v for v in req if len(neighbors(H,v))==2}
    return H,pair,req,cycles,rig


def try_block(C,D,rig,m):
    ES=perimeter(C)
    I=tuple(range(m))
    for e in ES:
        if all(v not in rig for v in e):
            return (e,tuple(tuple((r+int(v in rig))%m for r in I) for v in C),False)
    P=tuple(permutations(I))
    alt={tuple(x[v]^D[0][v] for v in C) for x in D}
    allowed=[tuple(p for p in P if v not in rig or all(p[r]!=r for r in I)) for v in C]
    for maps in product(*allowed):
        def image(bits):
            a=I
            for b,p in zip(bits,maps):
                if b:
                    a=tuple(p[r] for r in a)
            return a
        if all(image(b)==I for b in alt):
            return (None,maps,True)
    return None


def nodal_plan(H,cycles,cert,D,req,m):
    part=[set(perimeter(C)) for C in cycles]
    bridges=sorted(H-set().union(*part))
    I=tuple(range(m))
    n=len(D[0])
    blocks=[]
    for C,S,(om,P,relative) in zip(cycles,part,cert):
        ES=perimeter(C)
        keep=S-{om}
        arcs=[(ES[i-1],ES[i],v,p,relative) for i,(v,p) in
              enumerate(zip(C,P)) if ES[i-1] in keep and ES[i] in keep]
        blocks.append((tuple(sorted(keep)),arcs))
    blocks += [((e,),[]) for e in bridges]
    incidence={v:[] for v in range(n)}
    for j,(es,_) in enumerate(blocks):
        for v in sorted(set().union(*es)):
            incidence[v].append(j)

    def apply(x,r):
        W={e:0 for e in H}
        seen=set()
        def enter(j,anchor,t):
            es,arcs=blocks[j]
            vs=sorted(set().union(*es))
            first=es[0] if anchor is None else next(e for e in es if anchor in e)
            values={first:t}
            while True:
                old=len(values)
                for e,f,v,p,rel in arcs:
                    a=p if x[v]^(D[0][v] if rel else 0) else I
                    if e in values and f in values:
                        assert values[f]==a[values[e]]
                    elif e in values:
                        values[f]=a[values[e]]
                    elif f in values:
                        values[e]=a.index(values[f])
                if len(values)==old:
                    break
            assert set(values)==set(es)
            W.update(values)
            seen.add(j)
            for v in vs:
                if v==anchor:
                    continue
                t_v=values[next(e for e in es if v in e)]
                children=tuple(k for k in incidence[v] if k!=j)
                for z,k in enumerate(children):
                    assert k not in seen
                    enter(k,v,(t_v+int(z==0 and v in req)*x[v])%m)
        for j in range(len(blocks)):
            if j not in seen:
                enter(j,None,r)
        return W
    return apply


def forest_plan(H,cycles,req,rig,n):
    F=[set(H),set(H)]
    for C in cycles:
        ES=perimeter(C)
        if len(C)==3:
            v=next(v for v in C if v not in rig)
            pair=[e for e in ES if v in e]
        else:
            pair=[ES[0],ES[2]]
        for S,e in zip(F,pair):
            S.remove(e)
    assigned=[set(),set()]
    for v in req:
        assigned[next(i for i,S in enumerate(F) if len(neighbors(S,v))>=2)].add(v)

    def apply(x,R):
        w={}
        for i,S in enumerate(F):
            signs={v:edge(v,neighbors(S,v)[0]) for v in assigned[i]}
            h={}
            for v in range(n):
                if v in h:
                    continue
                h[v]=0
                todo=[(v,None)]
                while todo:
                    u,parent=todo.pop()
                    for y in neighbors(S,u):
                        if y==parent:
                            continue
                        e=edge(u,y)
                        assert y not in h
                        h[y]=h[u]^(int(signs.get(u)==e)*x[u])^(int(signs.get(y)==e)*x[y])
                        todo.append((y,u))
            for e in S:
                v=e[0]
                w.setdefault(e,[]).append(((R>>i)&1)^h[v]^(int(signs.get(v)==e)*x[v]))
        return {e:tuple(w.get(e,())) for e in H}
    return apply


def verify_views(E,D,m,fn,pair):
    E=sorted(E)
    phi={}
    for x in D:
        table=[]
        for r in range(m):
            w=fn(x,r)
            table.append(w | {e:x[e[0]] for e in pair})
        for v,b in enumerate(x):
            law=Counter(tuple(w[e] for e in E if v in e) for w in table)
            assert phi.setdefault((v,b),law)==law
    for v in range(len(D[0])):
        a,b=phi.get((v,0)),phi.get((v,1))
        if a is not None and b is not None:
            assert set(a).isdisjoint(b)


def run():
    count=checks=four=0
    for name,E,D,want,allowed in parse_cases():
        H,pair,req,C,rig=setup(E,D)
        if any(len(neighbors(H,v))<2 for v in req):
            assert not want
            count+=1
            continue
        cs=[tuple(try_block(c,D,rig,m) for c in C) for m in (2,3)]
        flags=tuple(all(v is not None for v in c) for c in cs)
        if allowed is not None:
            assert flags==allowed, (name,flags,allowed)
        m=1 if not req else 2 if flags[0] else 3 if flags[1] else 4
        assert m==want, (name,m)
        if m==1:
            verify_views(E,D,1,lambda x,r:{e:0 for e in H},pair)
            checks+=len(D)
        for i,ok in enumerate(flags):
            if ok:
                q=i+2
                fn=nodal_plan(H,C,cs[i],D,req,q)
                verify_views(E,D,q,fn,pair)
                checks+=q*len(D)
        fn=forest_plan(H,C,req,rig,len(D[0]))
        verify_views(E,D,4,fn,pair)
        four+=4*len(D)
        count+=1
    print(f"EXACT: {count} domains, {checks} one/two/three-state and {four} four-state input-seed rows checked against whole views")


if __name__=="__main__":
    run()
