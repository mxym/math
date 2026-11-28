#!/usr/bin/env python3
"""Exact enumeration and certificate replay for general free abelian six-orbit graphs."""
import base64
from collections import Counter
import gzip
from itertools import combinations, permutations, product
import json
from pathlib import Path
import sys

N=6
PAIRS=tuple(combinations(range(N),2))
NUM={e:i for i,e in enumerate(PAIRS)}
K33="000000001110111111000"
EXTRA=(
    "000000002110111111000",  # another cross matching
    "000000101110111111000",  # a matching inside a base part
    "100000001110111111000",  # one internal involution
    "200000001110111111000",  # opposite non-involutory internal steps
)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def shape_enumeration():
    """Enumerate the underlying simple graphs first, then double matchings."""
    maps=[(p,tuple(NUM[tuple(sorted((p[i],p[j])))] for i,j in PAIRS))
          for p in permutations(range(N))]
    assigned={}
    reps=Counter()
    for mask in range(1,1<<len(PAIRS)):
        present=tuple(k for k in range(len(PAIRS)) if mask>>k&1)
        if len(present)<N-1:
            continue
        edges=[PAIRS[k] for k in present]
        adj=[set() for _ in range(N)]
        for i,j in edges:
            adj[i].add(j);adj[j].add(i)
        reached={0}
        for _ in range(N-1):
            reached|=set().union(*(adj[j] for j in reached))
        if len(reached)!=N:
            continue
        degree=sum((1<<(4*i))+(1<<(4*j)) for i,j in edges)
        def matchings(k,used,double,code):
            yield double,code
            for q in range(k,len(present)):
                i,j=edges[q]
                two=1<<i|1<<j
                if two&used:continue
                yield from matchings(q+1,used|two,double|1<<present[q],
                                     code+(1<<(4*i))+(1<<(4*j)))
        for double,dg in matchings(0,0,0,degree):
            cross=tuple((dg>>(4*i))&15 for i in range(N))
            internal={i for i in range(N) if cross[i]<3}
            if any(adj[i]&internal for i in internal):
                continue
            options=[(0,) if c>=3 else (1,2) if c==2 else (2,) for c in cross]
            mult=tuple((mask>>k&1)+(double>>k&1) for k in range(len(PAIRS)))
            for ls in product(*options):
                large={i for i in range(N) if cross[i]+ls[i]>3}
                if any(adj[i]&large for i in large):
                    continue
                key=ls+mult
                rep=assigned.get(key)
                if rep is None:
                    orbit={tuple(ls[i] for i in p)+tuple(mult[i] for i in q) for p,q in maps}
                    rep="".join(map(str,min(orbit)))
                    for v in orbit:
                        assigned[v]=rep
                reps[rep]+=1
    require(sum(reps.values())==130348 and len(reps)==291,("shape census",sum(reps.values()),len(reps)))
    require(len(assigned)==130348 and reps[K33]==10,"orbit census")
    require(all(count==sum(v==name for v in assigned.values())
                for name,count in reps.items()),"some relabeling missing")
    return reps


def row_hnf(R,n):
    M=[list(row) for row in R if any(row)]
    k=0
    for j in range(n):
        p=next((i for i in range(k,len(M)) if M[i][j]),None)
        if p is None:continue
        M[k],M[p]=M[p],M[k]
        for i in range(k+1,len(M)):
            while M[i][j]:
                q=M[k][j]//M[i][j]
                M[k],M[i]=M[i],[a-q*b for a,b in zip(M[k],M[i])]
        if M[k][j]<0:
            M[k]=[-x for x in M[k]]
        for i in range(k):
            q=M[i][j]//M[k][j]
            M[i]=[a-q*b for a,b in zip(M[i],M[k])]
        k+=1
    require(all(not any(row) for row in M[k:]),"nonzero rows left")
    return tuple(map(tuple,M[:k]))


def contains(R,v):
    for row in R:
        j=next(i for i,x in enumerate(row) if x)
        q,rem=divmod(v[j],row[j])
        if rem:return False
        v=tuple(a-q*b for a,b in zip(v,row))
    return not any(v)


def voltage_setup(name):
    ls,ms=tuple(map(int,name[:N])),tuple(map(int,name[N:]))
    arrows,req,seed=[],[],[]
    classes=[{i} for i in range(N)]
    rank=0

    def add(i,j,k,mirror=False):
        d=len(arrows)
        arrows.append((i,j,k,1,d if mirror else d+1))
        if not mirror:
            arrows.append((j,i,k,-1,d))

    for (i,j),m in zip(PAIRS,ms):
        if not m:continue
        a,b=(next(g for g in classes if u in g) for u in (i,j))
        if a!=b:
            classes.remove(a);classes.remove(b);classes.append(a|b)
            k=-1
        else:
            k=rank;rank+=1
        add(i,j,k)
        if m==2:
            add(i,j,rank)
            req.append(((rank,1),(k,-1)))
            rank+=1
    require(len(classes)==1,"not connected quotient")
    for i,l in enumerate(ls):
        if l==1:
            add(i,i,rank,mirror=True)
            seed.append(((rank,2),));req.append(((rank,1),))
            rank+=1
        if l==2:
            add(i,i,rank);req.append(((rank,2),));rank+=1
    def as_row(terms):
        w=[0]*rank
        for j,x in terms:
            if j>=0:w[j]+=x
        return tuple(w)
    return rank,arrows,[as_row(a) for a in req],[as_row(a) for a in seed]


def verify(name,raw):
    rank,arcs,nonzero,seed=voltage_setup(name)
    cells={tuple(map(tuple,json.loads(a))):w for a,w in raw.items()}
    require(len(cells)==len(raw) and all(row_hnf(R,rank)==R for R in cells),
            "noncanonical certificate rows")
    seen={}
    def visit(R):
        if any(contains(R,v) for v in nonzero):
            return -1
        if R in seen:
            return seen[R]
        require(R in cells,("missing child relation state",name,R))
        path=cells[R]
        require(len(path) in (4,8,16) and all(type(j) is int and 0<=j<len(arcs) for j in path),
                "malformed word")
        a=[arcs[j] for j in path]
        require(all(s[1]==t[0] and s[4]!=j for s,t,j in zip(a,a[1:]+a[:1],path[1:]+path[:1])),
                "not cyclically nonbacktracking")
        prior=[[] for _ in range(N)]
        p=[0]*rank
        for u,v,k,sgn,_ in a:
            prior[u].append(tuple(p))
            if k>=0:p[k]+=sgn
        require(contains(R,tuple(p)),"witness not closed")
        height=0
        children=set()
        for same in prior:
            for x,y in combinations(same,2):
                diff=tuple(b-a for a,b in zip(x,y))
                require(not contains(R,diff),"witness has a known collision")
                RR=row_hnf(R+(diff,),rank)
                require(RR!=R,"non-strict successor")
                children.add(RR)
        for RR in children:
            height=max(height,1+visit(RR))
        seen[R]=height
        return height
    d=visit(row_hnf(seed,rank))
    require(set(seen)==set(cells),("unused submitted rows",name))
    return len(seen),d


def check(data):
    templates=shape_enumeration()
    main=data["reduced"]
    fixed=data["extra"]
    require(set(main)==set(templates)-{K33},"quotient representatives do not match")
    require(set(fixed)==set(EXTRA),"wrong extra-edge templates")
    checked=[verify(name,table) for name,table in sorted(main.items())]
    require(sum(c for c,d in checked)==4639 and max(d for c,d in checked)==5,
            "reduced proof census")
    print("exact quotient templates:",len(templates),"labeled:",sum(templates.values()))
    print("reduced proof:",len(checked),"cases;",sum(c for c,d in checked),"states")
    ext=[verify(name,fixed[name]) for name in EXTRA]
    require([c for c,d in ext]==[10,43,7,19],"extension chart count")
    print("four extra-edge charts:",ext)
    print("PASS: every listed relation proof and all required templates")


def load_file(file):
    p=json.loads(Path(file).read_text(encoding="utf-8"))
    require(p.get("format")=="abelian-six-voltage-certificate-v1", "unknown certificate format")
    want_reduced={}
    for part in p["reduced_gzip_base64"]:
        decoded=json.loads(gzip.decompress(base64.b64decode(part,validate=True)))
        require(not (set(want_reduced)&set(decoded)),"duplicated certificate keys")
        want_reduced.update(decoded)
    return {"reduced":want_reduced,"extra":p["extra"]}


if __name__=="__main__":
    file=sys.argv[1] if len(sys.argv)>1 else Path(__file__).with_name(
        "erdos_gyarfas_general_six_orbit_certificate.json")
    check(load_file(file))
