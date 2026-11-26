#!/usr/bin/env python3
"""Exact rational lower-bound certificates for weighted graph tensors."""
import argparse
from collections import deque
from fractions import Fraction
from itertools import combinations, product
import json
from math import lcm
from pathlib import Path

SOURCE = "https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L45"

def load_graph(data):
    n = data["vertices"]
    if type(n) is not int or not 2 <= n <= 10:
        raise ValueError("vertices must be an integer from 2 to 10")
    es = list(combinations(range(n), 2))
    ix = {e:i for i,e in enumerate(es)}
    w = [Fraction(0)] * len(es)
    for a,b,x in data["edges"]:
        if type(a) is not int or type(b) is not int or not isinstance(x,(int,str)) or type(x) is bool:
            raise ValueError("edge endpoints must be integers; weight must be an integer or rational string")
        e = tuple(sorted((a,b)))
        if e not in ix:
            raise ValueError("endpoint out of range or loop")
        f = Fraction(x)
        if f <= 0:
            raise ValueError("edge weights must be positive")
        w[ix[e]] += f
    scale = lcm(*(x.denominator for x in w))
    return n, es, ix, scale, tuple(int(x*scale) for x in w)

def rectangle(vals):
    x,y,z = sorted(map(Fraction,vals),reverse=True)
    return x+y if not z else x+y+max((x+y)*z-x*y,0)**2/(4*x*y*z)

def partitions(n, groups):
    # Restricted growth strings enumerate every unlabeled set partition once.
    def rec(cur, used):
        if len(cur)==n:
            if used==groups:
                yield tuple(cur)
            return
        if used + n-len(cur) < groups:
            return
        for x in range(min(used+1,groups)):
            yield from rec(cur+[x],max(used,x+1))
    return rec([0],1)

def value(es, scale, w, part):
    sums = [0,0,0]
    slot = {(0,1):0,(0,2):1,(1,2):2}
    for (a,b),x in zip(es,w):
        if part[a]!=part[b]:
            sums[slot[tuple(sorted((part[a],part[b])))]] += x
    vals = [Fraction(x,scale) for x in sums]
    return (vals[0] if max(part)==1 else rectangle(vals)), vals

def move(w, ix, a,b,c,k):
    def index(x,y):
        return ix[tuple(sorted((x,y)))]
    x,y,z = index(a,b),index(b,c),index(a,c)
    if k<=0 or k>min(w[x],w[y]):
        raise ValueError("splicing exceeds available edge weight")
    t=list(w)
    t[x]-=k; t[y]-=k; t[z]+=k
    return tuple(t)

def best_part(es,scale,w,ps):
    return max((value(es,scale,w,p)[0],p) for p in ps)

def cert(es,sc,w,p,ops):
    v, vals = value(es,sc,w,p)
    return {"exponent":str(v),"partition":list(p),"splices":ops,
            "crossing_weights":list(map(str,vals)),
            "depends_on_rectangular_theorem":max(p)==2 and min(vals)>0}

def solve(data, depth=1, states=120, max_units=4):
    n,es,ix,sc,w0=load_graph(data)
    cuts=list(partitions(n,2))
    tris=list(partitions(n,3))
    x,p=best_part(es,sc,w0,cuts)
    cut=cert(es,sc,w0,p,[])
    direct=cut
    if tris:
        y,p=best_part(es,sc,w0,tris)
        # Prefer an unconditional cut on ties.
        if y>x:
            direct=cert(es,sc,w0,p,[])
    best=direct
    queue=deque([(w0,[])])
    seen={w0}
    truncated=False
    while queue:
        w,ops=queue.popleft()
        if len(ops)>=depth:
            continue
        for b in range(n):
            for a,c in combinations((i for i in range(n) if i!=b),2):
                m=min(w[ix[tuple(sorted((a,b)))]],w[ix[tuple(sorted((b,c)))]])
                if not m:
                    continue
                for k in sorted({m,*range(1,min(m,max_units)+1)}):
                    t=move(w,ix,a,b,c,k)
                    if t in seen:continue
                    if len(seen)>=states:
                        truncated=True
                        continue
                    seen.add(t)
                    new=ops+[[a,b,c,str(Fraction(k,sc))]]
                    v,p=best_part(es,sc,t,cuts+tris)
                    if v>Fraction(best["exponent"]):
                        best=cert(es,sc,t,p,new)
                    queue.append((t,new))
    return {"max_cut":cut,"direct_partition_lower_bound":direct,"combined_lower_bound":best,
            "search":{"visited":len(seen),"depth":depth,"state_limit_hit":truncated,
                      "tested_splice_amounts":"first grid units up to limit, and bottleneck",
                      "grid_unit":str(Fraction(1,sc)),"grid_units_limit":max_units},
            "rectangular_source":SOURCE}

def verify(data, c):
    n,es,ix,sc,w=load_graph(data)
    p=c["partition"]
    if len(p)!=n or any(type(g) is not int for g in p) or set(p) not in ({0,1},{0,1,2}):
        raise ValueError("must give a proper 2- or 3-part partition")
    for a,b,d,weight in c["splices"]:
        if any(type(x) is not int or not 0<=x<n for x in (a,b,d)) or len({a,b,d})!=3:
            raise ValueError("invalid splice vertices")
        if type(weight) is not str or str(Fraction(weight))!=weight:
            raise ValueError("splice weight must be a canonical rational string")
        k=Fraction(weight)*sc
        if k.denominator!=1:
            raise ValueError("splice is outside the declared rational grid")
        w=move(w,ix,a,b,d,int(k))
    replay=cert(es,sc,w,p,c["splices"])
    if replay!=c:
        raise ValueError("claimed certificate does not replay")
    return replay

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    sub=ap.add_subparsers(dest="cmd",required=True)
    s=sub.add_parser("search"); s.add_argument("graph",type=Path)
    s.add_argument("--depth",type=int,default=1);s.add_argument("--states",type=int,default=120)
    s.add_argument("--grid-units",type=int,default=4)
    v=sub.add_parser("verify");v.add_argument("graph",type=Path);v.add_argument("certificate",type=Path)
    args=ap.parse_args()
    try:
        g=json.loads(args.graph.read_text())
        if args.cmd=="search":
            if not 0<=args.depth<=4 or not 1<=args.states<=2000 or not 0<=args.grid_units<=20:
                raise ValueError("search limits out of range")
            obj=solve(g,args.depth,args.states,args.grid_units)
        else:
            doc=json.loads(args.certificate.read_text())
            obj={"replayed":verify(g,doc.get("combined_lower_bound",doc))}
        print(json.dumps(obj,indent=2))
    except (ValueError,TypeError,KeyError,ZeroDivisionError,OSError) as e:
        ap.exit(2,"error: "+str(e)+"\n")

if __name__=="__main__":
    main()
