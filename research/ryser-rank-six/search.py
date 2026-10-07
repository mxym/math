"""Bounded exploratory search, never a proof of nonexistence."""
import argparse
import itertools
import json
import math
from pathlib import Path
import time
from threading import Timer


def cover_at_most(edges, k=5, width=6):
    n=len(edges); masks=[0]*(6*width)
    for i,e in enumerate(edges):
        for c,v in enumerate(e):
            masks[width*c+v] |= 1<<i
    failed=set()
    def rec(left,k):
        if not left:return []
        if not k:return None
        key=(left,k)
        if key in failed:return None
        covers=[(v,m & left) for v,m in enumerate(masks) if m & left]
        if max(m.bit_count() for _,m in covers)*k<left.bit_count():
            return None
        first=(left & -left).bit_length()-1
        opts=sorted((v for v,m in covers if (m>>first)&1),
                    key=lambda v:(masks[v]&left).bit_count(),reverse=True)
        for v in opts:
            ans=rec(left & ~masks[v],k-1)
            if ans is not None:return [v]+ans
        failed.add(key)
        return None
    return rec((1<<n)-1,k),masks


def main():
    from pysat.formula import IDPool
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver
    ap=argparse.ArgumentParser()
    ap.add_argument("--edges",type=int,default=24)
    ap.add_argument("--vertices-per-part",type=int,default=6)
    ap.add_argument("--seconds",type=int,default=240)
    ap.add_argument("--output",default="candidate.json")
    a=ap.parse_args();n=a.edges;q=a.vertices_per_part
    if n<2 or q<6 or a.seconds<=0:
        ap.error('need at least two edges, six available vertices per part, and positive time')
    pool=IDPool();clauses=[]
    x=lambda i,c,v:pool.id(("x",i,c,v))
    for i,c in itertools.product(range(n),range(6)):
        clauses+=CardEnc.equals([x(i,c,v) for v in range(q)],1,vpool=pool,
                               encoding=EncType.seqcounter).clauses
    for c,v in itertools.product(range(6),range(6)):
        clauses.append([x(i,c,v) for i in range(n)])
    for c in range(6):clauses.append([x(0,c,0)])
    clauses.append([x(1,0,0)])
    for c in range(1,6):
        for v in range(2,q):clauses.append([-x(1,c,v)])
    clauses.append([x(1,c,1) for c in range(1,6)])
    for i in range(n):
        for j in range(i+1,n):
            qs=[]
            for c in range(6):
                shared=pool.id(("eq",i,j,c));qs.append(shared)
                for v in range(q):
                    clauses.append([-x(i,c,v),-x(j,c,v),shared])
                    clauses.append([-shared,-x(i,c,v),x(j,c,v)])
                    clauses.append([-shared,-x(j,c,v),x(i,c,v)])
            clauses.append(qs)
    start=time.monotonic();models=0;cuts=set()
    with Solver(name="g4",bootstrap_with=clauses) as solver:
        while time.monotonic()-start<a.seconds:
            timer=Timer(min(20,a.seconds-(time.monotonic()-start)),solver.interrupt)
            timer.start()
            sat=solver.solve_limited(expect_interrupt=True)
            timer.cancel();solver.clear_interrupt()
            if sat is None:continue
            if not sat:
                print("Bounded encoding exhausted; no global nonexistence conclusion.",flush=True)
                break
            positive={v for v in solver.get_model() if v>0}
            edges=sorted(set(tuple(next(v for v in range(q) if x(i,c,v) in positive)
                                   for c in range(6)) for i in range(n)))
            models+=1
            cover,masks=cover_at_most(edges,width=q)
            if cover is None:
                # Independent complete five-vertex enumeration.
                full=(1<<len(edges))-1
                for subset in itertools.combinations(range(6*q),5):
                    total=0
                    for v in subset:total |= masks[v]
                    if total==full:raise RuntimeError("cover oracle discrepancy")
                if not all(any(u==v for u,v in zip(e,f))
                           for e,f in itertools.combinations(edges,2)):
                    raise RuntimeError("intersection encoding discrepancy")
                Path(a.output).write_text(json.dumps(
                    {"edges":edges,"vertex_bound":q,"cover_number":6,
                     "checked_five_vertex_sets":math.comb(6*q,5)},
                    indent=2)+"\n")
                print("EXACTLY CHECKED CANDIDATE SAVED",flush=True)
                return
            cover=sorted(set(cover))
            cover+=list(v for v in range(6*q) if v not in cover)[:5-len(cover)]
            key=tuple(sorted(cover))
            if key in cuts:raise RuntimeError("cut did not exclude its cover")
            cuts.add(key)
            avoid=[]
            for i in range(n):
                z=pool.id(("avoid",len(cuts),i));avoid.append(z)
                literals=[-x(i,v//q,v%q) for v in key]
                for lit in literals:solver.add_clause([-z,lit])
                solver.add_clause([z]+[-lit for lit in literals])
            solver.add_clause(avoid)
            if models%25==0:
                print(f"{models} models; {len(cuts)} exact cover cuts; "
                      f"{time.monotonic()-start:.1f}s",flush=True)
    print(f"Search ended: {models} models, no checked counterexample; "
          "bounded exploratory outcome only.",flush=True)


if __name__=="__main__":
    main()
