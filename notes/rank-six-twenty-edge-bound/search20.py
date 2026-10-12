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
    ap.add_argument("--root-flower",action="store_true",
                    help="normalize six necessary private neighbours of edge zero")
    ap.add_argument("--label-precedence",action="store_true",
                    help="labels appear in increasing order within each part")
    ap.add_argument("--private-neighbours",action="store_true",
                    help="every edge has a singleton-intersection neighbour in each part")
    ap.add_argument("--edge-critical",action="store_true",
                    help="for N=20, encode a disjoint five-cover after deleting each edge")
    a=ap.parse_args();n=a.edges;q=a.vertices_per_part
    if n<2 or q<6 or a.seconds<=0:
        ap.error('need at least two edges, six available vertices per part, and positive time')
    if a.root_flower and n<7:
        ap.error('the normalized root flower requires at least seven labeled edges')
    if a.edge_critical and n!=20:
        ap.error('edge-critical encoding currently uses the proved N=20 minimum-edge case')
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
    if a.root_flower:
        for r,c in itertools.product(range(6),range(6)):
            clauses.append([x(r+1,c,0)] if c==r else [-x(r+1,c,0)])
        # Row one contains the first nonzero label in parts one through five;
        # row two contains the first nonzero label in part zero.
        for c in range(1,6):clauses.append([x(1,c,1)])
        clauses.append([x(2,0,1)])
    if a.label_precedence:
        for i,c,v in itertools.product(range(n),range(6),range(2,q)):
            clauses.append([-x(i,c,v)]+[x(j,c,v-1) for j in range(i)])
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
    if a.private_neighbours:
        for i,c in itertools.product(range(n),range(6)):
            private=[]
            for j in range(n):
                if i==j:continue
                z=pool.id(("private",i,j,c));private.append(z)
                lo,hi=sorted((i,j))
                literals=[pool.id(("eq",lo,hi,c))]+[
                    -pool.id(("eq",lo,hi,d)) for d in range(6) if d!=c]
                for lit in literals:clauses.append([-z,lit])
                clauses.append([z]+[-lit for lit in literals])
            clauses.append(private)
    if a.edge_critical:
        for i in range(n):
            chosen=[pool.id(("critical-cover",i,c,v)) for c in range(6) for v in range(q)]
            clauses+=CardEnc.equals(chosen,5,vpool=pool,encoding=EncType.seqcounter).clauses
            for c,v in itertools.product(range(6),range(q)):
                y=pool.id(("critical-cover",i,c,v))
                clauses.append([-y,-x(i,c,v)])
            for j in range(n):
                if i==j:continue
                hits=[]
                for c,v in itertools.product(range(6),range(q)):
                    y=pool.id(("critical-cover",i,c,v))
                    z=pool.id(("critical-hit",i,j,c,v));hits.append(z)
                    clauses.extend([[-z,y],[-z,x(j,c,v)],[-y,-x(j,c,v),z]])
                clauses.append(hits)
    # Complete next-case restrictions from Input F and the twenty-edge proof.
    if n!=20 or q!=8:
        ap.error('this scratch scout uses exactly N=20, q=8')
    for c,v in itertools.product(range(6),range(q)):
        rows=[x(i,c,v) for i in range(n)]
        clauses+=CardEnc.atmost(rows,7,vpool=pool,encoding=EncType.seqcounter).clauses
        active=pool.id(("active",c,v))
        clauses.append([-active]+rows)
        for lit in rows:clauses.append([-lit,active])
        lower=CardEnc.atleast(rows,2,vpool=pool,encoding=EncType.seqcounter).clauses
        clauses.extend([[-active]+clause for clause in lower])
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
            rows=[tuple(next(v for v in range(q) if x(i,c,v) in positive)
                        for c in range(6)) for i in range(n)]
            if a.edge_critical:
                for i,row in enumerate(rows):
                    chosen={(c,v) for c in range(6) for v in range(q)
                            if pool.id(("critical-cover",i,c,v)) in positive}
                    if len(chosen)!=5 or any((c,v) in chosen for c,v in enumerate(row)):
                        raise RuntimeError('critical-cover encoding discrepancy')
                    if any(not any((c,v) in chosen for c,v in enumerate(other))
                           for j,other in enumerate(rows) if i!=j):
                        raise RuntimeError('critical-cover does not cover the remaining edges')
            edges=sorted(set(rows))
            if a.private_neighbours:
                for e,c in itertools.product(edges,range(6)):
                    if not any([d for d in range(6) if e[d]==f[d]]==[c] for f in edges):
                        raise RuntimeError('private-neighbour encoding discrepancy')
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
