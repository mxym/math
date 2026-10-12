#!/usr/bin/env python3
"""Independent exact replay using edge sets, span enumeration and state amplitudes.

This program imports neither the generator nor the other checker. It verifies
coverage independently, enumerates each small LC orbit afresh, and computes
cut ranks by enumerating binary row spans rather than Gaussian elimination.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from itertools import combinations, product
import json
from pathlib import Path


def check(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def edge(u: int, v: int) -> tuple[int, int]:
    return min(u, v), max(u, v)


def representatives() -> dict[int, frozenset[tuple[int, int]]]:
    return {
        1: frozenset(),
        2: frozenset({(0,1)}),
        3: frozenset({(0,1),(1,2)}),
        4: frozenset({(0,1),(1,2),(2,3)}),
        5: frozenset({(0,1),(1,2),(2,3),(3,4),(0,4)}),
        6: frozenset({(0,1),(1,2),(2,3),(3,4),(0,4),
                      (0,5),(1,5),(2,5),(3,5),(4,5)}),
    }


def decode(a: object, n: int) -> frozenset[tuple[int, int]]:
    check(isinstance(a, list) and len(a)==n and all(type(x) is int and 0<=x<2**n for x in a), "malformed row encoding")
    check(all(not(a[i] & 2**i) for i in range(n)), "loop")
    out=set()
    for i,j in combinations(range(n),2):
        x,y = bool(a[i]&2**j),bool(a[j]&2**i)
        check(x==y, "asymmetric matrix")
        if x:out.add((i,j))
    return frozenset(out)


def lc(e: frozenset[tuple[int,int]], v: int, n: int) -> frozenset[tuple[int,int]]:
    check(type(v) is int and 0<=v<n, "LC label outside graph")
    neighbors=[w for w in range(n) if w!=v and edge(w,v) in e]
    return e.symmetric_difference(frozenset(edge(a,b) for a,b in combinations(neighbors,2)))


def claw_on(e: frozenset[tuple[int,int]], labels: object, n: int) -> bool:
    if not isinstance(labels,list) or len(labels)!=4 or not all(type(v) is int and 0<=v<n for v in labels) or len(set(labels))!=4:
        return False
    c,*leaves=labels
    desired={edge(c,u) for u in leaves}
    actual={edge(u,v) for u,v in combinations(labels,2) if edge(u,v) in e}
    return actual==desired


def any_claw(e: frozenset[tuple[int,int]], n: int) -> bool:
    return any(claw_on(e,[v,*triple],n) for v in range(n)
               for triple in combinations([w for w in range(n) if w!=v],3))


def orbit(root: frozenset[tuple[int,int]], n: int) -> set[frozenset[tuple[int,int]]]:
    reached={root};queue=deque([root])
    while queue:
        e=queue.popleft()
        check(not any_claw(e,n), "negative representative reaches a claw")
        for v in range(n):
            h=lc(e,v,n)
            if h not in reached:reached.add(h);queue.append(h)
    return reached


def span_cut_rank(e: frozenset[tuple[int,int]], n: int, a: frozenset[int]) -> int:
    outside=[i for i in range(n) if i not in a]
    span={tuple(0 for _ in outside)}
    for u in sorted(a):
        row=tuple(int(edge(u,v) in e) for v in outside)
        span |= {tuple(x^y for x,y in zip(w,row)) for w in tuple(span)}
    size=len(span)
    check(size>0 and size&(size-1)==0, "span size not a power of two")
    return size.bit_length()-1


def direct_density_check(e: frozenset[tuple[int,int]], n: int, a: frozenset[int], r: int) -> None:
    # Direct integer numerator M of rho_A=M/2^n. Rows are computational basis
    # amplitudes without their common 2^(-n/2) normalization.
    left=sorted(a);right=[i for i in range(n) if i not in a]
    amplitudes=[]
    for x in product((0,1),repeat=len(left)):
        row=[]
        for y in product((0,1),repeat=len(right)):
            bits=dict(zip(left,x));bits.update(zip(right,y))
            phase=sum(bits[u]*bits[v] for u,v in e)%2
            row.append(1-2*phase)
        amplitudes.append(row)
    m=[[sum(x*y for x,y in zip(row,col)) for col in amplitudes] for row in amplitudes]
    d=len(m)
    check(sum(m[i][i] for i in range(d))==2**n, "density trace numerator")
    # Positive semidefiniteness is by M=TT^T. M^2=2^(n-r) M forces all
    # nonzero normalized eigenvalues to be 2^(-r), with multiplicity 2^r.
    factor=2**(n-r)
    for i in range(d):
        for j in range(d):
            check(sum(m[i][k]*m[k][j] for k in range(d))==factor*m[i][j], "density polynomial identity failed")


def verify(cert: dict, direct_quantum: bool = True) -> dict:
    check(cert.get("format")=="lc-claw-free-extensions-v1", "format")
    reps=representatives()
    check(set(cert["representatives"])=={str(n) for n in reps}, "representative coverage")
    check(set(cert["closed_claw_free_orbits"])=={str(n) for n in reps}, "orbit coverage")
    for n,e in reps.items():check(decode(cert["representatives"][str(n)],n)==e, "wrong representative")
    indexed={}
    for w in cert["extensions"]:
        key=(w["base_order"],w["attachment"])
        check(all(type(x) is int for x in key) and key not in indexed,"duplicate or noninteger extension key")
        indexed[key]=w
    cases=0;outcomes=Counter();max_steps=0
    for n,root in reps.items():
        # Coverage is generated from subsets, independently of the generator's mask loop.
        for size in range(1,n+1):
            for attachment in combinations(range(n),size):
                mask=sum(2**v for v in attachment)
                key=(n,mask)
                check(key in indexed,"missing nonempty attachment subset")
                w=indexed.pop(key)
                e=root | frozenset((v,n) for v in attachment)
                check(isinstance(w["lc"],list),"LC list")
                for v in w["lc"]:e=lc(e,v,n+1)
                max_steps=max(max_steps,len(w["lc"]))
                if w["kind"]=="claw":check(claw_on(e,w["claw"],n+1),"invalid claw certificate")
                elif w["kind"]=="representative":
                    check(n+1 in reps,"bad target order")
                    p=w["order"]
                    check(isinstance(p,list) and all(type(v) is int for v in p) and sorted(p)==list(range(n+1)),"bad permutation")
                    target=frozenset(edge(p[i],p[j]) for i,j in reps[n+1])
                    check(e==target,"endpoint is not claimed representative")
                else:raise RuntimeError("unknown endpoint")
                outcomes[w["kind"]]+=1;cases+=1
    check(not indexed,"extra extension cases")
    check(max_steps<=3,"LC length bound")
    orbit_sizes={};histograms={};assignments=0;direct_cuts=0
    for n,root in reps.items():
        found=orbit(root,n)
        supplied=[decode(a,n) for a in cert["closed_claw_free_orbits"][str(n)]]
        check(len(set(supplied))==len(supplied) and set(supplied)==found,"independent orbit mismatch")
        orbit_sizes[n]=len(found)
        subsets=[frozenset(s) for size in range(n+1) for s in combinations(range(n),size)]
        entropies={a:span_cut_rank(root,n,a) for a in subsets}
        if direct_quantum:
            for a,r in entropies.items():direct_density_check(root,n,a,r);direct_cuts+=1
        hist=Counter()
        for colors in product(range(4),repeat=n):
            parts=[frozenset(i for i,c in enumerate(colors) if c==j) for j in range(4)]
            a,b,c,d=parts
            val=entropies[a]+entropies[b]+entropies[c]-entropies[a|b]-entropies[a|c]-entropies[b|c]+entropies[a|b|c]
            sizes=sorted(map(len,parts))
            prediction=0
            if sizes[0]>0:
                if n in (4,5):prediction=-1
                elif sizes==[1,1,2,2]:prediction=-2
            check(val==prediction and val<=0,"MMI/formula failure")
            hist[val]+=1;assignments+=1
        histograms[n]=dict(sorted(hist.items()))
    return {"status":"PASS","checker":"edge-sets-span-enumeration-direct-state",
            "extension_cases":cases,"extension_outcomes":dict(outcomes),"maximum_lc_length":max_steps,
            "independently_generated_orbit_sizes":orbit_sizes,
            "all_four_label_assignments":assignments,"direct_density_cuts":direct_cuts,
            "i3_histograms":histograms}


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate",nargs="?",type=Path,default=Path(__file__).with_name("certificate.json"))
    ap.add_argument("--output",type=Path)
    ap.add_argument("--skip-direct-density",action="store_true",help="omit the optional finite amplitude diagnostic")
    args=ap.parse_args()
    result=verify(json.loads(args.certificate.read_text(encoding="utf-8")),not args.skip_direct_density)
    text=json.dumps(result,indent=2)+"\n"
    if args.output:args.output.write_text(text,encoding="utf-8")
    print(text,end="")

if __name__=="__main__":main()
