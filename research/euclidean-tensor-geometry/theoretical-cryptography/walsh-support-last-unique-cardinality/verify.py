#!/usr/bin/env python3
"""Walsh-support certificates, with optional upstream catalogue replay."""

from collections import Counter
from itertools import combinations
from math import prod
from pathlib import Path
import argparse
import hashlib
import json
import re

BASE = Path(__file__).resolve().parent
SMALL = (1,4,8,10,13,16,18,20)
EXPECTED = {
    (4,8): ((1,1),),
    (4,10): ((3,1),),
    (8,8): ((4,3),(5,1)),
    (8,10): ((5,5),(6,3),(7,1)),
    (8,13): ((7,7),(8,5)),
    (10,10): ((7,5),(8,3),(9,1)),
    (10,13): ((9,7),(10,5)),
    (13,13): ((11,9),(12,7),(13,5)),
    (13,16): ((13,11),),
    (16,16): ((15,13),(16,11)),
    (16,18): ((16,15),),
    (18,18): ((17,17),(18,15)),
}


def check(flag, msg):
    if not flag:
        raise ValueError(msg)


def walsh(table, n):
    a = [1-2*((table>>i)&1) for i in range(1<<n)]
    h=1
    while h<len(a):
        for base in range(0,len(a),2*h):
            for j in range(base,base+h):
                u,v=a[j],a[j+h]
                a[j],a[j+h]=u+v,u-v
        h *= 2
    return a


def walsh_direct(table,n):
    return [sum((-1)**(((table>>i)&1) ^ ((i&j).bit_count()&1))
                for i in range(1<<n)) for j in range(1<<n)]


def affdim(S):
    basis={}
    a=S[0]
    for k in S:
        u=a^k
        while u:
            j=u.bit_length()-1
            if j not in basis:
                basis[j]=u
                break
            u ^= basis[j]
    return len(basis)


def energy(S):
    by_diff=Counter(x^y for x,y in combinations(S,2))
    return sum(t*(t-1)//2 for t in by_diff.values())


def alternate(S):
    V={0}
    for q in S:
        V|={u^q^S[0] for u in V}
    points=set(S)
    foursets=sum((d:=(a^b^c))>c and d in points for a,b,c in combinations(S,3))
    return len(V).bit_length()-1, 3*foursets


def score(n,h):
    check(type(n)==int and 2<=n<=7,"unexpected dimension")
    check(type(h)==str and len(h)==1<<(n-2) and re.fullmatch('[0-9a-f]+',h),"bad truth table")
    z=int(h,16)
    W=walsh(z,n)
    S=[i for i,a in enumerate(W) if a]
    return W,S


def finite_certificate(data, verbose=False):
    check(set(data)=={str(r) for r in range(22,87)},"uncovered size in certificate")
    independent=0
    for r in range(22,87):
        flags=[]
        rows=data[str(r)]
        check(len(rows)==2,"wrong number of witnesses")
        for n,h,dim,E in rows:
            W,S=score(n,h)
            check(len(S)==r,"wrong support cardinality")
            check((affdim(S),energy(S))==(dim,E),"wrong support invariants")
            check(W==walsh_direct(int(h,16),n),"independent Walsh check")
            check(alternate(S)==(dim,E),"independent affine invariant check")
            independent+=1
            flags.append((dim,E))
        check(flags[0]!=flags[1],"certified witnesses do not separate the shape")
    both=sum(a[2]!=b[2] and a[3]!=b[3] for a,b in data.values())
    if verbose:
        print(f"PASS {both} sizes differ in both invariants.")
        print("PASS 65 sizes 22..86, 130 truth tables and invariant pairs.")
        print(f"PASS {independent} direct Fourier/4-set cross-checks.")


def check_join():
    possible = {}
    ruled_out = []
    full = []
    for s,t in combinations_with_self(SMALL+(21,)):
        for k in range(s+1):
            xi=2*(s+t)-2*k-21
            if not 0<=xi<=k:
                continue
            full.append((s,t,k,xi))
            # JM Lemma 1: unequal sizes cannot match all of the smaller;
            # equal common support cannot have exactly one unequal modulus.
            if (s<t and xi==s) or (s==t==k and xi==k-1):
                ruled_out.append((s,t,k,xi))
                continue
            if t==21:
                check((s,t,k,xi)==(21,21,21,21),"unlisted size-21 case")
                continue
            possible.setdefault((s,t),[]).append((k,xi))
    check(len(full)==25 and ruled_out==[(20,20,20,19)],"bad prefilter count")
    check({p:tuple(x) for p,x in possible.items()}==EXPECTED,"incomplete join table")
    dims={4:2,8:3,10:4,13:5,18:5}
    specials={(13,13),(13,16),(16,16),(16,18)}
    for (s,t),settings in possible.items():
        if (s,t) not in specials:
            for k,_ in settings:
                check(dims[s]+dims[t]-(k-1).bit_length()+1<=6,"bad dimension bound")
    print("PASS all 25 arithmetic join tuples: 23 proper survive, 1 excluded by Parseval, 1 same-size.")


def combinations_with_self(xs):
    for j,x in enumerate(xs):
        for y in xs[j:]:
            yield x,y


def records(path, expected_bytes, expected_hash):
    raw=path.read_bytes()
    check(len(raw)==expected_bytes and hashlib.sha256(raw).hexdigest()==expected_hash,
          "unrecognized catalogue bytes; consult UPSTREAM.md")
    first=None
    for line in raw.decode("ascii").splitlines():
        if line.startswith("hdr="):
            check(first is None,"record without stabilizer")
            first=line[4:]
        if line.startswith("fix="):
            check(first is not None,"stabilizer without record")
            yield first,int(line[4:])
            first=None
    check(first is None,"truncated final record")


def truth_from_anf(desc):
    table=0
    if desc!="0":
        for name in desc.split("+"):
            check(re.fullmatch("[a-f]{2,6}",name) and len(set(name))==len(name),
                  "invalid ANF term in catalogue")
            letters=sum(1<<(ord(c)-97) for c in name)
            table ^= TRUTH[letters]
    return table


TRUTH=[sum(1<<u for u in range(64) if (u & a)==a) for a in range(64)]


def catalogue_scan(path, metadata):
    group=64*prod(64-(1<<i) for i in range(6))
    weighted=0
    cases={18:[],21:[]}
    for i,(anf,fix) in enumerate(records(path,metadata["bytes"],metadata["sha256"]),1):
        check(group%fix==0,"bad catalogue stabilizer")
        weighted+=group//fix
        tt=truth_from_anf(anf)
        w=walsh(tt,6)
        S=[j for j,f in enumerate(w) if f]
        if len(S) in cases:
            check(w==walsh_direct(tt,6),"catalogue hit independently disagreed")
            cases[len(S)].append([i,anf,tt,affdim(S),sorted(Counter(map(abs,w)).items())])
    check(i==150357 and weighted==1<<57,"catalogue count or orbit sum mismatch")
    check(all(len(a)==1 and a[0][3]==5 for a in cases.values()),"catalogue hit count or dimension")
    check(next(iter(cases[18]))[4] == [(0,46),(8,14),(24,2),(32,2)],
          "incorrect size-18 amplitude levels")
    print(f"PASS catalogue n=6: {i} representatives; orbit total {weighted}.")
    for size in (18,21):
        ordinal,anf,tt,dim,heights=cases[size][0]
        print(f"size {size}: catalogue record {ordinal}, ANF {anf}, "
              f"truth {tt:016x}, support span {dim}, absolute Walsh {heights}.")
        if size==21:
            print("size 21 support:", [u for u,a in enumerate(walsh_direct(tt,6)) if a])


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--catalogue", type=Path, help="master byte-exact Langevin file")
    a=p.parse_args()
    data=json.loads((BASE/"witnesses.json").read_text())
    finite_certificate(data,True)
    check_join()
    bad=json.loads(json.dumps(data))
    bad["22"][1]=bad["22"][0]
    try:
        finite_certificate(bad)
    except ValueError as err:
        check(str(err)=="certified witnesses do not separate the shape", "wrong negative-control failure")
        print("PASS negative control: duplicate same-shape witness rejected.")
    else:
        raise ValueError("negative control was accepted")
    if a.catalogue:
        metadata=json.loads((BASE/"upstream.json").read_text())
        catalogue_scan(a.catalogue,metadata)
    else:
        print("Upstream catalogue scan skipped; use --catalogue for a full replay.")

if __name__=="__main__":
    main()
