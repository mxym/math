"""Check the point diagrams and their clean cells when no line is saturated."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations
from pathlib import Path
import gzip
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from covered_grid_choice import CATALOGUE, EXCEPTION, has_obstruction
from covered_spread import PAIRS, check_leaf, row_system

BORDER=733002486440
FOURTEEN=710436620800
SURVIVORS={389074212160,389074278760,727628534440,727633208960,BORDER,
           EXCEPTION,1557099336360,2920672502100,2931409920340}
TARGET=(4,1)
SMALL=(1,1)


def arcs(code):
    result=[]
    for j,(p,q) in enumerate(PAIRS):
        v=(code>>(2*j))&3
        assert v!=3
        if v:result.append((p,q) if v==1 else (q,p))
    return result


def signature(edges):
    targets=[{b for a,b in edges if a==p} for p in range(7)]
    types=[(6-len(targets[p]),6-sum(p in e for e in edges)) for p in range(7)]
    return targets,types


def low_degree():
    original,_=signature(arcs(FOURTEEN))
    copies={tuple(tuple(sorted(perm[q] for q in original[perm.index(p)])) for p in range(7))
            for perm in permutations(range(7))}
    viable=0
    for degrees in combinations_with_replacement((0,2,3,4),7):
        if sum(degrees)!=14:continue
        targets=[]
        def visit(p,remaining):
            nonlocal viable
            if p==7:
                assert not any(remaining)
                if not has_obstruction(targets):
                    assert tuple(targets) in copies
                    viable+=1
                return
            heads=[q for q in range(7) if remaining[q] and q!=p
                   and (q>=p or p not in targets[q])]
            for pair in combinations(heads,2):
                new=[v-int(q in pair) for q,v in enumerate(remaining)]
                if any(v>6-p-int(q>p) for q,v in enumerate(new)):continue
                targets.append(pair)
                visit(p+1,new)
                targets.pop()
        visit(0,degrees)
    assert viable>0


def check_types(code):
    edges=arcs(code)
    out,types=signature(edges)
    if code==EXCEPTION:
        assert types.count(SMALL)==2 and types.count(TARGET)==0
    elif code==BORDER:
        assert types.count(SMALL)==1 and types.count(TARGET)==4
    else:
        assert SMALL not in types and types.count(TARGET)>=2
    for p,q in combinations(range(7),2):
        if q in out[p] or p in out[q]:continue
        if TARGET in (types[p],types[q]):
            assert types[p]==types[q]==TARGET and out[p]==out[q] and len(out[p])==2


def main():
    low_degree()
    proofs={}
    for path in (HERE.parent/'covered-grid-choice-cert.json.gz', HERE/'line-density.json.gz'):
        with gzip.open(path,'rt') as f:
            for k,v in json.load(f).items():
                code=int(k)
                if code==EXCEPTION:continue
                assert code not in proofs
                proofs[code]=v
    seen=set()
    with gzip.open(CATALOGUE,'rt') as f:
        for line in f:
            code=int(line.split(' ',1)[0])
            edges=arcs(code)
            if len(edges)==21 or any(t==6 for t,g in signature(edges)[1]):continue
            if code in SURVIVORS:
                seen.add(code)
            else:
                matrix,rhs,owner,_=row_system(edges)
                check_leaf(matrix,rhs,owner,proofs.pop(code))
    assert seen==SURVIVORS and not proofs
    for code in SURVIVORS|{FOURTEEN}:check_types(code)
    # Each small-line grid with exceptional points contains a*b such points
    # and has a(3-b)+b(3-a) distinct border points. A border point contributes
    # to at most one of these grids.
    for a in range(1,4):
        for b in range(1,4):
            if a*b!=9:assert a*b<=2*(a*(3-b)+b*(3-a))
    for e in range(100):
        for b in range(100-e):
            if e<=2*b:assert 4*b+2*(99-b-e)>=132
    print('Verified ten remaining diagrams, target-grid closure, and at least eight target grids.')


if __name__=='__main__':main()
