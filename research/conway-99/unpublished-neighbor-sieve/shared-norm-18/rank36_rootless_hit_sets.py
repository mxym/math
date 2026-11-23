"""Replay 39 rank-36 hitting proofs with exact integer multipliers."""
from itertools import combinations
import json
from pathlib import Path
from rank36_four_hit_sets import engine, P

def check():
    R,C,D,o=engine()
    assert P==2402
    names={str(k):(v,set()) for k,v in R.items()}
    for k,v in D.items():
        names[str(('abs',k))]=([-x for x in v],{k})
    def row(const, terms):
        return [const*x+sum(P*z*D[k][i] for z,k in terms) for i,x in enumerate(o)]
    names.update({
        'zeroN':([-x for x in R['N']],set()),
        'squarecap':(row(5544,[(3,(1,27)),(-2,(2,26)),(-3,(0,16))]),set()),
        'u121cap':(row(29372,[(-1,(1,21))]),set()),
        'bothabs':(row(12320,[(-1,(0,18))]),{(0,16),(0,20)}),
        'no20N16':(row(6496,[(-1,(0,16))]),{(0,20)})})
    data=json.loads(Path(__file__).with_name('rank36-rootless-hit-sets.json').read_text())
    labels=data['labels']; assert len(labels)==len(set(labels)) and set(labels)<=set(names)
    hits=[]
    for h,d,terms in data['proof']:
        h=frozenset(tuple(k) for k in h);den=int(d)
        assert h<=set(D) and h not in hits and len(terms)==len(dict(terms)) and den>0
        used=set();lhs=[0]*len(o)
        for i,y in terms:
            c=int(y); assert 0<=i<len(labels) and c>0
            v,deps=names[labels[i]];used.update(deps)
            lhs=[a+c*b for a,b in zip(lhs,v)]
        assert used==h and lhs==[-den*a for a in o]
        hits.append(h)
    assert len(hits)==39 and not any(x<y for x in hits for y in hits)
    def accept(s):
        return all(h&s for h in hits) and ((0,16) not in s or (1,27) in s)
    allowed=[[set(q) for q in combinations(sorted(D),k) if accept(set(q))] for k in range(13)]
    counts=list(map(len,allowed))
    assert counts==[0,0,0,0,8,76,242,375,326,171,56,11,1]
    norm18free=[s for s in allowed[4] if (0,18) not in s]
    assert norm18free==[{(0,20),(0,26),(1,25),(2,28)}]
    print('39 exact rank-36 hitting sets. Necessary supports per size:', counts)
    print('Only N18-free support of size four surviving this filter:',sorted(norm18free[0]))

if __name__=='__main__':check()
