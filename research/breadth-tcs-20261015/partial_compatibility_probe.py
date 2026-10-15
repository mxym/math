"""Finite partial VC-one subcomplex probes inside VC-two total classes.

This is a control of proposed intermediate lemmas. It does not change SC0
into a partial-class problem and no partial UNSAT would refute total SC0.
"""
from pathlib import Path
from itertools import combinations
import json
import random
import time
from finite_decoder import samples, vcdim
from finite_cegis import maximal_class
from ambiguity_probe import solve_partial
from resumed_controls import WARMUTH

HERE=Path(__file__).parent

def main():
    rng=random.Random(15102026)
    records=[]; tested=0; start=time.monotonic()
    for n,C in [(5,WARMUTH),(6,maximal_class(6,2,41)),
                (7,maximal_class(7,2,41))]:
        S=samples(n,C)
        pairs=[sum(1<<i for i in A) for A in combinations(range(n),2)]
        pair_patterns={a:[b for b in range(1<<n) if not(b&~a)] for a in pairs}
        natural={a:({c&a for c in C}) for a in pairs}
        for run in range(3000):
            forbidden=[]
            for a in pairs:
                absent=[b for b in pair_patterns[a] if b not in natural[a]]
                b=rng.choice(absent or pair_patterns[a])
                forbidden.append((a,b))
            P={s for s in S if not any(not(a&~s[0]) and (s[1]&a)==b for a,b in forbidden)}
            result=solve_partial(n,P,timeout=3000)
            result.update({'parent_n':n,'parent_VC':vcdim(n,C),'run':run,
                           'forbidden_pair_patterns':forbidden,
                           'max_face_size':max(a.bit_count() for a,b in P)})
            records.append(result); tested+=1
            if result['result']!='sat':
                result.update({'parent_C':sorted(C),'P':[list(s) for s in sorted(P)],
                               'status':'Restricted PARTIAL-complex discovery result only. Not an original SC0 counterexample or a proved two-total-parent obstruction.'})
                (HERE/'PARTIAL_COMPATIBILITY_EXCEPTION.json').write_text(json.dumps(result,indent=2)+'\n')
                print(json.dumps({'tested':tested,'exception':result['result'],'n':n,'run':run},indent=2),flush=True)
                return
            if (run+1)%100==0:
                print(json.dumps({'n':n,'run':run+1,'tested':tested,'elapsed':time.monotonic()-start}),flush=True)
    (HERE/'PARTIAL_COMPATIBILITY_SUMMARY.json').write_text(json.dumps({'tested':tested,'records':records,
        'scope':'Only listed random forbidden-pair subcomplexes, not all partial VC-one classes, not guaranteed two-total-parent reductions, and not the total-class original SC0 target.'},indent=2)+'\n')

if __name__=='__main__':
    main()
