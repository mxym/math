"""Exact controls for a proper global-compatibility obstruction below VC.

No size-VC impossibility is asserted. The mathematical size-one lower bound
in the notes is proved by tight projections, not by trusting SMT UNSAT.
"""
from pathlib import Path
from itertools import combinations
import json
from finite_decoder import solve, samples, vcdim
from resumed_controls import WARMUTH

HERE=Path(__file__).parent

def shift(C,i):
    C=set(C); bit=1<<i
    return sorted({(c^bit) if c&bit and c^bit not in C else c for c in C})

def main():
    C=sorted(WARMUTH); n=5
    triples=[sum(1<<i for i in A) for A in combinations(range(n),3)]
    fours=[31^(1<<i) for i in range(n)]
    assert all(len({c&a for c in C})==7 for a in triples)
    assert all(len({c&a for c in C})==9 for a in fours)
    closure=[h for h in range(32) if all(h&a in {c&a for c in C} for a in triples)]
    assert closure==C
    # Every improper h has a forbidden triple witness. For ANY singleton
    # message coordinate j, some four-set contains both j and that witness.
    witness=[]
    for h in range(32):
        if h in C:
            continue
        B=next(a for a in triples if h&a not in {c&a for c in C})
        for j in range(n):
            A=next(a for a in fours if not(B&~a) and (a>>j)&1)
            assert h&A not in {c&A for c in C}
        witness.append({'outside_row':h,'forbidden_triple_mask':B})
    records=[]
    while True:
        change=False
        for i in range(n):
            new=shift(C,i)
            if new==C:
                continue
            probe=solve(n,new,d=1,timeout_ms=10000)
            records.append({'coordinate':i,'before':C,'after':new,'probe':probe})
            C=new; change=True
        if not change:
            break
    output={'original_C':sorted(WARMUTH),'original_VC':2,
            'triple_projection_size':7,'four_projection_size':9,
            'forbidden_triple_witnesses':witness,
            'lower_bound_proof':'Every one-message decoder output must lie in C by tight four-coordinate projections plus forbidden triple witnesses. Those projections also force all 11 message outputs to be distinct, but C has size 10. Hence no general labeled improper size-one scheme. This is BELOW VC=2 and does not refute SC0.',
            'shift_records':records,
            'scope':'One explicit five-coordinate class and its listed coordinate shifts; any failure of arbitrary-k shift lifting does not refute a VC-bound-specific theorem or SC0.'}
    first=records[0]['probe']; H={(x['mask'],x['labels']):x['output'] for x in first['decoder']}
    chains=[]
    for c in first['C']:
        a=31; deletion=[]
        while H[(0,0)]&a != c&a:
            j=next(j for j in range(5) if (a>>j)&1
                   and H[(1<<j,c&(1<<j))]&a == c&a)
            deletion.append(j); a^=1<<j
        chains.append({'concept':c,'delete_coordinates':deletion,'residual_domain_mask':a})
    output['first_shift_size_one_chains']=chains
    (HERE/'WARMUTH_LOWER_SHIFTING_CONTROLS.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'steps':len(records),'results':[r['probe']['solver_result'] for r in records],
                      'final_C':C,'final_VC':vcdim(n,C)},indent=2))

if __name__=='__main__':
    main()
