"""Actual Boolean controls against fixed signed-cancellation entropy bounds."""
from pathlib import Path
from math import comb
from datetime import datetime,timezone
import json
def determinant(a):
    a=[r[:] for r in a];n=len(a);sgn=1;prev=1
    for k in range(n-1):
        if not a[k][k]:
            t=next(i for i in range(k+1,n) if a[i][k])
            a[k],a[t]=a[t],a[k];sgn=-sgn
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                z=a[i][j]*pivot-a[i][k]*a[k][j]
                assert z%prev==0;a[i][j]=z//prev
            a[i][k]=0
        prev=pivot
    return sgn*a[-1][-1]
cases=[]
for s in [2,3,4,5,6]:
    r=2*s
    def z(x):return sum((x>>i)&1 for i in range(s))-sum((x>>i)&1 for i in range(s,r))
    rows=[x for x in range(1<<r) if z(x) in (0,1)]
    assert len(rows)==comb(2*s+1,s)
    sizes=[sum(z(x)==v for x in rows) for v in (0,1)]
    assert sizes==[comb(2*s,s),comb(2*s,s-1)]
    # r coordinate columns and r identical gamma columns make gamma mass1/2.
    a=[[(x>>j)&1 for j in range(r)]+[z(x)]*r for x in rows]
    gamma=[1]*s+[-1]*s
    for x,entry in zip(rows,a):
        assert all(v in (0,1) for v in entry)
        factor=[(x>>j)&1 for j in range(r)]
        assert sum(factor[j]*gamma[j] for j in range(r))==z(x)
        for y in range(2*r):
            # s positive paired terms, s positive coordinate terms, s negative gamma terms.
            signed=sum(((x>>i)&1)*int(y==i or y>=r) for i in range(s))
            signed+=sum(((x>>i)&1)*int(y==i) for i in range(s,r))
            signed-=sum(((x>>i)&1)*int(y>=r) for i in range(s,r))
            assert signed==entry[y]
    base=[1<<i for i in range(s)]+[(1<<0)|(1<<j) for j in range(s,r)]
    minor=[[a[rows.index(x)][j] for j in range(r)] for x in base]
    assert determinant(minor)==1
    # Gamma-column active signed-term patterns exactly identify x.
    patterns=[]
    for x in rows:
        pat=tuple([((x>>i)&1) for i in range(s)]+[0]*s+[((x>>i)&1) for i in range(s,r)])
        patterns.append(pat)
    assert len(set(patterns))==len(rows)
    for v in (0,1):
        pp=[patterns[i] for i,x in enumerate(rows) if z(x)==v]
        assert len(set(pp))==sizes[v]
    protocol_upper=r.bit_length()+1 # ceil log2(r+1)+Alice output
    for entry in a:
        for j in range(2*r):
            label=j if j<r else r
            output=entry[label]
            assert output==entry[j]
    cases.append({'s':s,'actual_rows':len(rows),'actual_columns':2*r,'exact_real_rank':r,
                  'rank_minor_determinant':1,'rank_minor_rows':base,
                  'rank_upper_factor':'X=the coordinate bit table, Y=[I_r | gamma repeated r times]',
                  'signed_primitive_term_count':3*s,'factor_vs_minimum_signed_rank_at_most':'3/2',
                  'row_bit_patterns':rows,'gamma_column_count':r,'gamma_column_masses':[1,2],
                  'gamma_output_counts':sizes,
                  'exact_gamma_pattern_entropy':'log2(actual_rows)',
                  'global_conditional_active_pattern_entropy_lower':'0.5*log2(actual_rows)',
                  'post_output_pattern_entropies':['log2(gamma_output_counts[0])','log2(gamma_output_counts[1])'],
                  'interactive_public_output_protocol_upper':protocol_upper,
                  'known_or_auxiliary_control_only':True,'full_log_rank_counterexample':False})
result={'schema':'full-log-rank-cancellation-entropy-controls-v1',
        'checked_utc':datetime.now(timezone.utc).isoformat().replace('+00:00','Z'),
        'family':'All coordinate patterns x in {0,1}^{2s} with gamma*x in {0,1}; coordinate columns plus2s gamma copies. Actual complete Boolean matrix.',
        'purpose':'Reject a polylog-rank upper bound on the active-pattern entropy of a fixed O(rank)-length signed decomposition, even after conditioning on an easy monochromatic rectangle. Does not refute log-rank.',
        'cases':cases,'entry_checks':sum(c['actual_rows']*c['actual_columns'] for c in cases),
        'new_major_results':0,'complete_original_target_solved':False}
out=Path(__file__).with_name('log-rank-cancellation-entropy-controls.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'cases':len(cases),'entry_checks':result['entry_checks'],'largest_order':[cases[-1]['actual_rows'],cases[-1]['actual_columns']],'actual_full_log_rank_counterexamples':0,'path':str(out)}))
