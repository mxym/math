"""Actual totalBoolean controls for the full log-rank stage; no full theorem."""
from pathlib import Path
from datetime import datetime,timezone
import json
cases=[]
for s in [2,3,4,5]:
    rows=[(x,i) for x in range(1<<s) for i in range(s)]
    cols=[(j,y) for j in range(s) for y in range(1<<s)]
    a=[[((x>>j)&1)*((y>>i)&1) for j,y in cols] for x,i in rows]
    n=s*(1<<s);assert len(a)==n and all(len(v)==n for v in a)
    basis_rows=[rows.index((1<<h,i)) for h in range(s) for i in range(s)]
    basis_cols=[cols.index((j,1<<k)) for j in range(s) for k in range(s)]
    minor=[[a[i][j] for j in basis_cols] for i in basis_rows]
    assert minor==[[int(i==j) for j in range(s*s)] for i in range(s*s)]
    rectangles=[]
    for j in range(s):
        for i in range(s):
            rr=[h for h,(x,k) in enumerate(rows) if k==i and (x>>j)&1]
            cc=[h for h,(k,y) in enumerate(cols) if k==j and (y>>i)&1]
            rectangles.append({'row_indices':rr,'column_indices':cc})
    sums=[[0]*n for _ in range(n)]
    for r in rectangles:
        for i in r['row_indices']:
            for j in r['column_indices']:sums[i][j]+=1
    assert sums==a
    rowtypes=len(set(tuple(v) for v in a))
    coltypes=len(set(tuple(a[i][j] for i in range(n)) for j in range(n)))
    assert rowtypes==coltypes==s*((1<<s)-1)+1
    ceil_log_s=(s-1).bit_length()
    worst_bits=0;checked=0
    for ri,(x,i) in enumerate(rows):
        for cj,(j,y) in enumerate(cols):
            # Alice announces i; Bob j; Alice x_j; Bob the resulting value.
            announced_xj=(x>>j)&1
            leaf=announced_xj*((y>>i)&1)
            assert leaf==a[ri][cj]
            worst_bits=max(worst_bits,2*ceil_log_s+2);checked+=1
    cases.append({'parameter_s':s,'actual_totalBoolean_order':n,'exact_rank':s*s,
                  'rank_lower_identity_minor_row_indices':basis_rows,
                  'rank_lower_identity_minor_column_indices':basis_cols,
                  'rank_upper_disjoint_all_one_rectangles':rectangles,
                  'signed_rectangle_rank_equals_real_rank':s*s,
                  'row_types':rowtypes,'column_types':coltypes,
                  'one_way_Alice_to_Bob_output_lower_bits':(rowtypes-1).bit_length(),
                  'interactive_public_output_protocol_upper_bits':worst_bits,
                  'all_entry_protocol_and_partition_checks':checked,
                  'adjacency_or_communication_matrix':a,
                  'full_log_rank_solution':False})
result={'schema':'full-log-rank-auxiliary-totalBoolean-controls-v1',
        'checked_utc':datetime.now(timezone.utc).isoformat().replace('+00:00','Z'),
        'written_family':'K_s[(x,i),(j,y)]=x_j*y_i for all x,y in {0,1}^s and all i,j in [s]. Every cross input is defined.',
        'scope':'Known elementary indexing/tensor controls. Rank=s^2 and short interactive protocol hold for the written entire family, not allBoolean matrices. No major-result count.',
        'tests':'Finite selected cases independently compare identity rank-minor, positive disjoint reconstruction, exact row/column types and protocol outputs for every entry.',
        'cases':cases,'new_major_results':0,'full_conjecture_solved':False}
out=Path(__file__).with_name('log-rank-totalboolean-controls.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'cases':len(cases),'entries_checked':sum(x['all_entry_protocol_and_partition_checks'] for x in cases),
                  'ranks':[x['exact_rank'] for x in cases],'full_log_rank_solution':False,'path':str(out)}))
