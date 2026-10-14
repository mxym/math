"""Verify the exact failure of a row-intersection-variance descent surrogate.
This is not a Ryser counterexample; both permanents exceed 3852.
"""
from pathlib import Path
import json
from ryser_baseline_verify import matching_dp,ryser
p=Path(__file__).with_name('ryser-variance-surrogate-obstruction.json')
d=json.loads(p.read_text());w=d['variance_decrease_with_permanent_increase'];n=13
for side in ['before','after']:
 rows=w[side+'_rows']
 assert len(rows)==n and all(0<=r<(1<<n) and r.bit_count()==4 for r in rows)
 assert all(sum(r>>j&1 for r in rows)==4 for j in range(n))
 variance=sum(((rows[i]&rows[j]).bit_count()-1)**2 for i in range(n) for j in range(n) if i!=j)
 assert variance==w[side+'_variance']
 dp=matching_dp(rows,n);ie=ryser(rows,n)
 assert dp==ie==w[side+'_permanent_dp_and_ryser']
i,j,c,e=w['switch_indices'];rows=w['before_rows'].copy()
assert (rows[i]>>c&1,rows[i]>>e&1,rows[j]>>c&1,rows[j]>>e&1)==(1,0,0,1)
rows[i]^=(1<<c)|(1<<e);rows[j]^=(1<<c)|(1<<e)
assert rows==w['after_rows']
assert w['after_variance']<w['before_variance'] and w['after_permanent_dp_and_ryser']>w['before_permanent_dp_and_ryser']>3852
print({'actual_binary_margins':True,'variance':(64,60),'exact_permanents_two_methods':(4208,4212),'full_Ryser_counterexample':False})
