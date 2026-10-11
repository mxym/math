#!/usr/bin/env python3
"""Finite synthetic experiment-design screen on exact water-invisible directions.
No claim of global continuous optimality. Unit tracer pulse; 90 daily samples.
"""
import argparse
import json
from pathlib import Path
import numpy as np
from scipy.linalg import expm
from exact import A,D,B,Q,V

def run():
    a,d,b,q,v=map(lambda x:np.asarray(x,dtype=float),[A,D,B,Q,V])
    xs=[v@np.eye(4)[[j],:] for j in [1,2,3]]
    mats={}
    for u in [0,1]:
        block=np.zeros((16,16));block[:4,:4]=a
        for j,x in enumerate(xs):
            off=4+4*j;block[off:off+4,off:off+4]=a
            block[off:off+4,:4]=u*(d@x-x@d)
        mats[u]=expm(block)
    def info(schedule):
        state=np.r_[b[:,0],np.zeros(12)];rows=[]
        for u in schedule:
            state=mats[u]@state
            rows.append([float((q@state[4+4*j:8+4*j]).item()) for j in range(3)])
        jmat=np.array(rows);sv=np.linalg.svd(jmat,compute_uv=False)
        return sv,jmat
    baseline,_=info([1]*90);zero,_=info([0]*90)
    # All 61 schedules in this prespecified family are evaluated, not randomly
    # selected after seeing their scores: delay 0..60, then constant unit ET.
    choices=[]
    for delay in range(61):
        sv,_=info([0]*delay+[1]*(90-delay))
        choices.append({'delay_days':delay,'singular_values':sv.tolist()})
    best=max(choices,key=lambda d:d['singular_values'][-1])
    return {'status':'PASS','scope':'synthetic local sensitivity; finite schedule family; no field data',
            'gauge_directions':3,'daily_samples':90,'unit_tracer_pulse_at_day':0,
            'always_demand_singular_values':baseline.tolist(),'zero_demand_singular_values':zero.tolist(),
            'best_delayed_step':best,'candidate_schedules':len(choices),
            'minimum_singular_value_gain':best['singular_values'][-1]/baseline[-1],
            'minimum_fisher_eigenvalue_gain':(best['singular_values'][-1]/baseline[-1])**2,
            'all_schedule_results':choices}
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).parent/'results')
    args=parser.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
    result=run();out=args.output_dir/'design.json';out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='all_schedule_results'},indent=2))
