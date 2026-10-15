"""Resume a finite general-model probe with mandatory small samples seeded.

These constraints are genuine original samples; no decoder family is
restricted and no side channel is added. The earlier inconclusive result
is kept as a separate file. A timeout still proves nothing about SC0.
"""
from pathlib import Path
import hashlib
import json
import finite_cegis as fc

HERE=Path(__file__).parent
old_file=HERE/'CEGIS_N12_D2_SEED107.json'
old=json.loads(old_file.read_text())
n,d,seed=12,2,107
C=fc.maximal_class(n,d,seed)
if old['C']!=C or old['actual_VC']!=d:
    raise ValueError('Resume source changed its finite class')
prior=[]
for state in old['history']:
    if 'failed_sample' in state:
        prior.append(state['failed_sample'])
    prior.extend(state.get('failed_samples',[]))
small=sorted({(a,c&a) for a in fc.masks_at_most(n,d+1)
              if a.bit_count()==d+1 for c in C})
initial=sorted({tuple(s) for s in prior}|set(small))
result=fc.synthesize(n,C,d,budget=300,seed=seed,initial_samples=initial)
result['resume_input_sha256']=hashlib.sha256(old_file.read_bytes()).hexdigest()
result['retained_prior_failed_samples']=len(prior)
result['mandatory_size_three_samples_seeded']=len(small)
result['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in [Path(__file__),HERE/'finite_cegis.py']}
result['scope']='One listed finite VC-two class. Original general improper no-side-information constraints retained. No universal theorem or negative conclusion from timeout.'
(HERE/'CEGIS_N12_D2_SEED107_LOCAL_SEED.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()
                  if k not in ['C','history','decoder','certificate','synthesized_sample_constraints']},indent=2))
print('rounds',len(result['history']),flush=True)
