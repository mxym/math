"""Cross-enumeration and adversarial controls for finite DAG certificates."""
from pathlib import Path
import copy
import hashlib
import json
import sys
from check_dag_certificate import check
from finite_decoder import samples, submasks

HERE=Path(__file__).parent

def must_reject(data,label):
    try:
        check(data)
    except (ValueError,KeyError,TypeError):
        return {'mutation':label,'rejected':True}
    raise ValueError('Mutated certificate was accepted: '+label)

def controls(file):
    d=json.loads(file.read_text())
    result=check(d)
    H={(r['mask'],r['labels']):r['output'] for r in d['decoder']}
    S=samples(d['n'],d['C'])
    require=all(any(H[(u,b&u)]&a==b for u in submasks(a)
                    if u.bit_count()<=d['d']) for a,b in S)
    if not require:
        raise ValueError('Direct enumeration disagrees with DAG checker')
    result['directly_enumerated_realizable_partial_samples']=len(S)
    result['direct_enumeration_agrees']=True
    mutants=[]
    q=copy.deepcopy(d); q['certificate']['roots'].pop()
    mutants.append(must_reject(q,'remove complete concept root'))
    q=copy.deepcopy(d); nonleaf=next(x for x in q['certificate']['nodes'] if x['children']); nonleaf['children'].pop()
    mutants.append(must_reject(q,'remove required deletion child edge'))
    q=copy.deepcopy(d); nonleaf=next(x for x in q['certificate']['nodes'] if x['children']); nonleaf['children'].append(nonleaf['children'][0])
    mutants.append(must_reject(q,'duplicate deletion child edge'))
    q=copy.deepcopy(d); full=(1<<d['n'])-1; root=next(x for x in q['certificate']['nodes'] if x['mask']==full)
    msg=(root['message_mask'],root['message_labels']); row=next(x for x in q['decoder'] if (x['mask'],x['labels'])==msg); row['output']^=1
    mutants.append(must_reject(q,'change a root decoder output by one bit'))
    q=copy.deepcopy(d); q['d']=1
    mutants.append(must_reject(q,'misdeclare VC dimension and compression size as one'))
    q=copy.deepcopy(d); q['certificate']['nodes'].append(copy.deepcopy(q['certificate']['nodes'][0]))
    mutants.append(must_reject(q,'duplicate certificate node'))
    q=copy.deepcopy(d); q['status']='round_cap_exhausted'
    mutants.append(must_reject(q,'claim an unfinished synthesis record is a certificate'))
    q=copy.deepcopy(d); q['C'].pop()
    mutants.append(must_reject(q,'delete a concept without matching the root set'))
    result['mutations']=mutants
    result['certificate_sha256']=hashlib.sha256(file.read_bytes()).hexdigest()
    return result

if __name__=='__main__':
    files=['CEGIS_N8_D2_SEED41.json','CEGIS_N10_D2_SEED73_RESUMED.json']
    record={'mode':'optimized' if not __debug__ else 'normal',
            'scope':'Only two listed finite certificates; checks and mutations are not an independent mathematical review or proof of SC0.',
            'results':{f:controls(HERE/f) for f in files},
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    suffix='_OPT' if not __debug__ else ''
    (HERE/f'CERTIFICATE_CONTROLS{suffix}.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))
