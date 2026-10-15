"""Plain integer verification of later finite decoder certificates."""
from pathlib import Path
import copy,gzip,hashlib,json,sys
from check_dag_certificate import check
from certificate_controls import must_reject
from finite_decoder import samples,submasks
R=Path(__file__).parent
NAMES=['CEGIS_N12_D2_SEED107_CNF.json','CEGIS_N16_D2_SEED149_CNF.json','CEGIS_N12_D3_SEED211_CNF.json']
def run(name):
    p=R/name
    if p.exists():raw=p.read_bytes();archive=None
    else:
        p=R/(name+'.gz'); raw=gzip.decompress(p.read_bytes()); archive=hashlib.sha256(p.read_bytes()).hexdigest()
    d=json.loads(raw);res=check(d)
    if d['n']<=12:
        H={(x['mask'],x['labels']):x['output'] for x in d['decoder']}
        S=samples(d['n'],d['C'])
        for a,b in S:
            if not any(H[(u,b&u)]&a==b for u in submasks(a) if u.bit_count()<=d['d']):
                raise ValueError('Enumerated sample was not covered')
        res['directly_enumerated_realizable_partial_samples']=len(S)
        res['direct_enumeration_agrees']=True
    else:
        res['direct_enumeration']='Not run at n>12; complete coverage certified by checked deletion-DAG induction.'
    q=copy.deepcopy(d);q['certificate']['roots'].pop();mut=[must_reject(q,'remove full root')]
    q=copy.deepcopy(d);x=next(x for x in q['certificate']['nodes'] if x['children']);x['children'].pop();mut.append(must_reject(q,'remove required child'))
    q=copy.deepcopy(d);x=next(x for x in q['certificate']['nodes'] if x['children']);x['children'].append(x['children'][0]);mut.append(must_reject(q,'duplicate required child'))
    q=copy.deepcopy(d);full=(1<<d['n'])-1;x=next(x for x in q['certificate']['nodes'] if x['mask']==full);t=(x['message_mask'],x['message_labels']);z=next(z for z in q['decoder'] if (z['mask'],z['labels'])==t);z['output']^=1;mut.append(must_reject(q,'flip root output bit'))
    q=copy.deepcopy(d);q['d']=1;mut.append(must_reject(q,'misdeclare actual VC'))
    q=copy.deepcopy(d);q['certificate']['nodes'].append(copy.deepcopy(q['certificate']['nodes'][0]));mut.append(must_reject(q,'duplicate node'))
    q=copy.deepcopy(d);q['status']='solver_unknown';mut.append(must_reject(q,'unfinished solver status'))
    q=copy.deepcopy(d);q['C'].pop();mut.append(must_reject(q,'delete concept without adjusting roots'))
    res['mutations']=mut;res['certificate_raw_sha256']=hashlib.sha256(raw).hexdigest()
    if archive:res['archive_sha256']=archive
    return res
if __name__=='__main__':
    rec={'scope':'Three listed finite certificates only. Same-author integer checks, not independent mathematical review or a proof of SC0.',
         'results':{f:run(f) for f in NAMES},
         'source_sha256':{s:hashlib.sha256((R/s).read_bytes()).hexdigest() for s in ['check_late_certificates.py','check_dag_certificate.py','certificate_controls.py','finite_decoder.py']}}
    (R/'LATE_CERTIFICATE_CONTROLS.json').write_text(json.dumps(rec,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:{x:y for x,y in v.items() if x!='mutations'} for k,v in rec['results'].items()},indent=2))
