"""Four genuine negative replay controls on private global certificate copies.
Adversarial choices are independent; the replayer remains authored code.
"""
from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction as F
import copy,hashlib,json,shutil,subprocess,sys,traceback
BASE=Path(__file__).resolve().parent
SRC=BASE/'owner-zip-snapshot/worktree/research/breadth-tcs-20261015/phase-4-depth-appt'
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_countercontrol.py')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
R={'utc':STAMP,'kind':'independently chosen corrupted copies, actual unchanged authored global replayer executions',
    'original_owner_files_or_UTC_changed':False,'independent_interval_engine_claim':False,'cases':[]}
try:
    names=['global_mixed_turn_certificate.py','GLOBAL_MIXED_TURN_CERTIFICATE.json',
       'replay_global_turn_certificate.py','critical_exact_intervals.py','GLOBAL_MIXED_PHASE.md']
    before={n:sha(SRC/n) for n in names};cert=json.loads((SRC/'GLOBAL_MIXED_TURN_CERTIFICATE.json').read_text())
    tests=[];rows=cert['stages'][0]['leaves']
    def area(row):
        l,h=map(F,row['first']);b,d=map(F,row['second']);return (h-l)*(d-b)
    pair=next((i,j) for i in range(len(rows)) for j in range(i+1,len(rows)) if area(rows[i])==area(rows[j]))
    damaged=copy.deepcopy(cert);damaged['stages'][0]['leaves'][pair[1]]=copy.deepcopy(rows[pair[0]])
    assert sum(area(x) for x in damaged['stages'][0]['leaves'])==sum(area(x) for x in rows)
    tests.append(('equal_area_gap_and_overlap',damaged,'Duplicate one box and remove a different equal-area box: total area is unchanged, tiling is false.'))
    damaged=copy.deepcopy(cert)
    leaf=next(x for x in damaged['stages'][2]['leaves'] if x['method']=='strict_negative')
    assert F(leaf['first'][0])*F(leaf['second'][0])<=F(13,25)
    leaf['method']='outside_K_cap';leaf['bound']=None
    tests.append(('false_outside_K_cap',damaged,'An admissible middle box may not be discarded as outside the cap.'))
    damaged=copy.deepcopy(cert)
    zero=[x for x in damaged['stages'][0]['leaves'] if F(x['first'][0])==0]
    eps=min(F(x['first'][1]) for x in zero)/2
    for leaf in zero:leaf['first'][0]=str(eps)
    tests.append(('omit_arbitrarily_small_K',damaged,'Remove every K=0 first-axis edge without changing the declared full domain.'))
    damaged=copy.deepcopy(cert);damaged['stages'][1]['leaves'][0]['bound']['hi']='0'
    tests.append(('forged_turn_derivative_bound',damaged,'A strict derivative bound must match exact recomputation.'))
    for name,altered,purpose in tests:
        case=RUN/name;case.mkdir()
        for n in names:
            if n!='GLOBAL_MIXED_TURN_CERTIFICATE.json':(case/n).write_bytes((SRC/n).read_bytes())
        (case/'GLOBAL_MIXED_TURN_CERTIFICATE.json').write_text(json.dumps(altered,indent=2)+'\n')
        p=subprocess.run([sys.executable,str(case/'replay_global_turn_certificate.py')],cwd=case,capture_output=True)
        (case/'stdout.txt').write_bytes(p.stdout);(case/'stderr.txt').write_bytes(p.stderr)
        assert p.returncode!=0 and b'AssertionError' in p.stderr,(name,p.returncode,p.stderr)
        assert not (case/'GLOBAL_MIXED_AUTHOR_REPLAY.json').exists()
        R['cases'].append({'name':name,'purpose':purpose,'actual_returncode':p.returncode,
            'actual_exception':'AssertionError','modified_certificate_sha256':sha(case/'GLOBAL_MIXED_TURN_CERTIFICATE.json'),
            'stderr_sha256':sha(case/'stderr.txt'),'case_directory':str(case.relative_to(BASE))})
    assert before=={n:sha(SRC/n) for n in names}
    R['unchanged_original_inputs']=before;R['expected_actual_child_failures']=len(tests)
    R['status']='PASS';R['decision']='PASS'
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_countercontrol_sha256']=sha(RUN/'executed_countercontrol.py')
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2)+'\n')
    print(json.dumps({'run':str(RUN),**R},indent=2))
if R['status']!='PASS':raise SystemExit(1)
