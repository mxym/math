"""Actual adversarial replayer runs on private intentionally damaged copies.
No original source or original certificate timestamp is changed. These test the
authored replayer's guards and are not an independent interval implementation.
"""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,shutil,subprocess,sys,traceback
BASE=Path(__file__).resolve().parent
SRC=BASE/'owner-zip-snapshot/worktree/research/breadth-tcs-20261015/phase-4-depth-appt'
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_countercontrol.py')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
R={'utc':STAMP,'kind':'independent adversarial selections, actual authored replayer executions on private corrupted copies',
   'independent_interval_engine_claim':False,'original_author_certificate_or_UTC_modified':False,'cases':[]}
try:
    names=['critical_exact_intervals.py','replay_critical_certificate.py',
           'CRITICAL_EXACT_INTERVAL_CERTIFICATE.json','CRITICAL_UNIQUENESS_CERTIFICATE.md']
    before={n:sha(SRC/n) for n in names}
    cert=json.loads((SRC/'CRITICAL_EXACT_INTERVAL_CERTIFICATE.json').read_text())
    tests=[]
    a=copy.deepcopy(cert);del a['upper_full_cover'][13]
    tests.append(('upper_cover_hole',a,'A full positive upper-value cover cannot omit an interior interval.'))
    a=copy.deepcopy(cert);del a['outside_core_left'][16]
    tests.append(('whole_K_strip_hole',a,'A whole-K stationary exclusion cannot omit one positive-length x strip.'))
    a=copy.deepcopy(cert);a['core_convexity_cover'][0]['bound']['lo']='0'
    tests.append(('forged_core_curvature_bound',a,'Stored box bounds must equal exact outward recomputation, not merely assert a sign.'))
    a=copy.deepcopy(cert);a['parameters']['K_upper']='3/5'
    tests.append(('widened_K_scope',a,'The original 0.52 certificate must not be relabeled as a wider K domain.'))
    for name,altered,purpose in tests:
        folder=RUN/name;folder.mkdir()
        for file in names:
            if file=='CRITICAL_EXACT_INTERVAL_CERTIFICATE.json':continue
            (folder/file).write_bytes((SRC/file).read_bytes())
        (folder/'CRITICAL_EXACT_INTERVAL_CERTIFICATE.json').write_text(json.dumps(altered,indent=2)+'\n')
        run=subprocess.run([sys.executable,str(folder/'replay_critical_certificate.py')],cwd=folder,capture_output=True)
        (folder/'stdout.txt').write_bytes(run.stdout);(folder/'stderr.txt').write_bytes(run.stderr)
        assert run.returncode!=0 and b'AssertionError' in run.stderr,(name,run.returncode,run.stderr)
        assert not (folder/'CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json').exists()
        R['cases'].append({'case':name,'purpose':purpose,'actual_returncode':run.returncode,
            'actual_exception':'AssertionError','modified_certificate_sha256':sha(folder/'CRITICAL_EXACT_INTERVAL_CERTIFICATE.json'),
            'stderr_sha256':sha(folder/'stderr.txt'),'stdout_sha256':sha(folder/'stdout.txt'),
            'retained_case_directory':str(folder.relative_to(BASE))})
    assert before=={n:sha(SRC/n) for n in names}
    R['unchanged_original_inputs']=before
    R['status']='PASS';R['decision']='PASS';R['expected_real_replayer_failures']=len(tests)
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_countercontrol_sha256']=sha(RUN/'executed_countercontrol.py')
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2)+'\n')
    print(json.dumps({'run':str(RUN),**R},indent=2))
if R['status']!='PASS':raise SystemExit(1)
