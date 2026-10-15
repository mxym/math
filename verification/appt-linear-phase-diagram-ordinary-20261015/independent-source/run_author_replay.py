"""Reviewer invokes the unmodified authored replayer in a new private scratch.

This is an actual reviewer execution of author code, not a newly independent
implementation. Mathematical review and independent auxiliary controls remain
separate. The certificate generator is never executed and its UTC is preserved.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,subprocess,sys,traceback
BASE=Path(__file__).resolve().parent
SCRATCH=BASE/'certificate-replay-scratch'
FROZEN=BASE/'owner-zip-snapshot/worktree/research/breadth-tcs-20261015/phase-4-depth-appt'
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_wrapper.py')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
R={'utc':STAMP,'kind':'actual private replay of unchanged author certificate checker; not independent code or Lean',
   'certificate_generator_executed':False,'original_owner_files_written':False}
try:
    names=['critical_exact_intervals.py','replay_critical_certificate.py',
           'CRITICAL_EXACT_INTERVAL_CERTIFICATE.json','CRITICAL_UNIQUENESS_CERTIFICATE.md']
    before={n:sha(SCRATCH/n) for n in names}
    assert all((SCRATCH/n).read_bytes()==(FROZEN/n).read_bytes() for n in names)
    assert before['CRITICAL_EXACT_INTERVAL_CERTIFICATE.json']=='f9dd26bc8b4769a22aac06d07ba76587da18ccbc0ec62292856fcf1ae7eee878'
    cert=json.loads((SCRATCH/'CRITICAL_EXACT_INTERVAL_CERTIFICATE.json').read_text())
    R['original_certificate_utc']={k:cert[k] for k in ['started_utc','completed_utc']}
    assert not (SCRATCH/'CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json').exists()
    result=subprocess.run([sys.executable,str(SCRATCH/'replay_critical_certificate.py')],
                          cwd=SCRATCH,capture_output=True)
    (RUN/'stdout.txt').write_bytes(result.stdout);(RUN/'stderr.txt').write_bytes(result.stderr)
    R['returncode']=result.returncode
    assert result.returncode==0,result.stderr.decode()
    replay=json.loads((SCRATCH/'CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json').read_text())
    assert replay['result']=='AUTHOR_REPLAY_SUCCESS'
    assert replay['total_leaves']==73
    assert replay['leaf_counts']=={'upper_full_cover':27,'outside_core_left':32,'outside_core_right':13,'core_convexity_cover':1}
    assert before=={n:sha(SCRATCH/n) for n in names}
    assert all((SCRATCH/n).read_bytes()==(FROZEN/n).read_bytes() for n in names)
    shutil.copyfile(SCRATCH/'CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json',RUN/'REPLAY_OUTPUT.json')
    R.update({'status':'PASS','decision':'PASS','replay_output':replay,
       'all_four_inputs_exact_before_after':before,'author_certificate_bytes_and_UTC_unchanged':True,
       'private_replay_output_sha256':sha(RUN/'REPLAY_OUTPUT.json')})
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_wrapper_sha256']=sha(RUN/'executed_wrapper.py')
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2)+'\n')
    print(json.dumps({'run':str(RUN),**R},indent=2))
if R['status']!='PASS':raise SystemExit(1)
