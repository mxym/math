"""Run the exact authored fourth-scope replayer in fresh private scratch.
The generator and original owner files are never executed/mutated in place.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,subprocess,sys,traceback
BASE=Path(__file__).resolve().parent
SRC=BASE/'owner-zip-snapshot/worktree/research/breadth-tcs-20261015/phase-4-depth-appt'
STAMP=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
RUN=BASE/'runs'/STAMP;RUN.mkdir(parents=True)
shutil.copyfile(__file__,RUN/'executed_wrapper.py')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
R={'utc':STAMP,'kind':'actual private execution of authored global-turn replayer; no independent engine claim',
   'certificate_generator_executed':False,'original_author_files_or_UTC_changed':False}
try:
    names=['global_mixed_turn_certificate.py','GLOBAL_MIXED_TURN_CERTIFICATE.json',
           'replay_global_turn_certificate.py','GLOBAL_MIXED_PHASE.md','critical_exact_intervals.py']
    before={n:sha(SRC/n) for n in names};scratch=RUN/'scratch';scratch.mkdir()
    for n in names:(scratch/n).write_bytes((SRC/n).read_bytes())
    cert=json.loads((SRC/'GLOBAL_MIXED_TURN_CERTIFICATE.json').read_text())
    R['original_certificate_UTC']={k:cert[k] for k in ['started_utc','completed_utc']}
    process=subprocess.run([sys.executable,str(scratch/'replay_global_turn_certificate.py')],cwd=scratch,capture_output=True)
    (RUN/'stdout.txt').write_bytes(process.stdout);(RUN/'stderr.txt').write_bytes(process.stderr)
    R['returncode']=process.returncode
    assert process.returncode==0,process.stderr.decode()
    output=json.loads((scratch/'GLOBAL_MIXED_AUTHOR_REPLAY.json').read_text())
    assert output['result']=='AUTHOR_GLOBAL_TURN_REPLAY_SUCCESS' and output['total_leaves']==74
    assert [x['leaves'] for x in output['stage_counts']]==[35,1,28,5,1,4]
    mid=output['stage_counts'][2];assert mid['methods']['outside_K_cap']==7 and mid['methods']['strict_negative']==21
    assert before=={n:sha(scratch/n) for n in names}=={n:sha(SRC/n) for n in names}
    shutil.copyfile(scratch/'GLOBAL_MIXED_AUTHOR_REPLAY.json',RUN/'REPLAY_OUTPUT.json')
    R.update({'status':'PASS','decision':'PASS','all_five_inputs_exact_before_after':before,
        'original_certificate_bytes_and_UTC_unchanged':True,'replay_output':output,
        'replay_output_sha256':sha(RUN/'REPLAY_OUTPUT.json')})
except BaseException:
    R['status']='FAIL';R['decision']='FAIL';R['traceback']=traceback.format_exc()
finally:
    R['executed_wrapper_sha256']=sha(RUN/'executed_wrapper.py')
    (RUN/'RESULT.json').write_text(json.dumps(R,indent=2)+'\n')
    print(json.dumps({'run':str(RUN),**R},indent=2))
if R['status']!='PASS':raise SystemExit(1)
