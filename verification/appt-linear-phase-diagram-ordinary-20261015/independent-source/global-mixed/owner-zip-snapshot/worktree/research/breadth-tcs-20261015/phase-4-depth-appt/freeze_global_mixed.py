from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess
import zipfile

repo=Path('/home/mxym/math-breadth-tcs-20261015')
prefix='research/breadth-tcs-20261015/phase-4-depth-appt'
folder=repo/prefix
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-4-depth-appt')
now=dt.datetime.now(dt.timezone.utc)
tag=now.strftime('%Y%m%dT%H%M%SZ')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
dependencies=[('PURE_ENVELOPE_GE_ONE.md','ad1a5aabca9d3fcf2e960cbf43bcf7cfbdfd232cc58b86bbaf355229656016a9'),
 ('LAST_MIXED_BOUNDARY.md','6e4f77e2bbecbc5e71f426925d444e8e1a9b69d2ffebcbef88badc1f4e87f0a0'),
 ('NO_ISLANDS.md','f7509ff124d76f12855a55705f317c51133c8e1a93fcadc7f230bebd91b8ad16'),
 ('CRITICAL_UNIQUENESS_CERTIFICATE.md','be76b90de9277fab91c1f676f8de7619c2d58a5b79cf65cf06839d7ce8e7637e'),
 ('critical_exact_intervals.py','78ab0341d6079ceedb7be01abc9eba8608d50df0ad2136fa53b554a547c6ce1c'),
 ('CRITICAL_EXACT_INTERVAL_CERTIFICATE.json','f9dd26bc8b4769a22aac06d07ba76587da18ccbc0ec62292856fcf1ae7eee878')]
for name,digest in dependencies:assert sha(folder/name)==digest
names=['GLOBAL_MIXED_PHASE.md','global_mixed_turn_certificate.py','GLOBAL_MIXED_TURN_CERTIFICATE.json',
       'replay_global_turn_certificate.py','GLOBAL_MIXED_AUTHOR_REPLAY.json',
       'global_mixed_turn_algebra.py','GLOBAL_TURN_ALGEBRA_CONTROL.json',
       'explore_stationary_curve.py','STATIONARY_CURVE_DISCOVERY.json','freeze_global_mixed.py']
for name in names:shutil.copyfile(aux/name,folder/name)
replay=json.loads((folder/'GLOBAL_MIXED_AUTHOR_REPLAY.json').read_text())
assert replay['result']=='AUTHOR_GLOBAL_TURN_REPLAY_SUCCESS' and replay['total_leaves']==74
for key,name in [('paper_sha256','GLOBAL_MIXED_PHASE.md'),
                 ('source_sha256','global_mixed_turn_certificate.py'),
                 ('base_engine_sha256','critical_exact_intervals.py'),
                 ('certificate_sha256','GLOBAL_MIXED_TURN_CERTIFICATE.json'),
                 ('replayer_sha256','replay_global_turn_certificate.py')]:
    assert replay[key]==sha(folder/name),(key,name)
for name in names[:-1]:(folder/name).chmod(0o444)
manifest={'frozen_utc':now.isoformat(),'review':'Author only; new separate ordinary review scope required',
 'owner':'/root/breadth_tcs_resume_20261015, APPT depth role, own prefix only',
 'scope':['All c>0,r>=0 in scalar linear-order finite-r APPT window',
          'Unique mixed global maximizer throughout 0<c<c_star',
          'Exactly two unique analytic coexistence boundaries and all tie sets',
          'Nondegenerate interior maximizer and original APPT body-law transfer',
          'Two turns of R_stat for every 0<K<=13/25 including removable K=0 charts'],
 'not_claimed':['Finite-dimensional exact entropy formulas','All-order physical entropy classification','Lean verification','New major problem solved'],
 'files':[{'path':str(folder/name),'sha256':sha(folder/name),'bytes':(folder/name).stat().st_size} for name in names],
 'dependencies':[{'path':str(folder/name),'sha256':digest} for name,digest in dependencies],
 'reproduction':'Copy new source/certificate/replayer/paper plus unchanged critical_exact_intervals.py to private scratch, then run replay_global_turn_certificate.py. Do not regenerate frozen certificates in place.',
 'no_changed_old_frozen_bytes':True,'no_external_publication':True,'no_root_changes':True,'no_lean_expansion':True}
dump(folder/'GLOBAL_MIXED_V1_MANIFEST.json',manifest)
archive=aux/f'global-mixed-owner-dirty-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0')
assert all(not p or p.startswith(prefix+'/') for p in staged),staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: complete author APPT scalar phase classification with full-domain certificate'],check=True)
head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'head':head,'status':status,'manifest':manifest,
 'archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size}}
dump(aux/f'global-mixed-checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
