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
 ('NO_ISLANDS.md','f7509ff124d76f12855a55705f317c51133c8e1a93fcadc7f230bebd91b8ad16')]
for name,digest in dependencies:assert sha(folder/name)==digest
names=['critical_exact_intervals.py','CRITICAL_EXACT_INTERVAL_CERTIFICATE.json',
       'CRITICAL_UNIQUENESS_CERTIFICATE.md','replay_critical_certificate.py',
       'CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json','freeze_critical_certificate.py']
for name in names:shutil.copyfile(aux/name,folder/name)
replay=json.loads((folder/'CRITICAL_CERTIFICATE_AUTHOR_REPLAY.json').read_text())
assert replay['result']=='AUTHOR_REPLAY_SUCCESS' and replay['total_leaves']==73
for key,name in [('paper_sha256','CRITICAL_UNIQUENESS_CERTIFICATE.md'),
                 ('source_sha256','critical_exact_intervals.py'),
                 ('certificate_sha256','CRITICAL_EXACT_INTERVAL_CERTIFICATE.json'),
                 ('replayer_sha256','replay_critical_certificate.py')]:
    assert replay[key]==sha(folder/name),(key,name)
for name in names[:-1]:(folder/name).chmod(0o444)
manifest={'frozen_utc':now.isoformat(),'review':'Author only; independent ordinary review pending',
 'scope':['Unique nondegenerate interior last-boundary tie','Strict rational threshold enclosure 519/2000<c_star<13/50',
          'Complete local three-branch phase diagram','Analytic coexistence curves and linear closing of mixed window'],
 'not_claimed':['Unique mixed optimizer for every global c/r','Lean verification','New major problem solved'],
 'files':[{'path':str(folder/name),'sha256':sha(folder/name),'bytes':(folder/name).stat().st_size} for name in names],
 'dependencies':[{'path':str(folder/name),'sha256':digest} for name,digest in dependencies],
 'reproduction':'Copy these frozen files to a private scratch folder; run replay_critical_certificate.py there. Do not regenerate the original frozen certificate: generation records a fresh UTC.',
 'no_external_publication':True,'no_root_changes':True,'no_lean_expansion':True}
dump(folder/'CRITICAL_V1_MANIFEST.json',manifest)
archive=aux/f'critical-unique-dirty-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0')
assert all(not p or p.startswith(prefix+'/') for p in staged),staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: certify unique APPT critical mixed state and local phase diagram'],check=True)
head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'head':head,'status':status,'manifest':manifest,
 'archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size}}
dump(aux/f'critical-unique-checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
