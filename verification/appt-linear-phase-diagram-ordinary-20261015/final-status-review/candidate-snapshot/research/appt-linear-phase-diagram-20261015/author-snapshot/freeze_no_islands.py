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
for name,digest in [('PURE_ENVELOPE_GE_ONE.md','ad1a5aabca9d3fcf2e960cbf43bcf7cfbdfd232cc58b86bbaf355229656016a9'),
 ('LAST_MIXED_BOUNDARY.md','6e4f77e2bbecbc5e71f426925d444e8e1a9b69d2ffebcbef88badc1f4e87f0a0')]:
    assert sha(folder/name)==digest
for name in ['NO_ISLANDS.md','no_islands_author_controls.py','NO_ISLANDS_AUTHOR_CONTROL.json',
             'explore_monotonic_sufficient_bounds.py','MONOTONIC_SUFFICIENT_BOUNDS_DISCOVERY.json',
             'freeze_no_islands.py']:
    shutil.copyfile(aux/name,folder/name)
paper=folder/'NO_ISLANDS.md'
assert sha(paper)=='f7509ff124d76f12855a55705f317c51133c8e1a93fcadc7f230bebd91b8ad16'
assert json.loads((folder/'NO_ISLANDS_AUTHOR_CONTROL.json').read_text())['paper_sha256']==sha(paper)
paper.chmod(0o444)
manifest={'frozen_utc':now.isoformat(),'scope':'Single mixed-c interval and unique last parameter; finitely many threshold interior ties',
 'review':'Author only; independent ordinary review pending',
 'paper':{'path':str(paper),'sha256':sha(paper),'bytes':paper.stat().st_size},
 'controls':{'path':str(folder/'NO_ISLANDS_AUTHOR_CONTROL.json'),'sha256':sha(folder/'NO_ISLANDS_AUTHOR_CONTROL.json')},
 'dependencies':['PURE_ENVELOPE_GE_ONE.md frozen v1','LAST_MIXED_BOUNDARY.md frozen v1','credited L/S for actual APPT transfer'],
 'not_proved':['Unique interior threshold width','Unique strict mixed optimizer for every r','Certified numerical c_star enclosure'],
 'original_full_phase_target_status':'Author partial closure; full mixed branch uniqueness still open',
 'no_lean_expansion':True,'no_push':True,'no_root_changes':True}
dump(folder/'NO_ISLANDS_V1_MANIFEST.json',manifest)
archive=aux/f'no-islands-dirty-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0')
assert all(not p or p.startswith(prefix+'/') for p in staged),staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: prove author no-islands scalar transition theorem'],check=True)
head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'head':head,'status':status,'manifest':manifest,
 'archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size}}
dump(aux/f'no-islands-checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
