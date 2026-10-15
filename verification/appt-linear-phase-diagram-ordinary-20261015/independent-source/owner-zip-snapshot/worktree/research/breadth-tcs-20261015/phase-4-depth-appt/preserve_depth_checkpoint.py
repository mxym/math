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
paper=folder/'PURE_ENVELOPE_GE_ONE.md'
assert sha(paper)=='ad1a5aabca9d3fcf2e960cbf43bcf7cfbdfd232cc58b86bbaf355229656016a9'
for name in ['LAST_MIXED_BOUNDARY.md','preserve_depth_checkpoint.py']:
    shutil.copyfile(aux/name,folder/name)
boundary=folder/'LAST_MIXED_BOUNDARY.md'
boundary.chmod(0o444)
boundarymeta={'path':str(boundary),'sha256':sha(boundary),'bytes':boundary.stat().st_size,
 'frozen_utc':now.isoformat(),'review':'pending independent ordinary review',
 'scope':'Last mixed boundary has interior triple coexistence; no no-islands claim',
 'independent_scalar_argument':True,'credited_actual_matrix_transfer':['L','S'],
 'not_dependencies':['root scalar T draft','root small-c lower-onset B7 draft']}
dump(folder/'LAST_BOUNDARY_V1_MANIFEST.json',boundarymeta)
before=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
manifest=[]
for p in sorted(folder.rglob('*')):
    if p.is_file() and p.name not in ['CHECKPOINT_FILE_MANIFEST.json']:
        manifest.append({'path':p.relative_to(repo).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size})
dump(folder/'CHECKPOINT_FILE_MANIFEST.json',{'utc':now.isoformat(),'precommit_head':before,
 'target_status':'Intermediate c complete phase diagram open; no major result claimed',
 'clock_policy':'APPT depth has no breadth switch clock','files':manifest})
archive=aux/f'depth-first-checkpoint-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
    for p in sorted(aux.iterdir()):
        if p.is_file() and p!=archive and p.suffix!='.zip':z.write(p,'private-aux/'+p.name)
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0')
assert all(not p or p.startswith(prefix+'/') for p in staged),staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: preserve APPT pure envelope and last-boundary author proofs'],check=True)
head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'head':head,'status':status,'boundary_paper':boundarymeta,
 'dirty_archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size},
 'manifest_files':len(manifest),'manifest_sha256':sha(folder/'CHECKPOINT_FILE_MANIFEST.json'),
 'no_push':True,'root_merge':False,'old_phases_unchanged':True}
dump(aux/f'checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
