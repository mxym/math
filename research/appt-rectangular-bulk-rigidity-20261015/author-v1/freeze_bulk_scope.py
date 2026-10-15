from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess
import zipfile

repo=Path('/home/mxym/math-breadth-tcs-20261015')
prefix='research/breadth-tcs-20261015/phase-7-rectangular-bulk-rigidity'
folder=repo/prefix
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-7-rectangular-bulk-rigidity')
now=dt.datetime.now(dt.timezone.utc);tag=now.strftime('%Y%m%dT%H%M%SZ')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
oldhead=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
assert oldhead=='a61c599a7ecb575c214afc9dac735acd8cce7e55'
for name in ['README.md','THEOREM_MAP.md','freeze_bulk_scope.py']:
    shutil.copyfile(aux/name,folder/name)
controls=json.loads((folder/'AUTHOR_EXACT_CONTROLS.json').read_text())
assert controls['all_requested_assertions_passed'] and controls['finite_cases']==12
assert controls['paper_sha256']==sha(folder/'PAPER.md')
assert controls['source_sha256']==sha(folder/'author_bulk_controls.py')
assert sha(folder/'PAPER.md')=='3701fa925c3c4098961c227768f62915e9cf388bdafea5918a638ce2b7963a9f'
before=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1','-uall']).decode()
for line in before.splitlines():assert line[3:].startswith(prefix+'/'),line
manifest={'frozen_utc':now.isoformat(),'status':'Complete ordinary author manuscript; distinct independent full review pending',
 'owner':'/root/breadth_tcs_resume_20261015 APPT depth role',
 'source_root_commit':'1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f',
 'domain':'Each fixed finiteA, every actual original complex all-global-unitary APPT density,2<=m<=n,m->infinity,real0<alpha<=A,alpha gamma->infinity; arbitraryalpha/noscillation',
 'claims':['Uniform per-actual-state entropy profile with joint-scale rate','Actual full empirical W2 rigidity iff criterion','Fourth-root W2 stability','Optimal exponent with exact integer-rank actual APPT spectra and joint-scale entropy error'],
 'read_scope_required':['Entire PAPER and original all-global-unitary quantifiers','Uniform kernel1/alpha at actual zero eigenvalues','Trace-centered moment/log remainder throughalpha1','Actual projection rank and Schmidt witness sufficiency','Actual J and mean retained','Exceptional quadratic mass forW2','Exact sharpness cost and errorO(l^-4) smaller than gapl^-2','All stated scope exclusions'],
 'not_dependencies':['PendingS5/S6','Phase4 scalar geometry','Root developing fullzero-order path criterion','Restricted spectrum model or enlarged Lean audit'],
 'not_claimed':['All-order/all-aspect spectral synthesis','Exact finite maximum/optimizers','Historical-first or external human peer review','New major-problem count'],
 'reproduction':'Copy PAPER and author_bulk_controls.py to a new private scratch and runpython3; compare source/paperhash and exact mathematical rows, allow new UTC; never overwrite frozen evidence',
 'files':[{'path':p.relative_to(folder).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
          for p in sorted(folder.rglob('*')) if p.is_file()],
 'publication':'No root edit,push,index,release,DOI,preprint or external message; author-only'}
dump(folder/'AUTHOR_V1_MANIFEST.json',manifest)
for p in folder.rglob('*'):
    if p.is_file():p.chmod(0o444)
archive=aux/f'bulk-rigidity-owner-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=[p for p in subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0') if p]
assert all(p.startswith(prefix+'/') for p in staged),staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: author rectangular APPT W2 rigidity and optimal fourth-root stability'],check=True)
newhead=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'parent_head':oldhead,'head':newhead,'status':status,
 'paper':{'path':str(folder/'PAPER.md'),'sha256':sha(folder/'PAPER.md'),'bytes':(folder/'PAPER.md').stat().st_size},
 'manifest_sha256':sha(folder/'AUTHOR_V1_MANIFEST.json'),
 'controls_sha256':sha(folder/'AUTHOR_EXACT_CONTROLS.json'),
 'archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size}}
dump(aux/f'checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
