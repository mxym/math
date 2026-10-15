from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess
import zipfile

repo=Path('/home/mxym/math-breadth-tcs-20261015')
prefix='research/breadth-tcs-20261015/phase-6-growing-peak-rigidity'
folder=repo/prefix
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-6-growing-peak-rigidity')
now=dt.datetime.now(dt.timezone.utc)
tag=now.strftime('%Y%m%dT%H%M%SZ')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
oldhead=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
assert oldhead=='cf01a57b7f0b3a153b36e1961e4575f0f66d18d7'
for name in ['README.md','THEOREM_MAP.md','freeze_peak_scope.py']:
    shutil.copyfile(aux/name,folder/name)
controls=json.loads((folder/'AUTHOR_EXACT_CONTROLS.json').read_text())
assert controls['all_requested_assertions_passed'] and controls['finite_cases']==21
assert controls['paper_sha256']==sha(folder/'PAPER.md')
assert controls['source_sha256']==sha(folder/'author_peak_controls.py')
assert sha(folder/'PAPER.md')=='2374564f1f2cd3c576c3528d8acfda3f9a729ae08f506621f930ed42b33fd227'
before=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1','-uall']).decode()
for line in before.splitlines():
    assert line[3:].startswith(prefix+'/'),line
manifest={'frozen_utc':now.isoformat(),'status':'Complete author manuscript; distinct independent ordinary review pending',
 'owner':'/root/breadth_tcs_resume_20261015 APPT depth role',
 'source_root_commit':'1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f',
 'domain':'For every fixed C>0 all actual original complex all-global-unitary APPT density sequences,2<=m<=n,m->infinity,real alpha->infinity,alpha<=Cm,chi=alpha logu_D-logD->+infinity',
 'claims':['Uniform actual-state peak moment profile','Sharp moment/excess iff h->0','Relative entropy deficit iff h/chi->0','Actual whole-tail flatness, second-peak power decay and entire moment concentration in the physical peak'],
 'read_scope_required':['Complete PAPER including original quantifiers and exact centering','Credited G physical source input range','Uniform all-state bounds with arbitrary n','Entropy necessity before logarithmic profile','chi/alpha->0 and arbitrary bounded order-ratio oscillation','Whole tail energy versus mere second-peak bound','Actual examples and no extrapolation of S finite-r losses'],
 'not_dependencies':['Pending phase5 sublinear rigidity','Phase4 scalar geometry','Restricted candidate spectral model','New Lean or expanded old audit'],
 'not_claimed':['Entire diverging-alpha assembly','Exact finite maximum or optimizers','Historical-first or external human review','New major-problem resolution'],
 'reproduction':'Copy PAPER and author_peak_controls.py to a private scratch, run python3 author_peak_controls.py; compare exact mathematical rows/source hashes, allow new UTC; never overwrite frozen evidence',
 'files':[{'path':p.relative_to(folder).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size}
          for p in sorted(folder.rglob('*')) if p.is_file()],
 'publication':'No root edits, push, public indices, preprint, release, DOI or external messages; author-only'}
dump(folder/'AUTHOR_V1_MANIFEST.json',manifest)
for p in folder.rglob('*'):
    if p.is_file():p.chmod(0o444)
archive=aux/f'peak-rigidity-owner-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=[p for p in subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0') if p]
assert all(p.startswith(prefix+'/') for p in staged),staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: author growing-peak APPT actual spectral criteria'],check=True)
newhead=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'parent_head':oldhead,'head':newhead,'status':status,
 'paper':{'path':str(folder/'PAPER.md'),'sha256':sha(folder/'PAPER.md'),'bytes':(folder/'PAPER.md').stat().st_size},
 'manifest_sha256':sha(folder/'AUTHOR_V1_MANIFEST.json'),
 'controls_sha256':sha(folder/'AUTHOR_EXACT_CONTROLS.json'),
 'archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size}}
dump(aux/f'checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
