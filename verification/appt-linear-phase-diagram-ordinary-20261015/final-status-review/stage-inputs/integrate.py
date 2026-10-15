"""Preserve then integrate independently read scalar coexistence corpus, without merge/publication."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,tarfile,shutil,re

root=Path('/home/mxym/math-appt-multiscale-20261013')
stage=Path(__file__).resolve().parent;public=stage/'public-sources'
base='1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f'
prior=stage.parent/'scalar-phase-publication'/'TRANSPORT_BINDINGS.json'
pause=Path('/mnt/d/math/handoff/research-20261015-root-only-paused/STATE.json')
def git(p,*a,**kw):return subprocess.check_output(['git','-C',str(p),*a],**kw)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ancestor(a,b):return subprocess.run(['git','-C',str(root),'merge-base','--is-ancestor',a,b]).returncode==0
if (stage/'INTEGRATION_RECEIPT.json').exists():raise RuntimeError('Already integrated; no duplicate operation')
if git(root,'rev-parse','HEAD').decode().strip()!=base:raise RuntimeError('Unexpected root head')
recovering=bool(git(root,'status','--porcelain').strip())
old=json.loads(prior.read_text());gpdata=json.loads(pause.read_text())['Gaussian'];gp=Path(gpdata['path'])
if git(gp,'rev-parse','HEAD').decode().strip()!=gpdata['head'] or git(gp,'status','--porcelain').decode()!=gpdata['status']:raise RuntimeError('Gaussian status/head changed')
for rel,v in gpdata['files'].items():
 if sha(gp/rel)!=v['sha256']:raise RuntimeError('Gaussian bytes changed '+rel)
for rel,h in old['files'].items():
 if recovering and rel in ['README.md','README.en.md','RESEARCH.md','SOLVED_PROBLEMS.md']:continue
 if sha(root/rel)!=h:raise RuntimeError('Previously bound source differs '+rel)
projects=[p for p in sorted(public.iterdir()) if p.is_dir()]
dest={p.name:('verification/'+p.name if p.name.endswith('ordinary-20261015') else 'research/'+p.name) for p in projects}
for p in projects:
 if (root/dest[p.name]).exists() and not recovering:raise RuntimeError('New project destination exists '+p.name)
 if recovering:
  if not (stage/'integration-first-check-failure'/'FAILURE.json').is_file():raise RuntimeError('Unexplained dirty root')
  actual={str(f.relative_to(root/dest[p.name])):sha(f) for f in (root/dest[p.name]).rglob('*') if f.is_file()}
  expected={str(f.relative_to(p)):sha(f) for f in p.rglob('*') if f.is_file()}
  if actual!=expected:raise RuntimeError('Partial copied project differs '+p.name)
 if not p.name.endswith('ordinary-20261015'):
  binding=json.loads((p/'FINAL_STATUS_BINDING.json').read_text())
  if binding.get('status',binding.get('decision'))!='PASS':raise RuntimeError('Final binding incomplete '+p.name)
  if p.name=='research-attempts-20261015':
   if json.loads((p/'PROJECT_KIND.json').read_text()).get('kind')!='research-attempt catalog':raise RuntimeError('Wrong catalog kind')
  elif not (p/'REVIEW.json').is_file():raise RuntimeError('Missing full independent read')
index=json.loads((stage/'index-candidates'/'INDEX_BINDINGS.json').read_text())
for name,v in index.items():
 if sha(root/name)!=(v['after_sha256'] if recovering else v['before_sha256']) or sha(stage/'index-candidates'/name)!=v['after_sha256']:
  raise RuntimeError('Changed index proposal '+name)
if not recovering:
 with tarfile.open(stage/'pre-integration-all-reviewed-and-Gaussian.tar.gz','w:gz') as tar:
  tar.add(public,arcname='public-sources')
  tar.add(stage/'index-candidates',arcname='index-candidates')
  for rel in gpdata['files']:tar.add(gp/rel,arcname='Gaussian/'+rel,recursive=False)
  for name in index:tar.add(root/name,arcname='root-before/'+name,recursive=False)
 (stage/'Gaussian-before-integration-tracked.patch').write_bytes(git(gp,'diff','--binary','HEAD'))
 (stage/'Gaussian-before-integration-index.patch').write_bytes(git(gp,'diff','--cached','--binary'))
 for p in projects:
  shutil.copytree(p,root/dest[p.name])
  for f in (root/dest[p.name]).rglob('*'):
   if f.is_file():f.chmod(0o644)
 for name in index:shutil.copyfile(stage/'index-candidates'/name,root/name)
else:
 for row in git(root,'status','--porcelain','--untracked-files=all').decode().splitlines():
  rel=row[3:]
  if rel not in index and not any(rel.startswith(v+'/') for v in dest.values()):raise RuntimeError('Unexpected dirty source '+rel)
protected={rel:h for rel,h in old['files'].items() if rel not in index}
for rel,h in protected.items():
 if sha(root/rel)!=h:raise RuntimeError('Protected input changed after integration '+rel)
files={}
for p in projects:
 for f in sorted((root/dest[p.name]).rglob('*')):
  if f.is_file():files[str(f.relative_to(root))]=sha(f)
for name in index:files[name]=sha(root/name)
# Check all ordinary project-internal Markdown references, excluding historical
# source snapshots, whose relative paths intentionally describe their old context.
skip_parts={'control-runs','global-control-runs','runs','snapshot','snapshots','snapshot-v1','snapshot-v2','snapshot-v3','initial-snapshot','credited-inputs','additional-reused-inputs','history','author-versions','entropy-review-input-v2','index-candidates','final-source-snapshots','readme-organization-history','completed-v2','credited-pole-threshold-v2','final-status-review','author-snapshot','index-before','owner-zip-snapshot'}
checked=0
for rel in files:
 f=root/rel
 if f.suffix!='.md' or any(part in skip_parts for part in Path(rel).parts):continue
 # The bound plain-text mathematical notation M_[1/2,2](m) denotes the
 # interval-indexed onset, not a file reference. Do not mutate reviewed
 # source bytes merely to work around this narrow link-regex ambiguity.
 markdown=f.read_text().replace('M_[1/2,2](m)','M_interval(m)')
 for link in re.findall(r'\]\(([^)]+)\)',markdown):
  if '://' in link or link.startswith('#') or link.startswith('mailto:'):continue
  target=link.split('#')[0]
  if not target:continue
  if not (f.parent/target).exists():raise RuntimeError('Missing local link '+rel+' -> '+target)
  checked+=1
for commit in ['830a7f6c40d37d6005755fc04b1bf20ea834c137','cb81f0fa1f82028c148c317c61b2ebfa786809ea','07a7e833b496d679482aaebf015c0e5f46fb956c']:
 if not ancestor(commit,base):raise RuntimeError('Parallel main ancestry missing')
rec={'utc':datetime.now(timezone.utc).isoformat(),'base':base,'new_files_and_indices':files,
     'protected_files':protected,'projects':dest,'Gaussian_original_matched':len(gpdata['files']),
     'local_links_checked':checked,'new_Lean':False,'new_audit_roots':0,
     'independently_read_ordinary_targets':['last-mixed-boundary','no-islands','critical-uniqueness','global-mixed-phase'],
     'old_bindings_metadata':{k:v for k,v in old.items() if k!='files'}}
(stage/'INTEGRATION_RECEIPT.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({'integrated_files_and_indices':len(files),'protected_previous_files':len(protected),
                  'local_links_checked':checked,'Gaussian_files_unchanged':len(gpdata['files']),
                  'new_Lean':False,'old_audit_unchanged':True}))
