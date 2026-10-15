"""Guarded ordinary-source commit; no merge or push, no formal execution."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,tarfile,xml.etree.ElementTree as ET

stage=Path(__file__).resolve().parent
root=Path('/home/mxym/math-appt-multiscale-20261013')
rec=json.loads((stage/'INTEGRATION_RECEIPT.json').read_text())
def git(*a):return subprocess.check_output(['git','-C',str(root),*a])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if (stage/'COMMIT_RECEIPT.json').exists():raise RuntimeError('Already committed; do not duplicate')
if git('rev-parse','HEAD').decode().strip()!=rec['base']:raise RuntimeError('Unexpected HEAD')
staged=set(git('diff','--cached','--name-only').decode().splitlines())
for rel,h in {**rec['protected_files'],**rec['new_files_and_indices']}.items():
 if sha(root/rel)!=h:raise RuntimeError('Changed bound bytes '+rel)
files=list(rec['new_files_and_indices'])
allowed=set(files)
if staged and staged!=allowed:raise RuntimeError('Unexpected existing staged work')
dirty=git('status','--porcelain','--untracked-files=all').decode().splitlines()
visible={row[3:] for row in dirty}
if visible-allowed:raise RuntimeError('Unexpected dirty root source')
ignored=sorted(allowed-visible)
for rel in ignored:
 q=subprocess.run(['git','-C',str(root),'check-ignore','--quiet','--',rel])
 if q.returncode or not (root/rel).is_file():raise RuntimeError('Unexplained absent dirty source '+rel)
with tarfile.open(stage/'precommit-all-new-sources.tar.gz','w:gz') as tar:
 for rel in files:tar.add(root/rel,arcname=rel,recursive=False)
subprocess.run(['git','-C',str(root),'add','--',*[f for f in files if f not in ignored]],check=True)
if ignored:subprocess.run(['git','-C',str(root),'add','--force','--',*ignored],check=True)
if set(git('diff','--cached','--name-only').decode().splitlines())!=allowed:raise RuntimeError('Index set differs')
for rel in files:
 if rel.endswith('.log'):
  for line in (root/rel).read_bytes().splitlines():
   if line.endswith((b' ',b'\t')):raise RuntimeError('Non-CR trailing whitespace in raw log '+rel)
# Matplotlib emits legal trailing path-data whitespace. Keep reviewed SVG bytes;
# validate their XML and exact provenance, then check all canonical prose/code.
svg_files=[rel for rel in files if rel.endswith('.svg')]
provenance=json.loads((root/'research/appt-coupled-order-window-20261015/figures/PROVENANCE.json').read_text())
for rel in svg_files:
 if sha(root/rel)!=provenance['files']['coupled-transition.svg']:
  raise RuntimeError('Generated SVG differs from reviewed provenance '+rel)
 if ET.parse(root/rel).getroot().tag!='{http://www.w3.org/2000/svg}svg':
  raise RuntimeError('Invalid SVG root '+rel)
if svg_files:
 svg_check=subprocess.run(['git','-C',str(root),'-c','core.whitespace=-blank-at-eol,space-before-tab,blank-at-eof',
                          'diff','--cached','--check','--',*svg_files],capture_output=True)
 (stage/'GENERATED_SVG_CHECK.log').write_bytes(svg_check.stdout+svg_check.stderr)
 if svg_check.returncode:raise RuntimeError('Generated SVG syntax/whitespace check failed')
else:
 (stage/'GENERATED_SVG_CHECK.log').write_text('No new SVG files; no empty-pathspec check run.\n')
check1=subprocess.run(['git','-C',str(root),'-c','core.whitespace=trailing-space,space-before-tab,cr-at-eol',
                       'diff','--cached','--check','--','.',':(exclude)**/*.diff',':(exclude)**/*.svg'],capture_output=True)
(stage/'CANONICAL_DIFF_CHECK.log').write_bytes(check1.stdout+check1.stderr)
if check1.returncode:raise RuntimeError('Canonical whitespace check failed; retain output')
diffs=[f for f in files if f.endswith('.diff')]
for rel in diffs:
 for line in (root/rel).read_text().splitlines():
  if line.endswith((' ','\t')) and line!=' ':raise RuntimeError('Non-context trailing whitespace '+rel)
check2=subprocess.run(['git','-C',str(root),'-c','core.whitespace=-blank-at-eol,space-before-tab,-blank-at-eof',
                       'diff','--cached','--check','--',*diffs],capture_output=True)
(stage/'INTRINSIC_CONTEXT_DIFF_CHECK.log').write_bytes(check2.stdout+check2.stderr)
if check2.returncode:raise RuntimeError('Exact status diff artifact check failed')
(stage/'precommit-index.patch').write_bytes(git('diff','--cached','--binary'))
commit_process=subprocess.run(['git','-C',str(root),'-c','user.name=Yongxian Zhang','-c','user.email=mxymmxym1@gmail.com',
                'commit','-m','research: classify the full APPT linear-order scalar phase diagram'],capture_output=True)
(stage/'GIT_COMMIT_OUTPUT.log').write_bytes(commit_process.stdout+commit_process.stderr)
if commit_process.returncode:raise RuntimeError('Git commit failed; exact output retained')
head=git('rev-parse','HEAD').decode().strip()
if git('status','--porcelain').strip():raise RuntimeError('Unexpected dirty root after commit')
for rel,h in {**rec['protected_files'],**rec['new_files_and_indices']}.items():
 if sha(root/rel)!=h:raise RuntimeError('Bytes changed after commit '+rel)
result={'utc':datetime.now(timezone.utc).isoformat(),'base':rec['base'],'source_commit':head,
        'root_clean':True,'new_files_and_indices':len(files),'protected_previous_files':len(rec['protected_files']),
        'independent_ordinary_targets':['last-mixed-boundary','no-islands','critical-uniqueness','global-mixed-phase'],'new_Lean':False,'new_audit_roots':0,
        'new_major_conjecture_count':0,'force_push':False,'published_yet':False}
(stage/'COMMIT_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
