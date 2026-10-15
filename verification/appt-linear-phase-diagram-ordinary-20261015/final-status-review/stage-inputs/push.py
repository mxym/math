"""Only an ordinary fast-forward push after literal checked-source readback."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,subprocess
git=Path(r'D:\Git\cmd\git.exe');bare=Path(r'D:\math\tmp\aixiv-20261013\git-transport.git')
stage=Path(__file__).resolve().parent
os.environ['GCM_INTERACTIVE']='never';os.environ['GIT_TERMINAL_PROMPT']='0'
def run(args,input=None):
 p=subprocess.run([str(git),'-C',str(bare),'-c','gc.auto=0',*args],input=input,capture_output=True,timeout=60)
 if p.returncode:raise RuntimeError(p.stderr.decode(errors='replace'))
 return p.stdout
if (stage/'PUSH_RECEIPT.json').exists():raise RuntimeError('Already pushed; do not duplicate')
binding=json.loads((stage/'TRANSPORT_BINDINGS.json').read_text())
run(['fetch','origin','refs/heads/main:refs/heads/main'])
base=run(['rev-parse','refs/heads/main']).decode().strip()
if base!=binding['previous_main']:raise RuntimeError('Parallel main changed; preserve and merge before any push')
run(['fetch',str(stage/'research-proof.bundle'),'HEAD:refs/heads/research-linear-phase-diagram-reviewed-20261015'])
head=run(['rev-parse','refs/heads/research-linear-phase-diagram-reviewed-20261015']).decode().strip()
if head!=binding['head']:raise RuntimeError('Transport commit differs')
run(['merge-base','--is-ancestor',base,head])
run(['index-pack','--stdin'],input=(stage/'checked-public-inputs.pack').read_bytes())
names=list(binding['files']);stream=run(['cat-file','--batch'],input=''.join(head+':'+rel+'\n' for rel in names).encode())
offset=0
for rel in names:
 end=stream.index(b'\n',offset);hdr=stream[offset:end].split()
 if len(hdr)!=3 or hdr[1]!=b'blob':raise RuntimeError('Transport source missing '+rel)
 size=int(hdr[2]);start=end+1;blob=stream[start:start+size];offset=start+size+1
 if hashlib.sha256(blob).hexdigest()!=binding['files'][rel]:raise RuntimeError('Transport source mismatch '+rel)
run(['push','origin','refs/heads/research-linear-phase-diagram-reviewed-20261015:refs/heads/main'])
remote=run(['ls-remote','origin','refs/heads/main']).decode().split()[0]
if remote!=head:raise RuntimeError('Remote readback differs')
receipt={'utc':datetime.now(timezone.utc).isoformat(),'source_commit':head,'previous_main':base,
         'remote_main_readback':remote,'fast_forward':True,'force_push':False,
         'transported_bound_files_checked':len(names),'old_protected_files_literal_matched':binding['prior_protected_files'],
         'new_Lean':False,'new_audit_roots':0,'Gaussian_original_dirty_files_matched':27,
         'aixiv_submissions':0,'emails':0,'new_releases':0,'doi':None,'status':'PUSHED_AND_REMOTE_VERIFIED'}
(stage/'PUSH_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
