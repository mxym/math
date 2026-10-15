"""Bind the committed bytes, make a reproducible artifact and Git transport."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,zipfile
stage=Path(__file__).resolve().parent;root=Path('/home/mxym/math-appt-multiscale-20261013')
integration=json.loads((stage/'INTEGRATION_RECEIPT.json').read_text())
commit=json.loads((stage/'COMMIT_RECEIPT.json').read_text())
def git(*a,**kw):return subprocess.check_output(['git','-C',str(root),*a],**kw)
head=git('rev-parse','HEAD').decode().strip()
if head!=commit['source_commit'] or git('status','--porcelain').strip():raise RuntimeError('Changed source tree')
if (stage/'TRANSPORT_BINDINGS.json').exists():raise RuntimeError('Transport already prepared')
files={**integration['protected_files'],**integration['new_files_and_indices']}
for rel,h in files.items():
 if hashlib.sha256(git('show',head+':'+rel)).hexdigest()!=h:raise RuntimeError('Committed source differs '+rel)
objects=[git('rev-parse',head+':'+rel).decode().strip() for rel in files]
pack=git('pack-objects','--stdout',input=('\n'.join(sorted(set(objects)))+'\n').encode())
(stage/'checked-public-inputs.pack').write_bytes(pack)
git('bundle','create',str(stage/'research-proof.bundle'),'HEAD','^'+commit['base'])
binding={'head':head,'previous_main':commit['base'],'files':files,
         'independent_ordinary_targets':['last-mixed-boundary','no-islands','critical-uniqueness','global-mixed-phase'],
         'prior_protected_files':len(integration['protected_files']),
         'Gaussian_original_dirty_files_matched':27,'new_Lean':False,'new_audit_roots':0,
         'no_new_major_count':True,'parallel_ancestry':['830a7f6c40d37d6005755fc04b1bf20ea834c137',
          'cb81f0fa1f82028c148c317c61b2ebfa786809ea','07a7e833b496d679482aaebf015c0e5f46fb956c']}
(stage/'TRANSPORT_BINDINGS.json').write_text(json.dumps(binding,indent=2)+'\n')
artifact=Path('/mnt/d/math/output/research/appt-linear-phase-diagram-reviewed-20261015-source.zip')
if artifact.exists():raise RuntimeError('Do not overwrite source artifact')
artifact.parent.mkdir(parents=True,exist_ok=True)
meta={'source_commit':head,'base_commit':commit['base'],'files':files,
      'kind':'complete all-c/all-r linear-order APPT scalar phase diagram and original fixed-c spectral transfer; four separately source-bound internal AI-agent reads and two exact integer certificates; no new formal audit',
      'new_Lean':False,'new_audit_roots':0,'external_human_peer_review':False,
      'new_major_conjecture_count':0,'source_bundle_sha256':hashlib.sha256((stage/'research-proof.bundle').read_bytes()).hexdigest()}
with zipfile.ZipFile(artifact,'x',compression=zipfile.ZIP_DEFLATED) as z:
 for rel in files:z.writestr(rel,git('show',head+':'+rel))
 z.writestr('ARTIFACT.json',json.dumps(meta,indent=2)+'\n')
receipt={'utc':datetime.now(timezone.utc).isoformat(),'source_commit':head,
         'path':'D:/math/output/research/'+artifact.name,'sha256':hashlib.sha256(artifact.read_bytes()).hexdigest(),
         'bound_files':len(files),'committed_blob_hashes_all_matched':True,'published_yet':False}
(stage/'ARTIFACT_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
