from pathlib import Path
import datetime as dt
import hashlib
import json
import shutil
import subprocess
import zipfile

repo=Path('/home/mxym/math-breadth-tcs-20261015')
prefix='research/breadth-tcs-20261015/phase-5-sublinear-rigidity'
folder=repo/prefix
aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015/phase-5-sublinear-rigidity')
now=dt.datetime.now(dt.timezone.utc)
tag=now.strftime('%Y%m%dT%H%M%SZ')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
assert head=='336212bfe804e0770fe847073f2932bee943d653'
names=['PAPER.md','author_exact_controls.py','AUTHOR_EXACT_CONTROLS.json','README.md',
       'THEOREM_MAP.md','LOCAL_COVERAGE_MAP.md','freeze_author_scope.py']
for name in names:shutil.copyfile(aux/name,folder/name)
controls=json.loads((folder/'AUTHOR_EXACT_CONTROLS.json').read_text())
assert controls['all_requested_assertions_passed'] and controls['finite_cases']==18
assert controls['paper_sha256']==sha(folder/'PAPER.md')
assert controls['source_sha256']==sha(folder/'author_exact_controls.py')
assert sha(folder/'PAPER.md')=='da596b457eb4d2b82a1d231de065d07197def79414be0aaa1c1f069505e8e74b'
ledger={'created_utc':now.isoformat(),'scope':'phase5 only, source-bound full all-aspect sublinear rigidity',
 'mathematical_control_failures':[],
 'actual_nonmathematical_tool_failures':[
  {'kind':'read-only path lookup','utc':'2026-10-15T12:58:49Z',
   'what':'Four shorthand directory paths omitted their date suffix and rg returned path-not-found; dated paths were immediately located with rg --files and scientific texts fully read',
   'mathematical_effect':'None; no source absence was treated as an unsolved mathematical range'},
  {'kind':'apply_patch context mismatch','utc':'2026-10-15T13:16:01Z',
   'what':'Expected a backslash-plus typo in an unfrozen manuscript but actual line was sufficiency,+trace; patch made no changes',
   'actual_error':'apply_patch verification failed: Failed to find expected lines',
   'resolution':'Read actual line with rg, corrected formatting, then created/reran the exact controls; no mathematical finding or failed control was deleted'}],
 'rejected_mathematical_extensions':[
  'Replacing the weighted sum by a branch minimum: actual balanced pole has asymptotic ratio1/2',
  'Deleting J: actual three-level operator-interval APPT family has L2,theta1/2 but J1/2 and ratio1/2',
  'Demanding unweighted Q/gamma1 when bulk weight vanishes: square physical pole has Q/gamma4 and can be sharp',
  'Taking a log of a coarse o(U+V) all-state error in the high-chi entropy proof: replaced by physical y1->3 necessity and stronger state-relative reduction',
  'Dropping the exact actual-middle mean term: finite rational control rejects it'],
 'author_controls':'18 exact Fraction/integer physical regressions passed; no independent review implied',
 'scope_status':'Complete author proof; new independent full ordinary read pending; no new Lean or major count'}
dump(folder/'ATTEMPT_LEDGER.json',ledger)
manifest={'frozen_utc':now.isoformat(),'status':'Complete author manuscript, new independent ordinary review pending',
 'owner':'/root/breadth_tcs_resume_20261015 APPT depth role',
 'source_root_commit':'1c76bb8dd03bb622e8ed1eabbe88e8abc5b3e59f',
 'domain':'Every original actual complex all-global-unitary APPT state,2<=m<=n,m->infinity,real alpha->infinity,alpha/m->0,all aspect growth and oscillations',
 'claims':['Weighted-sum sharp moment-EXCESS iff criterion','Distinct relative entropy iff criterion',
           'Retained-bulk actual W2 law equivalence with explicit J','Necessary actual peak/width margin when both weights remain positive'],
 'read_scope_required':['Entire PAPER including all-state identity and weighted overshoot','Actual G physical/value inputs and L7 coupling',
  'J/mean identity and exceptional W2 integrability','chi bounded above and chi->+infinity necessity/sufficiency',
  'All extreme ratios and oscillating paths','Actual counterexample witnesses and all stated remaining limits'],
 'not_dependencies':['Four phase4 scalar manuscripts','Restricted candidate state model','New or enlarged Lean audit'],
 'not_claimed':['All remaining positive-order spectral windows','Fixed-m relative synthesis','External priority or human review','New major-problem count'],
 'reproduction':'Copy PAPER.md and author_exact_controls.py to private scratch, run python author_exact_controls.py there; compare source/paper hashes and exact mathematical rows, UTC may differ',
 'files':[{'path':str(folder/name),'sha256':sha(folder/name),'bytes':(folder/name).stat().st_size}
          for name in names+['SOURCE_INPUTS.json','TARGET.json','PRIMARY_SCREEN.json','ATTEMPT_LEDGER.json','initialize_sublinear_rigidity.py']],
 'credited_inputs':json.loads((folder/'SOURCE_INPUTS.json').read_text())['inputs'],
 'publication':'No root edit, push, index promotion, preprint, release, DOI or email; author-only'}
dump(folder/'AUTHOR_V1_MANIFEST.json',manifest)
for name in names[:-1]:(folder/name).chmod(0o444)
archive=aux/f'sublinear-rigidity-owner-{tag}.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in sorted(folder.rglob('*')):
        if p.is_file():z.write(p,'worktree/'+p.relative_to(repo).as_posix())
subprocess.run(['git','-C',str(repo),'add','--',prefix],check=True)
staged=[p for p in subprocess.check_output(['git','-C',str(repo),'diff','--cached','--name-only','-z']).decode().split('\0') if p]
assert all(p.startswith(prefix+'/') for p in staged),staged
subprocess.run(['git','-C',str(repo),'commit','-m','research: author all-aspect growing-sublinear APPT spectral criteria'],check=True)
newhead=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD']).decode().strip()
status=subprocess.check_output(['git','-C',str(repo),'status','--porcelain=v1']).decode()
result={'utc':now.isoformat(),'head':newhead,'status':status,
 'paper':{'path':str(folder/'PAPER.md'),'sha256':sha(folder/'PAPER.md'),'bytes':(folder/'PAPER.md').stat().st_size},
 'manifest_sha256':sha(folder/'AUTHOR_V1_MANIFEST.json'),
 'controls_sha256':sha(folder/'AUTHOR_EXACT_CONTROLS.json'),
 'archive':{'path':str(archive),'sha256':sha(archive),'bytes':archive.stat().st_size}}
dump(aux/f'checkpoint-{tag}.json',result)
print(json.dumps(result,indent=2,ensure_ascii=False))
