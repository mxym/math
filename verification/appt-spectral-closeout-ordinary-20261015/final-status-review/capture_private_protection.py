"""Read-only protection capture. No protected source bytes are copied."""
from pathlib import Path
import datetime,hashlib,json,subprocess
out=Path(__file__).resolve().parent/'private-protection-evidence'
out.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda p,*args:subprocess.check_output(['git','-C',str(p),*args])
family=Path('/mnt/d/math/handoff/research-20261015-reviewed-continuing')
latest=json.loads((family/'LATEST.json').read_bytes())
statepath=Path(latest['directory'].replace('D:/','/mnt/d/').replace('D:\\','/mnt/d/').replace('\\','/'))/'STATE.json'
raw=statepath.read_bytes();assert sha(raw)==latest['state_sha256']
g=json.loads(raw)['Gaussian'];gp=Path(g['path'])
head=git(gp,'rev-parse','HEAD').decode().strip();status=git(gp,'status','--porcelain').decode()
assert head==g['head'] and status==g['status']
records={}
for rel,expected in g['files'].items():
    b=(gp/rel).read_bytes();assert sha(b)==expected['sha256'],rel
    records[rel]={'sha256':sha(b),'bytes':len(b)}
assert len(records)==27
root=Path('/home/mxym/math-appt-multiscale-20261013')
hn=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015/phase-5-haldane/CLOCK.json')
assert sha(hn.read_bytes())=='d3aab86688c0a69e4cdcaa71f825e1c301017233d9a072adb7c47480af4c6b56'
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'private_only':True,'publication_excluded':True,'state_reference_sha256':sha(raw),'private_state_not_copied':True,'Gaussian':{'path':str(gp),'head':head,'status':status,'files':records,'read_only_hash_checks':True,'source_bytes_not_copied':True},'HN0_clock_sha256':sha(hn.read_bytes()),'HN0_effective_seconds':3965.905531,'HN0_status':'paused','root_head':git(root,'rev-parse','HEAD').decode().strip(),'root_status':git(root,'status','--porcelain').decode(),'formalizations_tree_oid':git(root,'rev-parse','HEAD:formalizations').decode().strip(),'Lean_execution_or_audit':False}
name=datetime.datetime.now(datetime.timezone.utc).strftime('PROTECTION-%Y%m%dT%H%M%S.%fZ.json')
(out/name).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'private_protection_record':str(out/name),'Gaussian_files_hash_status_matched':len(records),'Gaussian_source_bytes_copied':False,'full_STATE_copied':False,'HN0':'paused, clock unchanged','Lean_executed':False}))
