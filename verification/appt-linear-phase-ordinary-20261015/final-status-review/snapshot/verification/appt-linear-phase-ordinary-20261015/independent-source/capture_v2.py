from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess

base=Path(__file__).resolve().parent;source=base.parent/'scalar-phase-geometry-20261015'
snapshot=base/'snapshot-v2';snapshot.mkdir(parents=True,exist_ok=True)
files={}
for p in sorted(source.rglob('*')):
    if not p.is_file():continue
    rel=p.relative_to(source);data=p.read_bytes();target=snapshot/rel;target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert target.read_bytes()==data,str(rel)
    else:target.write_bytes(data)
    files[str(rel)]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'lines':len(data.splitlines())}
assert files['PAPER.md']['sha256']=='83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79'
assert (snapshot/'author-versions/v1-before-alpha-domain-finding/PAPER.md').read_bytes()==(base/'snapshot-v1/PAPER.md').read_bytes()
credit=json.loads((snapshot/'CREDITED_INPUTS.json').read_text())
for row in credit['files']:
    p=snapshot/row['copied_path'];data=p.read_bytes()
    assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
    assert data==subprocess.check_output(['git','-C','/home/mxym/math-appt-multiscale-20261013','show',row['source_commit']+':'+row['repository_path']])
manifest={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'files':files,'source':str(source),'credited8_match_immutable_main':True,'author_code_executed':False,'author_FAIL_and_PASS_preserved_as_author_evidence':True,'source_hypothesis':'Original T5 c>=10 only; no oral c>=1 strengthening certified'}
(base/'INPUT_V2.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':'PASS','files':len(files),'paper':files['PAPER.md'],'credited_sources':len(credit['files'])}))
