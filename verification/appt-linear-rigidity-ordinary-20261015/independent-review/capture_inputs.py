from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess

base=Path(__file__).resolve().parent
source=base.parent/'linear-critical-rigidity'
snap=base/'snapshot';snap.mkdir(parents=True,exist_ok=True)
files={}
def copy(p,relative):
    data=p.read_bytes();target=snap/relative;target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert target.read_bytes()==data,str(relative)
    else:target.write_bytes(data)
    files[str(relative)]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'lines':len(data.splitlines())}
for name in ['PAPER.md','THEOREM_MAP.md','checks.py','CREDITED_INPUTS.json','LITERATURE_SCREEN.md','RESEARCH_LOG.md']:
    copy(source/name,Path(name))
assert files['PAPER.md']['sha256']=='e9ba9730c6fd7ed8ac4fbae264e1ef2f86e0d148e93155acdd33be3704dbc5b2'
assert files['THEOREM_MAP.md']['sha256']=='61107598bba868585a62bc3b237b84815cb0852832f26ba96b537873562d8199'
credit=json.loads((source/'CREDITED_INPUTS.json').read_text())
root=Path('/home/mxym/math-appt-multiscale-20261013')
for name,row in credit['files'].items():
    p=source/'credited-inputs'/name
    data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==row['sha256'],name
    assert subprocess.check_output(['git','-C',str(root),'show',credit['head']+':'+name])==data,name
    copy(p,Path('credited-inputs')/name)
run=source/'control-runs/20261015T102144.614697Z'
for p in sorted(run.iterdir()):
    if p.is_file():copy(p,p.relative_to(source))
result={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'source':str(source),'files':files,'credited_commit':credit['head'],'credited7_match_immutable_commit':True,'author_code_executed':False,'Lean':False,'private_only':True}
(base/'INPUT_MANIFEST.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','files':len(files),'paper':files['PAPER.md'],'credited':len(credit['files'])}))
