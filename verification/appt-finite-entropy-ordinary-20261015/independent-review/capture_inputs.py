from pathlib import Path
import hashlib,json,subprocess,datetime,shutil

source=Path('/mnt/d/math/tmp/research-resume-20261015/all-aspect-all-orders')
dest=Path(__file__).resolve().parent
snap=dest/'snapshot';snap.mkdir(parents=True,exist_ok=True)
digest=lambda data:hashlib.sha256(data).hexdigest()
names=['PAPER.md','THEOREM_MAP.md','checks.py','LITERATURE_SCREEN.md','RESEARCH_LOG.md','CREDITED_INPUTS.json','LOCAL_PRIOR_WORK_SCOPE_CORRECTION.diff','requirements.txt']
files={}
for name in names:
    data=(source/name).read_bytes();target=snap/name
    if target.exists():assert target.read_bytes()==data,name
    else:target.write_bytes(data)
    files[name]={'sha256':digest(data),'bytes':len(data),'lines':len(data.splitlines())}
assert files['PAPER.md']['sha256']=='296b66adc5939942366d47c2f2193d1eb07a62d982f0d4c25add8d2b0e7d9f29'
assert files['THEOREM_MAP.md']['sha256']=='f1c816dfe062e796acf22680395130b1a1d03f52fa06de6db04282fe06b18f80'
credit=json.loads((source/'CREDITED_INPUTS.json').read_text())
root=Path('/home/mxym/math-appt-multiscale-20261013')
for name,row in credit['files'].items():
    data=(source/'credited-inputs'/name).read_bytes()
    assert digest(data)==row['sha256'] and len(data)==row['bytes'],name
    assert subprocess.check_output(['git','-C',str(root),'show',credit['source_commit']+':'+name])==data,name
    target=snap/'credited-inputs'/name;target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert target.read_bytes()==data,name
    else:target.write_bytes(data)
    files['credited-inputs/'+name]={'sha256':digest(data),'bytes':len(data),'lines':len(data.splitlines()),'commit':credit['source_commit']}
for src in [source/'author-versions/before-local-prior-work-correction',source/'control-runs/20261015T095157.902301Z']:
    for p in sorted(src.rglob('*')):
        if not p.is_file():continue
        rel=p.relative_to(source);target=snap/rel;target.parent.mkdir(parents=True,exist_ok=True)
        data=p.read_bytes()
        if target.exists():assert target.read_bytes()==data,str(rel)
        else:target.write_bytes(data)
        files[str(rel)]={'sha256':digest(data),'bytes':len(data),'lines':len(data.splitlines())}
manifest={'status':'PASS','captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':str(source),'files':files,'credited_commit':credit['source_commit'],'author_code_executed':False,'private_only':True,'Lean':False}
(dest/'INPUT_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':'PASS','files':len(files),'paper_sha256':files['PAPER.md']['sha256'],'credited_sources':len(credit['files'])}))
