"""Freeze the author's stronger cutoff theorem, with all earlier inputs retained."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, difflib

HERE=Path(__file__).resolve().parent
AUTHOR=HERE.parent/'growing-renyi-order'
manifest=json.loads((HERE/'INPUT_MANIFEST.json').read_text())
old_manifest=HERE/'history'/'corrected-v2-INPUT_MANIFEST.json'
if not old_manifest.exists():old_manifest.write_bytes((HERE/'INPUT_MANIFEST.json').read_bytes())

def copy(source,relative):
    data=source.read_bytes();target=HERE/relative
    if target.exists():assert target.read_bytes()==data,str(target)
    else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
    manifest['files'][relative]={'source':str(source),'sha256':hashlib.sha256(data).hexdigest(),
        'bytes':len(data),'lines':len(data.splitlines())}

for name in ['PAPER.md','THEOREM_MAP.md','REVIEW_HISTORY.md','checks.py']:
    copy(AUTHOR/name,'snapshot/P-v3/'+name)
    prior=AUTHOR/'author-versions'/'before-sharper-upper-rate'/name
    copy(prior,'author-versions/before-sharper-upper-rate/'+name)
    assert prior.read_bytes()==(HERE/'snapshot'/'P-v2'/name).read_bytes(),name
    old=(HERE/'snapshot'/'P-v2'/name).read_text().splitlines(True)
    new=(HERE/'snapshot'/'P-v3'/name).read_text().splitlines(True)
    difference=''.join(difflib.unified_diff(old,new,fromfile='v2/'+name,tofile='v3/'+name))
    (HERE/'history'/('upper-strengthening-'+name+'.diff')).write_text(difference)
folder=AUTHOR/'control-runs'/'20261015T091342.637637Z'
for path in folder.iterdir():
    if path.is_file():copy(path,'author-evidence/'+folder.name+'/'+path.name)
result=json.loads((folder/'RESULT.json').read_text());assert result['status']=='PASS'
for name,digest in result['source_sha256'].items():
    assert hashlib.sha256((folder/name).read_bytes()).hexdigest()==digest
assert manifest['files']['snapshot/P-v3/PAPER.md']['sha256']=='3d038944ad35c16fb1c3c99db4fcc096f3a12e543016048a002c035712516e06'
assert (HERE/'snapshot/P-v2/PAPER.md').read_text().split('**P2.**',1)[1]==(HERE/'snapshot/P-v3/PAPER.md').read_text().split('**P2.**',1)[1]
manifest['strengthened_source_captured_utc']=datetime.now(timezone.utc).isoformat()
(HERE/'INPUT_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'final_inputs':{n:manifest['files']['snapshot/P-v3/'+n] for n in ['PAPER.md','THEOREM_MAP.md','REVIEW_HISTORY.md','checks.py']},
    'files':len(manifest['files']),'P2_v2_bytes_retained':True,'author_controls_run':False}))
