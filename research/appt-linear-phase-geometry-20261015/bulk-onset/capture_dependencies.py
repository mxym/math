"""Capture exact credited local mathematical sources, without running them."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil
out=Path(__file__).resolve().parent
companion=out.parent/'scalar-phase-geometry-20261015'
review=out.parent/'independent-scalar-phase-review'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((companion/'CREDITED_INPUTS.json').read_text())
rows=[]
for row in old['files']:
 src=companion/row['copied_path'];dest=out/row['copied_path']
 if sha(src)!=row['sha256']:raise RuntimeError('Credited mathematical copy changed')
 dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():raise RuntimeError('Do not overwrite previous capture')
 shutil.copyfile(src,dest);rows.append(row)
extras=[(companion/'PAPER.md','credited-pole-threshold-v2/PAPER.md',
         '83c2240adfbca39009ff446504cc477f47684a0e5de1db52439862053bbcad79'),
        (review/'REVIEW_V2.md','credited-pole-threshold-v2/REVIEW.md',None),
        (review/'REVIEW_V2.json','credited-pole-threshold-v2/REVIEW.json',None)]
for src,rel,expected in extras:
 if expected and sha(src)!=expected:raise RuntimeError('Pole threshold source is no longer the reviewed v2')
 dest=out/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():raise RuntimeError('Do not overwrite previous capture')
 shutil.copyfile(src,dest)
 rows.append({'source_commit':None,'source_kind':'private independently read unchanged companion v2, before publication',
              'source_path':str(src),'copied_path':rel,'sha256':sha(src),'bytes':src.stat().st_size})
shutil.copyfile(companion/'PRIMARY_SCOPE.json',out/'PRIMARY_SCOPE.json')
record={'utc':datetime.now(timezone.utc).isoformat(),'files':rows,
        'actual_inputs':'old L1/L20-L21 and S; companion global pole-onset T2; V credited as already completed value scope',
        'external_screen':'PRIMARY_SCOPE reused with original checked date/read limits; not a fresh fulltext screen or a priority certificate',
        'new_Lean':False,'new_audit_roots':0}
(out/'CREDITED_INPUTS.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'captured_files':len(rows),'companion_original_math_source':extras[0][2]}))
