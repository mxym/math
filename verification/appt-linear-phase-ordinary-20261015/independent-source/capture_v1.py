from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess

base=Path(__file__).resolve().parent
source=base.parent/'scalar-phase-geometry-20261015'
snapshot=base/'snapshot-v1';snapshot.mkdir(parents=True,exist_ok=True)
data=(source/'PAPER.md').read_bytes()
assert len(data)==18203
assert hashlib.sha256(data).hexdigest()=='b270516f97cf719b2e64d4738d328d09d84ac133d8c44cc1620fd1126733e263'
p=snapshot/'PAPER.md'
if p.exists():assert p.read_bytes()==data
else:p.write_bytes(data)
files={'PAPER.md':{'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'lines':len(data.splitlines())}}
commit='c4e0d9e713ba349d376469231789bb7b36915b7d'
root='/home/mxym/math-appt-multiscale-20261013'
paths=['research/appt-growing-renyi/LINEAR_ORDER_VARIATIONAL.md','research/appt-growing-renyi/LINEAR_ORDER_REVIEW.json','research/appt-growing-renyi/ALL_ORDER_VARIATIONAL.md','research/appt-growing-renyi/ALL_ORDER_REVIEW.json','research/appt-linear-critical-rigidity-20261015/PAPER.md','research/appt-linear-critical-rigidity-20261015/THEOREM_MAP.md','research/appt-linear-critical-rigidity-20261015/REVIEW.md','research/appt-linear-critical-rigidity-20261015/REVIEW.json','research/appt-linear-critical-rigidity-20261015/FINAL_STATUS_BINDING.json']
for name in paths:
    content=subprocess.check_output(['git','-C',root,'show',commit+':'+name])
    dest=snapshot/'credited-main'/name;dest.parent.mkdir(parents=True,exist_ok=True)
    if dest.exists():assert dest.read_bytes()==content,name
    else:dest.write_bytes(content)
    files['credited-main/'+name]={'sha256':hashlib.sha256(content).hexdigest(),'bytes':len(content),'lines':len(content.splitlines()),'commit':commit}
manifest={'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'source':str(source),'files':files,'author_map_and_controls_not_yet_available_at_initial_capture':True,'author_code_executed':False,'private_only':True,'Lean':False}
(base/'INPUT_V1.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':'PASS','files':len(files),'paper':files['PAPER.md'],'source_commit':commit}))
