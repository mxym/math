"""Read-only capture of exact credited local sources. Does not run Lean."""
from pathlib import Path
import hashlib,json,shutil,subprocess
from datetime import datetime,timezone

root=Path('/home/mxym/math-appt-multiscale-20261013')
out=Path(__file__).resolve().parent
base='c4e0d9e713ba349d376469231789bb7b36915b7d'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
head=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD']).decode().strip()
if head!=base:raise RuntimeError('Unexpected source HEAD')
paths=[
 'research/appt-growing-renyi/LINEAR_ORDER_VARIATIONAL.md',
 'research/appt-growing-renyi/LINEAR_ORDER_REVIEW.json',
 'research/appt-growing-renyi/ALL_ORDER_VARIATIONAL.md',
 'research/appt-growing-renyi/ALL_ORDER_REVIEW.json',
 'research/appt-linear-critical-rigidity-20261015/PAPER.md',
 'research/appt-linear-critical-rigidity-20261015/REVIEW.md',
 'research/appt-linear-critical-rigidity-20261015/REVIEW.json',
 'research/appt-linear-critical-rigidity-20261015/FINAL_STATUS_BINDING.json',
]
rows=[]
for rel in paths:
 src=root/rel
 if not src.is_file():raise FileNotFoundError(str(src))
 dest=out/'credited-inputs'/rel
 dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists() and sha(dest)!=sha(src):raise RuntimeError('Existing credited copy differs')
 shutil.copyfile(src,dest)
 rows.append({'source_commit':base,'repository_path':rel,'copied_path':str(dest.relative_to(out)),
              'sha256':sha(src),'bytes':src.stat().st_size})
record={'utc':datetime.now(timezone.utc).isoformat(),'source_commit':base,'files':rows,
        'new_Lean':False,'new_audit_roots':0,'actual_inputs':'L1/L20-L21 and S; V credited as prior all-order closure'}
(out/'CREDITED_INPUTS.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'captured':len(rows),'source_commit':base}))
