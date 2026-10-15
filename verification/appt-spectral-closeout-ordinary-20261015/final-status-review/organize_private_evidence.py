"""Keep raw operational snapshots out of the future public metadata copy."""
from pathlib import Path
import hashlib,json,datetime
out=Path(__file__).resolve().parent
private=out/'private-protection-evidence';private.mkdir(exist_ok=True)
source=out/'preliminary-reads';target=private/'preliminary-reads'
assert source.resolve().is_relative_to(out.resolve())
assert target.parent.resolve().is_relative_to(out.resolve())
assert source.is_dir() and not target.exists()
before={str(p.relative_to(source)):hashlib.sha256(p.read_bytes()).hexdigest() for p in source.rglob('*') if p.is_file()}
source.rename(target)
after={str(p.relative_to(target)):hashlib.sha256(p.read_bytes()).hexdigest() for p in target.rglob('*') if p.is_file()}
assert before==after
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PRIVATE_OPERATIONAL_SNAPSHOTS_RELOCATED_WITHOUT_BYTE_CHANGE','source_relative':'preliminary-reads','destination_relative':'private-protection-evidence/preliminary-reads','files':before,'reason':'TASK_SCOPE contains operational user-request text; raw guard snapshots and preparatory diagnostics are private preservation, not public proof evidence','public_copy_excluded':True}
(private/'PRIVATE_ORGANIZATION.json').write_text(json.dumps(record,indent=2)+'\n')
# Keep first-run negative results before a final run against updated helpers.
first=out/'HELPER_NEGATIVE_CONTROLS.json'
history=out/'helper-runs';history.mkdir(exist_ok=True)
(history/'INITIAL_HELPER_NEGATIVE_CONTROLS.json').write_bytes(first.read_bytes())
print(json.dumps({'private_raw_snapshot_files':len(before),'bytes_unchanged':True,'initial_negative_run_preserved':True}))
