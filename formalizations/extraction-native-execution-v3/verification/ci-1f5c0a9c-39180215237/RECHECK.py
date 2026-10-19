"""Read-only CI seal recheck; frozen reader requires its actual event HEAD."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--artifact',type=Path);ap.add_argument('--reader-repo',type=Path);a=ap.parse_args()
assert {p.relative_to(P).as_posix():sha(p)for p in P.rglob('*')if p.is_file()and p!=P/'SEALED_FILES.json'}==json.loads((P/'SEALED_FILES.json').read_text())
r=json.loads((P/'REPORT.json').read_text());snap=P/'snapshot';expected=json.loads((snap/'EVIDENCE_HASHES.json').read_text())
assert r['snapshot_omissions']==['native/audit-driver']
assert {p.relative_to(snap).as_posix():sha(p)for p in snap.rglob('*')if p.is_file()and p!=snap/'EVIDENCE_HASHES.json'}=={n:h for n,h in expected.items()if n!='native/audit-driver'}
assert sha(snap/'EVIDENCE_HASHES.json')==r['raw_manifest_sha256']
reader=a.reader_repo or Path(r['expected_event_reader_repo']);artifact=a.artifact or Path(r['full_artifact_wrapper'])
assert subprocess.check_output(['git','-C',str(reader),'rev-parse','HEAD'],text=True).strip()==r['event_commit']
raw=artifact/json.loads((artifact/'LATEST.json').read_text())['directory']
assert sha(raw/'EVIDENCE_HASHES.json')==r['raw_manifest_sha256']
result=subprocess.run([sys.executable,str(reader/'formalizations/extraction-native-execution-v3/evidence.py'),str(artifact),'--expected-commit',r['event_commit'],'--run-id',str(r['run_id']),'--run-attempt',str(r['run_attempt'])],check=True,text=True,capture_output=True)
assert 'NATIVE_V3_ARTIFACT_PASS'in result.stdout
print(result.stdout.strip());print('CI_NATIVE_V3_FULL_ARTIFACT_AND_SEAL_READONLY_RECHECK_PASS_NO_LEAN')
