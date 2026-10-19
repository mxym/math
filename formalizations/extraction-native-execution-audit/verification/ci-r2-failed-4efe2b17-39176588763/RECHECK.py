from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
actual={p.name:sha(p)for p in P.iterdir()if p.is_file()and p.name!='FAILED_EVIDENCE_HASHES.json'}
assert actual==json.loads((P/'FAILED_EVIDENCE_HASHES.json').read_text())
s=json.loads((P/'STAGES.json').read_text())
assert [(r['stage'],r['exit_code'])for r in s]==[('toolchain',0),('build',0),('types',134)]
for r in s:assert sha(P/r['log'])==r['sha256']
assert s[-1]['command']==['lake','env','lean','-j1','-M4000','@EVIDENCE@/CheckInvocation.lean']
assert sha(P/'types.log')=='48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a'
assert 'Build completed successfully (4125 jobs).'in(P/'build.log').read_text()
assert 'lean::memory_exception'in(P/'types.log').read_text()
assert not (P/'SUMMARY.json').exists()
assert json.loads((P/'REPORT.json').read_text())['complete_audit_pass']is False
print('HOSTED_R2_FAILURE_EVIDENCE_PRESERVATION_PASS_NOT_KERNEL_VERIFICATION')
