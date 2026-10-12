#!/usr/bin/env python3
"""Positive and deliberate-failure tests of the exact source-inventory CLI.
This is a metadata-controller regression, not a substitute for Lean proof checking.
"""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile

PACKAGE=(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[2]).resolve()
PROGRAM=PACKAGE/'scripts/source_manifest.py'
results=[]
with tempfile.TemporaryDirectory(prefix='appt-manifest-control-') as temporary:
    root=Path(temporary)
    (root/'APPT').mkdir();(root/'Verification').mkdir();(root/'scripts').mkdir()
    for name in ['lakefile.toml','lake-manifest.json','lean-toolchain','NECESSITY_SOURCES.json']:
        shutil.copy2(PACKAGE/name,root/name)
    shutil.copy2(PROGRAM,root/'scripts/source_manifest.py')
    (root/'APPT/Fixture.lean').write_text('def sourceInventoryFixture : Nat := 1\n')
    (root/'Verification/Fixture.lean').write_text('def auditInventoryFixture : Nat := 1\n')
    command=[sys.executable,str(root/'scripts/source_manifest.py')]
    subprocess.run(command,check=True,capture_output=True,text=True,timeout=10)
    baseline={p.relative_to(root):p.read_bytes() for p in root.rglob('*') if p.is_file()}
    def restore():
        for p in root.rglob('*'):
            if p.is_file() and p.relative_to(root) not in baseline:p.unlink()
        for p,data in baseline.items():(root/p).write_bytes(data)
    def check(name,should_pass):
        completed=subprocess.run(command+['--check'],capture_output=True,text=True,timeout=10)
        diagnostic='RuntimeError: Manifest does not cover the exact current proof package'
        passed=(completed.returncode==0 and 'COMPLETE_SOURCE_MANIFEST_PASS' in completed.stdout) if should_pass else (completed.returncode==1 and diagnostic in completed.stderr)
        record={'name':name,'expected_acceptance':should_pass,'exit_code':completed.returncode,'passed':passed,'stdout':completed.stdout,'stderr':completed.stderr}
        results.append(record)
        if not passed:raise RuntimeError(json.dumps(record))
    check('unchanged pinned source tree',True)
    (root/'APPT/Fixture.lean').write_text('def sourceInventoryFixture : Nat := 2\n')
    check('changed mathematical source',False);restore()
    (root/'Verification/Fixture.lean').write_text('def auditInventoryFixture : Nat := 2\n')
    check('changed independent replay support',False);restore()
    (root/'APPT/Fixture.lean').unlink()
    check('missing mathematical source',False);restore()
    (root/'APPT/Unlisted.lean').write_text('def unlistedFixture : Nat := 3\n')
    check('extra unlisted mathematical source',False);restore()
    (root/'lean-toolchain').write_text('leanprover/lean4:v0.0.0\n')
    check('changed toolchain pin',False);restore()
    manifest=json.loads((root/'PROOF_SOURCES.json').read_text())
    manifest['APPT/Fixture.lean']='f'*64
    (root/'PROOF_SOURCES.json').write_text(json.dumps(manifest))
    check('altered recorded checksum',False);restore()
    check('restored pinned source tree',True)
report={'status':'PASS','scope':'Source-inventory CLI controls only','program_sha256':hashlib.sha256(PROGRAM.read_bytes()).hexdigest(),'checks':results}
print(json.dumps(report,indent=2))
