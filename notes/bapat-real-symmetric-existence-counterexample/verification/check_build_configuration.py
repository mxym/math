#!/usr/bin/env python3
"""Test the portable shell wrapper without executing TeX or changing the PDF."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

source = Path(__file__).resolve().parent.parent / 'build.sh'
with tempfile.TemporaryDirectory(prefix='bapat-build-test-') as tmp:
    root = Path(tmp)
    shutil.copy2(source, root / 'build.sh')
    bindir = root / 'bin'
    bindir.mkdir()
    for name in ['pdflatex', 'pdftoppm', 'pdftotext', 'pdfinfo']:
        script = '#!/bin/sh\n'
        if name == 'pdflatex':
            script += 'printf "%s\\n" "$*" >> "$BUILD_TRACE"\n'
        script += 'exit 0\n'
        p = bindir / name
        p.write_text(script)
        p.chmod(0o755)
    env = dict(os.environ)
    env['PATH'] = str(bindir) + os.pathsep + env['PATH']
    env['BUILD_TRACE'] = str(root / 'trace')
    env.pop('LOCAL_TEX_DIR', None)
    result = subprocess.run(['bash', 'build.sh'], cwd=root, env=env, capture_output=True, text=True)
    trace = (root / 'trace').read_text().splitlines()
    if result.returncode or len(trace) != 2 or any('-fmt=' in s for s in trace):
        raise SystemExit('FAIL: default build did not select two ordinary pdflatex passes')
    print('PASS: default build selects two ordinary pdflatex passes.')
    local = root / 'custom-format'
    local.mkdir()
    (local / 'pdflatex.fmt').write_bytes(b'test placeholder; never executed')
    (root / 'trace').unlink()
    env['LOCAL_TEX_DIR'] = str(local)
    result = subprocess.run(['bash', 'build.sh'], cwd=root, env=env, capture_output=True, text=True)
    trace = (root / 'trace').read_text().splitlines()
    if result.returncode or len(trace) != 2 or any(f'-fmt={local}/pdflatex.fmt' not in s for s in trace):
        raise SystemExit('FAIL: explicit custom format was not selected')
    print('PASS: LOCAL_TEX_DIR selects the supplied pre-existing format for both passes.')
    (root / 'trace').unlink()
    env['LOCAL_TEX_DIR'] = str(root / 'missing')
    result = subprocess.run(['bash', 'build.sh'], cwd=root, env=env, capture_output=True, text=True)
    if result.returncode != 2 or (root / 'trace').exists() or 'must contain' not in result.stderr:
        raise SystemExit('FAIL: missing custom format did not fail before execution')
    print('PASS: a missing custom format exits 2 before any compiler invocation.')
print('All checks use temporary command stubs; the frozen mathematical artifacts were untouched.')
