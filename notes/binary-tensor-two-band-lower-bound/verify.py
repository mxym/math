#!/usr/bin/env python3
"""Run the exact checker in ordinary and optimized Python modes."""
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
checker = root / "checks" / "check_exact.py"
outputs = []

for extra in ([], ["-O"]):
    cmd = [sys.executable, "-B", *extra, str(checker)]
    cp = subprocess.run(cmd, cwd=root, text=True,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if cp.returncode:
        sys.stderr.write(cp.stdout)
        sys.stderr.write(cp.stderr)
        raise SystemExit(cp.returncode)
    outputs.append(cp.stdout)

if outputs[0] != outputs[1]:
    raise RuntimeError("ordinary and optimized checker output differ")

sys.stdout.write(outputs[0])
print("ORDINARY/OPTIMIZED OUTPUT IDENTITY: PASS")
