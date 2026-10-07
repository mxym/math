#!/usr/bin/env python3
import json
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
normal = subprocess.run(
    [sys.executable, "-B", str(root / "checks" / "check_exact.py")],
    check=True, capture_output=True, text=True
).stdout
optimized = subprocess.run(
    [sys.executable, "-B", "-O", str(root / "checks" / "check_exact.py")],
    check=True, capture_output=True, text=True
).stdout
if json.loads(normal) != json.loads(optimized):
    raise SystemExit("normal and optimized reports differ")
print(normal, end="")

independent = subprocess.run(
    [sys.executable, "-B", str(root / "checks" / "check_independent.py")],
    check=True, capture_output=True, text=True
).stdout
independent_opt = subprocess.run(
    [sys.executable, "-B", "-O", str(root / "checks" / "check_independent.py")],
    check=True, capture_output=True, text=True
).stdout
if json.loads(independent) != json.loads(independent_opt):
    raise SystemExit("independent normal and optimized reports differ")
print(independent, end="")
