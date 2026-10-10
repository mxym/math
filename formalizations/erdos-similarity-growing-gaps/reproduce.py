#!/usr/bin/env python3
"""Build and replay the growing-gap Lean package."""
from pathlib import Path
import subprocess
import os
import shutil

root = Path(__file__).resolve().parent

lake = os.environ.get("LAKE_BIN") or shutil.which("lake") or "/home/agent/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake"

def run(args):
    print("$", " ".join(args), flush=True)
    subprocess.run(args, cwd=root, check=True)

run([lake, "exe", "cache", "get"])
run([lake, "build", "ErdosSimilarityGrowingGaps"])
run([lake, "env", "lean", "-t", "0", "ErdosSimilarityGrowingGaps/Replay.lean"])
run(["python3", "checks/negative.py"])
print("reproduction passed")
