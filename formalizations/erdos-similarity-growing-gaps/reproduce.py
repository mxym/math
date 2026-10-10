#!/usr/bin/env python3
"""Build and replay the growing-gap Lean package."""
from pathlib import Path
import subprocess
import os
import shutil

root = Path(__file__).resolve().parent

workspace_lake = "/workspace/tools/elan/bin/lake"
lake = os.environ.get("LAKE_BIN") or (workspace_lake if Path(workspace_lake).exists() else None) or shutil.which("lake") or "/home/agent/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake"

def run(args):
    print("$", " ".join(args), flush=True)
    subprocess.run(args, cwd=root, check=True)

# The pinned 4.34.1 release predates the optional `leantar` helper used by
# the current cache downloader.  A complete pinned cache may already be
# supplied by the environment; in that case the downloader failure is
# harmless and the kernel build below is still authoritative.  Other cache
# failures remain fatal.
print("$", lake, "exe", "cache", "get", flush=True)
cache = subprocess.run(
    [lake, "exe", "cache", "get"], cwd=root, text=True,
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
if cache.returncode:
    if "leantar not found" in cache.stdout:
        print("cache downloader skipped: pinned compiler has no leantar", flush=True)
    else:
        print(cache.stdout, end="", flush=True)
        raise SystemExit(cache.returncode)
else:
    print(cache.stdout, end="", flush=True)
run([lake, "build", "ErdosSimilarityGrowingGaps"])
run([lake, "env", "lean", "-t", "0", "ErdosSimilarityGrowingGaps/Replay.lean"])
run(["python3", "checks/negative.py"])
print("reproduction passed")
