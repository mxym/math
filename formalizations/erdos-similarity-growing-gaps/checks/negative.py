#!/usr/bin/env python3
"""The kernel must reject a deliberately false tree bound."""
from pathlib import Path
import subprocess
import shutil
import tempfile

root = Path(__file__).resolve().parents[1]
lean = root / ".." / ".." / ".." / "home" / "agent" / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1" / "bin" / "lean"
# In normal use Lake supplies the toolchain; this fallback keeps the check
# useful when LEAN_BIN is explicitly provided.
import os
lake = os.environ.get("LAKE_BIN") or shutil.which("lake") or "/home/agent/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake"
sources = ["""
import ErdosSimilarityGrowingGaps.VariableTree
open GrowingGap
example : span 2 1 0 1 ≤ 0 := by
  norm_num [span]
""", """
import ErdosSimilarityGrowingGaps.FiniteRouting
example : ((1 - (1 / 2 : ℝ)) ^ 1) = 0 := by
  norm_num
"""]
with tempfile.TemporaryDirectory() as td:
    for j, source in enumerate(sources):
        f = Path(td) / f"Reject{j}.lean"
        f.write_text(source)
        proc = subprocess.run(
            [lake, "env", "lean", str(f)],
            cwd=root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if proc.returncode == 0:
            raise SystemExit(f"negative control {j} unexpectedly compiled")
    print("negative controls rejected as expected")
