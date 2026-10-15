"""Compile the standalone manuscript and bind its actual build inputs."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "build" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
BUILD.mkdir(parents=True, exist_ok=False)
inputs = sorted(ROOT.glob("*.tex"))
hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
env = dict(os.environ)
env["SOURCE_DATE_EPOCH"] = str(int(datetime(2026, 10, 16, tzinfo=timezone.utc).timestamp()))
for number in range(1, 4):
    run = subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "-output-directory", str(BUILD), "paper.tex"],
        cwd=ROOT, env=env, capture_output=True, timeout=120,
    )
    (BUILD / f"pass-{number}.stdout.txt").write_bytes(run.stdout)
    (BUILD / f"pass-{number}.stderr.txt").write_bytes(run.stderr)
    if run.returncode:
        print(run.stdout.decode(errors="replace")[-9000:])
        raise SystemExit(run.returncode)
log = (BUILD / "paper.log").read_text(errors="replace")
overfull = re.findall(r"Overfull \\[hv]box[^\n]*(?:\n[^\n]*)?", log)
undefined = [line for line in log.splitlines() if "undefined" in line.lower() or "multiply defined" in line.lower()]
if {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs} != hashes:
    raise RuntimeError("A TeX input changed during compilation")
target = ROOT / "paper.pdf"
shutil.copyfile(BUILD / "paper.pdf", target)
info = subprocess.run(["pdfinfo", str(target)], capture_output=True, text=True, check=True).stdout
(BUILD / "pdfinfo.txt").write_text(info)
fonts = subprocess.run(["pdffonts", str(target)], capture_output=True, text=True, check=True).stdout
(BUILD / "pdffonts.txt").write_text(fonts)
report = {
    "utc": datetime.now(timezone.utc).isoformat(),
    "tex_inputs_sha256": hashes,
    "pdf_sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
    "pdf_bytes": target.stat().st_size,
    "overfull_boxes": overfull,
    "undefined_or_duplicate_references": undefined,
    "compilation_passes": 3,
    "build_directory": str(BUILD),
    "visual_review": "pending",
    "mathematical_review": "separately scoped; compilation is not proof verification",
}
(ROOT / "BUILD.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"pdf": str(target), "sha256": report["pdf_sha256"], "overfull_count": len(overfull), "reference_warning_count": len(undefined), "pdfinfo": info}, indent=2))
if overfull or undefined:
    print(json.dumps({"overfull": overfull, "undefined": undefined}, indent=2))
    raise SystemExit(2)
