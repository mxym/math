#!/usr/bin/env python3
"""Build the PDF with the installed pdfLaTeX; no downloads or shell escape."""
import datetime
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parent
source = root / "source" / "paper.tex"
env = os.environ.copy()
env["SOURCE_DATE_EPOCH"] = str(int(datetime.datetime(2026, 10, 9, tzinfo=datetime.timezone.utc).timestamp()))
env["FORCE_SOURCE_DATE"] = "1"
with tempfile.TemporaryDirectory(prefix="mi-written-v1-pdf-") as directory:
    for _ in range(2):
        result = subprocess.run(
            ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
             "-output-directory", directory, source.name],
            cwd=source.parent, env=env, text=True, capture_output=True,
        )
        if result.returncode:
            print(result.stdout)
            print(result.stderr)
            raise SystemExit(result.returncode)
    output = Path(directory) / "paper.pdf"
    data = output.read_bytes()
    (source.parent / "paper.pdf").write_bytes(data)
    log = (Path(directory) / "paper.log").read_text()
    problems = [line for line in log.splitlines()
                if "Overfull" in line or "undefined references" in line or "LaTeX Warning" in line]
    print("PDF SHA-256:", hashlib.sha256(data).hexdigest())
    print("PDF bytes:", len(data))
    for problem in problems:
        print(problem)
