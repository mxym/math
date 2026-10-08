"""Compile the complete paper with the installed pdfLaTeX."""
from pathlib import Path
import json, os, shutil, subprocess, tempfile
ROOT = Path(__file__).resolve().parent

def main():
    with tempfile.TemporaryDirectory(prefix="ehrhart-paper-") as name:
        work = Path(name)
        env = dict(os.environ)
        env["SOURCE_DATE_EPOCH"] = "1791417600"  # 2026-10-08 00:00:00 UTC
        env["FORCE_SOURCE_DATE"] = "1"
        for _ in range(3):
            result = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                 "-file-line-error", "-output-directory", str(work), "paper.tex"],
                cwd=ROOT, env=env, capture_output=True, text=True, timeout=180)
            if result.returncode:
                raise RuntimeError(result.stdout[-6000:])
        log = (work / "paper.log").read_text()
        bad = [line for line in log.splitlines() if any(
            marker in line for marker in ["Overfull", "undefined", "Missing character"])]
        if bad:
            raise RuntimeError("PDF validation failed: " + repr(bad))
        shutil.copyfile(work / "paper.pdf", ROOT / "paper.pdf")
        print(json.dumps({"status": "PASS", "passes": 3,
                          "pdf": "paper.pdf", "overflow_or_missing_glyph": False}))

if __name__ == "__main__":
    main()
