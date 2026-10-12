#!/usr/bin/env python3
"""Compare the repaired import scanner with the pinned Lean --deps parser."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from replay_continuum import load_verifier


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-bin", type=Path, required=True)
    args = parser.parse_args()
    lean = (args.lean_bin / "lean").resolve()
    library = lean.parent.parent / "lib/lean"
    verifier = load_verifier()
    cases = {
        "import-all-with-comment-literal": (
            'module\npublic import all Init\n'
            'def text : String := "/-"\n'
        ),
        "nested-comments-and-false-import": (
            'module\n/- outside /- nested -/\nimport Missing.In.Comment\n-/\n'
            'public meta import Init\n-- import Missing.In.LineComment\n'
            'def text : String := "first line\nimport Missing.In.String\nlast line"\n'
            'def quote : Char := \'"\'\n'
        ),
        "implicit-init": 'module\ndef n : Nat := 0\n',
        "prelude": 'prelude\nimport Init\n',
    }
    records = []
    with tempfile.TemporaryDirectory(prefix="continuum-import-controls-") as directory:
        root = Path(directory)
        for label, code in cases.items():
            source = root / "Control.lean"
            source.write_text(code)
            result = subprocess.run(
                [str(lean), "--deps", str(source)], cwd=root,
                capture_output=True, text=True,
            )
            if result.returncode:
                raise RuntimeError(label + ": " + result.stdout + result.stderr)
            actual = []
            for line in result.stdout.splitlines():
                artifact = Path(line.strip())
                if artifact.suffix != ".olean":
                    raise RuntimeError("Unexpected Lean dependency output: " + line)
                actual.append(artifact.relative_to(library).with_suffix("").as_posix().replace("/", "."))
            scanned = verifier.imports(source)
            if set(actual) != set(scanned):
                raise RuntimeError(label + ": scanner/compiler mismatch")
            records.append({"case": label, "imports": sorted(set(actual)), "status": "PASS"})
    print(json.dumps({"status": "PASS", "cases": records}, indent=2))


if __name__ == "__main__":
    main()
