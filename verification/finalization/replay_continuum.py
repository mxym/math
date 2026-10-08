#!/usr/bin/env python3
"""Replay the sealed continuum package with a corrected Lean import scanner.

The original release is validated by its unchanged verifier. Only its Python
dependency scanner is overridden; every Lean source, guard, inventory and
kernel replay is the original pinned input.
"""
import hashlib
import importlib.util
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[2]
RELEASE = REPO / "formalizations/continuum-remainder-avoidance"
ORIGINAL = RELEASE / "scripts/verify.py"
ORIGINAL_SHA256 = "c0f68c5904bf175e284d4255f5dfb3a1c43a19643e821172b2d88b7d6330bdc5"


def load_verifier():
    if hashlib.sha256(ORIGINAL.read_bytes()).hexdigest() != ORIGINAL_SHA256:
        raise RuntimeError("The pinned historical verifier changed")
    sys.path.insert(0, str(RELEASE / "scripts"))
    spec = importlib.util.spec_from_file_location("sealed_continuum_verifier", ORIGINAL)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load the pinned verifier")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    def imports(source):
        code = module.stripped(source.read_text())
        return re.findall(
            r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)",
            code,
            re.MULTILINE,
        )

    module.imports = imports
    return module


if __name__ == "__main__":
    load_verifier().main()
