#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
MANIFEST = Path(__file__).resolve().parents[1] / "MANIFEST.json"

def fail(message):
    raise RuntimeError(message)

def sha256(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

def main():
    data = json.loads(MANIFEST.read_text())
    files = data.get("files")
    if not isinstance(files, list) or not files:
        fail("manifest has no files")
    seen = set()
    for row in files:
        rel = row["path"]
        expected = row["sha256"]
        if rel in seen:
            fail(f"duplicate path: {rel}")
        seen.add(rel)
        p = ROOT / rel
        if not p.is_file():
            fail(f"missing file: {rel}")
        actual = sha256(p)
        if actual != expected:
            fail(f"hash mismatch: {rel}: {actual} != {expected}")
    print(f"PASS: {len(files)} pinned files match SHA-256 manifest")
    print("scope: byte identity only; theorem correctness requires paper and proof audit")

if __name__ == "__main__":
    main()
