#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
MANIFEST = Path(__file__).resolve().parents[1] / "MANIFEST.json"

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha256(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

def main():
    data = json.loads(MANIFEST.read_text())
    rows = data.get("files")
    require(isinstance(rows, list) and rows, "manifest has no files")
    seen = set()
    for row in rows:
        rel = row["path"]
        require(rel not in seen, f"duplicate path: {rel}")
        seen.add(rel)
        p = ROOT / rel
        require(p.is_file(), f"missing file: {rel}")
        actual = sha256(p)
        require(actual == row["sha256"],
                f"hash mismatch: {rel}: {actual} != {row['sha256']}")
    print(f"PASS: {len(rows)} pinned files match SHA-256 manifest")
    print("scope: byte identity only; theorem correctness requires paper and proof audit")

if __name__ == "__main__":
    main()
