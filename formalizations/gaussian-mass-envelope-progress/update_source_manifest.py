#!/usr/bin/env python3
"""Refresh input hashes after an intentional source edit, before committing."""
from pathlib import Path
import hashlib
import json
root = Path(__file__).resolve().parent
paths = sorted(list(root.glob("*.lean")) + list((root / "audit").glob("*.lean")) +
    [root / p for p in ["lean-toolchain", "lakefile.lean", "lake-manifest.json",
        "reproduce.py", "update_source_manifest.py", "fetch_cache.sh", "PROOF_ROOTS.txt", ".gitattributes"]])
result = {}
for path in paths:
    data = path.read_bytes()
    digest = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    result[str(path.relative_to(root))] = digest
(root / "SOURCE_BLOBS.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
