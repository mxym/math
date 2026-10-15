"""Check exact submission-file bindings, without mathematical claims."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import sys

def main():
    package = Path(__file__).resolve().parent
    root = package.parent.parent
    manifest = json.loads((package / "SOURCE_HASHES.json").read_text())
    for name, expected in manifest["files"].items():
        rel = PurePosixPath(name)
        if rel.is_absolute() or ".." in rel.parts or "\\" in name:
            raise ValueError("Invalid binding path")
        target = root / rel
        if not target.is_file():
            raise ValueError("Missing bound file: " + name)
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError("Hash mismatch: " + name)
    print(json.dumps({"status": "PASS", "files": len(manifest["files"]),
                      "proof_verification_performed": False}))

if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
