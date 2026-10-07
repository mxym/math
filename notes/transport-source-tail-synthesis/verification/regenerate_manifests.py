#!/usr/bin/env python3
"""MAINTAINER-ONLY: rewrite integrity ledgers after consciously approved edits.

THIS IS NOT A PUBLIC VERIFICATION OR AUTHENTICATION PATH. It deliberately
replaces prior hashes and grants no authenticity or approval to changed content.
Use verify_integrity.py or package_release.py to check a received release.
Run this only after independent review and explicit authorization of all edits.
The --acknowledge-no-authenticity flag is mandatory. All fixed mandatory release
paths except the four generated outputs must already exist, and all 57 source
pins and protected mathematics must pass before any generated output changes.
Only SOURCE_MANIFEST.json, MANIFEST.json, SHA256SUMS and the source archive are
rewritten. Missing required wrappers, audits, or source files cannot be blessed.
"""

import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import verify_integrity as integrity


def json_bytes(document):
    return (json.dumps(document, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def record(root, path):
    data = integrity.read_file(root, path)
    return {"path": path, "bytes": len(data), "sha256": integrity.sha256(data)}


def regenerate_manifests(root, acknowledge_no_authenticity=False):
    integrity.require(acknowledge_no_authenticity is True, "maintenance-acknowledgment",
                      "explicit acknowledgment that regeneration grants no authenticity is required")
    root = integrity.checked_root(root)
    files = integrity.verify_mandatory_inventory(root, allow_missing_generated=True)
    integrity.verify_dependencies(root)
    integrity.verify_protected_math(root)
    source_records = [record(root, path) for path in sorted(files) if integrity.source_eligible(path)]
    source_document = {"schema_version": 1, "archive": integrity.ARCHIVE_PATH,
                       "prefix": integrity.ARCHIVE_PREFIX, "files": source_records}
    source_bytes = json_bytes(source_document)
    (root / "SOURCE_MANIFEST.json").write_bytes(source_bytes)
    archive = root / integrity.ARCHIVE_PATH
    archive.parent.mkdir(exist_ok=True)
    archive.write_bytes(integrity.canonical_gzip_bytes(integrity.canonical_tar_bytes(
        root, {item["path"]: item for item in source_records}, source_bytes)))
    files, _ = integrity.scan_tree(root)
    records = [record(root, path) for path in sorted(files - integrity.MANIFEST_EXCLUSIONS)]
    (root / "MANIFEST.json").write_bytes(json_bytes({"schema_version": 1, "files": records}))
    hashes = {item["path"]: item["sha256"] for item in records}
    hashes["MANIFEST.json"] = integrity.sha256(integrity.read_file(root, "MANIFEST.json"))
    (root / "SHA256SUMS").write_bytes(
        "".join("{}  {}\n".format(hashes[path], path) for path in sorted(hashes)).encode("utf-8"))
    return integrity.verify(root)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, help="complete staged release directory")
    parser.add_argument("--acknowledge-no-authenticity", action="store_true", required=True,
                        help="confirm this is an authorized maintainer refresh, not release verification")
    args = parser.parse_args(argv)
    try:
        result = regenerate_manifests(args.root, args.acknowledge_no_authenticity)
    except (integrity.IntegrityError, OSError, ValueError) as error:
        print("FAIL: {}".format(error), file=sys.stderr)
        return 1
    print("MAINTAINER REFRESH: consistency checked for {} files and {} source archive members; "
          "no authenticity established".format(
        result["release_files"], result["archive_members"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
