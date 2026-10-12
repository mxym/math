#!/usr/bin/env python3
"""Verify a complete release and reproduce its source archive without resealing.

This public path NEVER changes the package, its source archive, or its ledgers.
Full integrity verification and fixed mandatory-inventory checks run before any
output is written. The reconstructed archive must be byte-identical to the
verified existing archive. With --output, write that archive only to a NEW file
outside the package; without --output, perform a read-only reproducibility check.

Invalid/missing manifests, checksum omissions, changed wrappers or sources, and
missing required files are failures, not invitations to generate fresh hashes.
Explicitly authorized maintenance uses regenerate_manifests.py separately;
neither tool establishes authenticity without an independent trusted release.
"""

import argparse
import os
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import verify_integrity as integrity


def build_release(root, output=None):
    root = integrity.checked_root(root)
    # Trust boundary: do not regenerate or overwrite anything before this full
    # preflight succeeds. In particular, never repair a received release here.
    result = integrity.verify(root)
    integrity.verify_mandatory_inventory(root)
    source_bytes = integrity.read_file(root, "SOURCE_MANIFEST.json")
    records = integrity.file_records(integrity.load_json_bytes(source_bytes, "SOURCE_MANIFEST.json"),
                                     "SOURCE_MANIFEST.json")
    candidate = integrity.canonical_gzip_bytes(integrity.canonical_tar_bytes(root, records, source_bytes))
    integrity.require(candidate == integrity.read_file(root, integrity.ARCHIVE_PATH),
                      "archive-reproducibility", "rebuilt archive differs; no files changed")
    if output is not None:
        destination = Path(output).absolute()
        resolved = destination.resolve()
        resolved_root = root.resolve()
        integrity.require(resolved != resolved_root and resolved_root not in resolved.parents,
                          "unsafe-output", "output must be outside the immutable release package")
        integrity.require(not os.path.lexists(destination), "output-exists",
                          "output must be a new file; existing files are never overwritten")
        # Publish atomically with no overwrite, keeping temporary bytes outside
        # the immutable package. Link and temporary file share one filesystem.
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(prefix=".transport-archive-", dir=destination.parent,
                                             delete=False) as stream:
                temporary = Path(stream.name)
                stream.write(candidate)
            os.link(temporary, destination)
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, help="existing complete release directory")
    parser.add_argument("--output", type=Path, help="optional new source archive file outside the release")
    args = parser.parse_args(argv)
    try:
        result = build_release(args.root, args.output)
    except (integrity.IntegrityError, OSError, ValueError) as error:
        print("FAIL: {}".format(error), file=sys.stderr)
        return 1
    print("PASS: verified {} files; reproduced {} source archive members byte-for-byte; "
          "release unchanged{}".format(result["release_files"], result["archive_members"],
          "; external archive written" if args.output is not None else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
