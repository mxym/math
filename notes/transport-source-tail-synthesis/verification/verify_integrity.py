#!/usr/bin/env python3
"""Fail-closed, offline release verification using only Python's standard library.

Contract (schema_version 1):
* MANIFEST.json: {"schema_version": 1, "files": [{"path": str, "bytes": int,
  "sha256": lowercase_hex}, ...]}. Entries are sorted by path and cover every
  regular file except MANIFEST.json and SHA256SUMS, including the source archive.
* SHA256SUMS: sorted UTF-8 lines '<sha256>  <path>\n', covering the same files
  plus MANIFEST.json. It does not recursively hash itself.
* This release's fixed REQUIRED_RELEASE_FILES inventory is independent of the
  mutable manifests. Removing a required wrapper, report, audit, source copy,
  or provenance record cannot be blessed by recomputing all ledgers.
* SOURCE_MANIFEST.json: schema_version/files as above, plus "archive" equal to
  ARCHIVE_PATH and "prefix" equal to ARCHIVE_PREFIX. Its files are exactly the
  release files except PDFs, all three root manifests/hash lists, and the archive.
  The archive also contains SOURCE_MANIFEST.json, byte-identical to the outer
  copy but deliberately absent from the source manifest's own files list.
* The archive is gzip (mtime=0, empty filename, level-9 header), containing
  sorted USTAR regular files only: uid=gid=mtime=0, uname=gname='', mode=0644.
  No extraction is performed. Source bytes, member names, metadata, canonical
  tar encoding, and the absence of extra/trailing data are all checked.
* DEPENDENCIES.json has exactly 57 inputs with path, local_copy, bytes, sha256,
  git_blob; local_copy must equal 'sources/' + path. Git SHA-1 is computed over
  b'blob ' + decimal_length + b'\0' + file_bytes, not the bare file bytes.
* PROTECTED_MATHEMATICS.json pins Section 1 and all 10 theorem/lemma/corollary/
  proof environments of synthesis.tex. Its source_sha256 identifies the prior
  source snapshot; it is provenance, not the hash of the edited whole release
  manuscript. The current whole-file hash is pinned by MANIFEST.json.

All validation uses explicit exceptions, never assert, and is identical under
python -O. This detects inconsistencies, not maliciously replaced manifests:
authenticity requires an independently trusted release/commit or digest. Verify
a static private copy; this is not a concurrent hostile-filesystem sandbox.
"""

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import stat
import sys
import tarfile
import zlib

sys.dont_write_bytecode = True

ARCHIVE_PATH = "source/transport-source-tail-synthesis-source.tar.gz"
ARCHIVE_PREFIX = "transport-source-tail-synthesis/"
MANIFEST_EXCLUSIONS = frozenset(("MANIFEST.json", "SHA256SUMS"))
SOURCE_EXCLUSIONS = MANIFEST_EXCLUSIONS | {"SOURCE_MANIFEST.json", ARCHIVE_PATH}
HEX256 = re.compile(r"[0-9a-f]{64}\Z")
HEX160 = re.compile(r"[0-9a-f]{40}\Z")
PATH_PATTERN = re.compile(r"[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*\Z")
ENV_TOKEN = re.compile(rb"\\(begin|end)\{(theorem|lemma|corollary|proof)\}")
GZIP_HEADER = b"\x1f\x8b\x08\x00\x00\x00\x00\x00\x02\xff"
MAX_ARCHIVE_BYTES = 256 * 1024 * 1024


# Fixed inventory for this release, independent of editable manifest entries.
# A future release must consciously update this contract when changing its layout.
REQUIRED_RELEASE_FILES = frozenset("""
BUILD_INFO.json
DEPENDENCIES.json
DEPENDENCY_MAP.md
MANIFEST.json
README.md
RELEASE_DELTA.json
RELEASE_DELTA.md
REVIEW.md
SHA256SUMS
SOURCE_MANIFEST.json
audit/B_REVIEW.md
audit/CORE_PROOF_REVIEW.md
audit/CORRECTION_RECORD.md
audit/IMPORT_REVIEW.md
audit/SANITIZATION_CHANGE_LEDGER.json
audit/SANITIZATION_CHANGE_LEDGER.md
provenance/PROTECTED_MATHEMATICS.json
provenance/RIGHTS_AND_ATTRIBUTION.md
provenance/RIGHTS_SOURCE_PINS.json
provenance/SANITIZATION_QA.json
provenance/UPSTREAM_NOTICE.md
provenance/openai_math_LICENSE.txt
source/transport-source-tail-synthesis-source.tar.gz
sources/comparisons/2026-10-07-density-overlap-phase.md
sources/comparisons/2026-10-07-gaussian-finite-moments.md
sources/comparisons/2026-10-07-modulus-tail-reconciliation.md
sources/comparisons/2026-10-07-source-regularity-reconciliation.md
sources/notes/critical-boundary-slow-variation/BUILD_INFO.txt
sources/notes/critical-boundary-slow-variation/QA.txt
sources/notes/critical-boundary-slow-variation/README.txt
sources/notes/critical-boundary-slow-variation/manuscript.tex
sources/notes/stretched-exponential-sharpness/README.md
sources/notes/stretched-exponential-sharpness/stretched_exponential_sharpness.tex
sources/preprints/001-strongly-log-concave-brenier/README.md
sources/preprints/001-strongly-log-concave-brenier/v1/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v1/references.bib
sources/preprints/001-strongly-log-concave-brenier/v2/CHANGELOG.txt
sources/preprints/001-strongly-log-concave-brenier/v2/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v2/references.bib
sources/preprints/001-strongly-log-concave-brenier/v3/BUILD_INFO.txt
sources/preprints/001-strongly-log-concave-brenier/v3/CHANGELOG.txt
sources/preprints/001-strongly-log-concave-brenier/v3/QA.txt
sources/preprints/001-strongly-log-concave-brenier/v3/README.txt
sources/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v3/references.bib
sources/preprints/001-strongly-log-concave-brenier/v4/BUILD_INFO.txt
sources/preprints/001-strongly-log-concave-brenier/v4/CHANGELOG.txt
sources/preprints/001-strongly-log-concave-brenier/v4/QA.txt
sources/preprints/001-strongly-log-concave-brenier/v4/README.txt
sources/preprints/001-strongly-log-concave-brenier/v4/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v4/references.bib
sources/preprints/001-strongly-log-concave-brenier/v5/BUILD_INFO.txt
sources/preprints/001-strongly-log-concave-brenier/v5/CHANGELOG.txt
sources/preprints/001-strongly-log-concave-brenier/v5/QA.txt
sources/preprints/001-strongly-log-concave-brenier/v5/README.txt
sources/preprints/001-strongly-log-concave-brenier/v5/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v5/references.bib
sources/preprints/007-tail-brenier-stability/README.md
sources/preprints/007-tail-brenier-stability/v1/PROOF_AUDIT.md
sources/preprints/007-tail-brenier-stability/v1/main.tex
sources/preprints/007-tail-brenier-stability/v1/verification/check_interpolation.py
sources/preprints/007-tail-brenier-stability/v1/verification/run.txt
sources/preprints/007-tail-brenier-stability/v2/PROOF_AUDIT.md
sources/preprints/007-tail-brenier-stability/v2/README.md
sources/preprints/007-tail-brenier-stability/v2/build.py
sources/preprints/007-tail-brenier-stability/v2/core.tex
sources/preprints/007-tail-brenier-stability/v2/extension.tex
sources/preprints/007-tail-brenier-stability/v2/main.tex
sources/preprints/007-tail-brenier-stability/v2/verification/check_steep_example.py
sources/preprints/007-tail-brenier-stability/v2/verification/interpolation_run.txt
sources/preprints/007-tail-brenier-stability/v2/verification/steep_run.txt
sources/preprints/008-density-overlap-phase/README.md
sources/preprints/008-density-overlap-phase/v1/PROOF_AUDIT.md
sources/preprints/008-density-overlap-phase/v1/main.tex
sources/preprints/008-density-overlap-phase/v1/verification/check_exact.py
sources/preprints/008-density-overlap-phase/v1/verification/optimized_run.txt
sources/preprints/008-density-overlap-phase/v1/verification/run.txt
sources/reviews/2026-10-07-critical-slow-variation-review.md
sources/reviews/2026-10-07-density-overlap-independent-audit.md
sources/reviews/2026-10-07-transport-v5-assembly.md
synthesis.pdf
synthesis.tex
verification/INTEGRITY_QA.json
verification/build_pdf.sh
verification/check_root_overlap.py
verification/package_release.py
verification/regenerate_manifests.py
verification/requirements.txt
verification/results/007-interpolation-normal.json
verification/results/007-interpolation-normal.txt
verification/results/007-interpolation-optimized.json
verification/results/007-interpolation-optimized.txt
verification/results/007-steep-normal.json
verification/results/007-steep-normal.txt
verification/results/007-steep-optimized.json
verification/results/007-steep-optimized.txt
verification/results/008-exact-normal.json
verification/results/008-exact-normal.txt
verification/results/008-exact-optimized.json
verification/results/008-exact-optimized.txt
verification/results/CHECK_REPORT.json
verification/results/root-overlap-normal.json
verification/results/root-overlap-normal.txt
verification/results/root-overlap-optimized.json
verification/results/root-overlap-optimized.txt
verification/run_checks.py
verification/test_integrity.py
verification/verify_integrity.py
""".split())
REQUIRED_DEPENDENCY_FILES = frozenset("""
sources/comparisons/2026-10-07-density-overlap-phase.md
sources/comparisons/2026-10-07-gaussian-finite-moments.md
sources/comparisons/2026-10-07-modulus-tail-reconciliation.md
sources/comparisons/2026-10-07-source-regularity-reconciliation.md
sources/notes/critical-boundary-slow-variation/BUILD_INFO.txt
sources/notes/critical-boundary-slow-variation/QA.txt
sources/notes/critical-boundary-slow-variation/README.txt
sources/notes/critical-boundary-slow-variation/manuscript.tex
sources/notes/stretched-exponential-sharpness/README.md
sources/notes/stretched-exponential-sharpness/stretched_exponential_sharpness.tex
sources/preprints/001-strongly-log-concave-brenier/README.md
sources/preprints/001-strongly-log-concave-brenier/v1/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v1/references.bib
sources/preprints/001-strongly-log-concave-brenier/v2/CHANGELOG.txt
sources/preprints/001-strongly-log-concave-brenier/v2/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v2/references.bib
sources/preprints/001-strongly-log-concave-brenier/v3/BUILD_INFO.txt
sources/preprints/001-strongly-log-concave-brenier/v3/CHANGELOG.txt
sources/preprints/001-strongly-log-concave-brenier/v3/QA.txt
sources/preprints/001-strongly-log-concave-brenier/v3/README.txt
sources/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v3/references.bib
sources/preprints/001-strongly-log-concave-brenier/v4/BUILD_INFO.txt
sources/preprints/001-strongly-log-concave-brenier/v4/CHANGELOG.txt
sources/preprints/001-strongly-log-concave-brenier/v4/QA.txt
sources/preprints/001-strongly-log-concave-brenier/v4/README.txt
sources/preprints/001-strongly-log-concave-brenier/v4/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v4/references.bib
sources/preprints/001-strongly-log-concave-brenier/v5/BUILD_INFO.txt
sources/preprints/001-strongly-log-concave-brenier/v5/CHANGELOG.txt
sources/preprints/001-strongly-log-concave-brenier/v5/QA.txt
sources/preprints/001-strongly-log-concave-brenier/v5/README.txt
sources/preprints/001-strongly-log-concave-brenier/v5/manuscript.tex
sources/preprints/001-strongly-log-concave-brenier/v5/references.bib
sources/preprints/007-tail-brenier-stability/README.md
sources/preprints/007-tail-brenier-stability/v1/PROOF_AUDIT.md
sources/preprints/007-tail-brenier-stability/v1/main.tex
sources/preprints/007-tail-brenier-stability/v1/verification/check_interpolation.py
sources/preprints/007-tail-brenier-stability/v1/verification/run.txt
sources/preprints/007-tail-brenier-stability/v2/PROOF_AUDIT.md
sources/preprints/007-tail-brenier-stability/v2/README.md
sources/preprints/007-tail-brenier-stability/v2/build.py
sources/preprints/007-tail-brenier-stability/v2/core.tex
sources/preprints/007-tail-brenier-stability/v2/extension.tex
sources/preprints/007-tail-brenier-stability/v2/main.tex
sources/preprints/007-tail-brenier-stability/v2/verification/check_steep_example.py
sources/preprints/007-tail-brenier-stability/v2/verification/interpolation_run.txt
sources/preprints/007-tail-brenier-stability/v2/verification/steep_run.txt
sources/preprints/008-density-overlap-phase/README.md
sources/preprints/008-density-overlap-phase/v1/PROOF_AUDIT.md
sources/preprints/008-density-overlap-phase/v1/main.tex
sources/preprints/008-density-overlap-phase/v1/verification/check_exact.py
sources/preprints/008-density-overlap-phase/v1/verification/optimized_run.txt
sources/preprints/008-density-overlap-phase/v1/verification/run.txt
sources/reviews/2026-10-07-critical-slow-variation-review.md
sources/reviews/2026-10-07-density-overlap-independent-audit.md
sources/reviews/2026-10-07-transport-v5-assembly.md
""".split())
GENERATED_FILES = frozenset(("SOURCE_MANIFEST.json", "MANIFEST.json", "SHA256SUMS", ARCHIVE_PATH))

class IntegrityError(ValueError):
    """A checked integrity failure (also raised in optimized Python)."""


def require(condition, code, message):
    if not condition:
        raise IntegrityError("{}: {}".format(code, message))


def safe_path(value, label="path"):
    require(isinstance(value, str) and bool(PATH_PATTERN.fullmatch(value)),
            "unsafe-path", "{} is not a portable relative path: {!r}".format(label, value))
    require(all(part not in (".", "..") for part in value.split("/")),
            "unsafe-path", "{} contains a dot component: {!r}".format(label, value))
    return value


def checked_root(root):
    root = Path(os.path.abspath(os.fspath(root)))
    mode = root.lstat().st_mode
    require(not stat.S_ISLNK(mode) and stat.S_ISDIR(mode),
            "unsafe-root", "package root must be a real directory")
    return root


def read_file(root, relative):
    relative = safe_path(relative)
    current = root
    parts = relative.split("/")
    for index, part in enumerate(parts):
        current = current / part
        try:
            mode = current.lstat().st_mode
        except FileNotFoundError:
            raise IntegrityError("missing-file: {}".format(relative)) from None
        require(not stat.S_ISLNK(mode), "symlink", relative)
        require(stat.S_ISREG(mode) if index == len(parts) - 1 else stat.S_ISDIR(mode),
                "special-file", relative)
    return current.read_bytes()


def scan_tree(root):
    """Return regular files/directories without following any symlink."""
    files, directories = set(), set()

    def walk(directory, prefix):
        with os.scandir(directory) as entries:
            for entry in sorted(entries, key=lambda item: item.name):
                relative = safe_path(prefix + entry.name)
                mode = entry.stat(follow_symlinks=False).st_mode
                require(not stat.S_ISLNK(mode), "symlink", relative)
                if stat.S_ISDIR(mode):
                    directories.add(relative)
                    walk(Path(entry.path), relative + "/")
                else:
                    require(stat.S_ISREG(mode), "special-file", relative)
                    files.add(relative)

    walk(root, "")
    return files, directories


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate-json-key", repr(key))
        result[key] = value
    return result


def reject_constant(value):
    raise IntegrityError("invalid-json: non-finite constant {}".format(value))


def load_json_bytes(data, label):
    try:
        result = json.loads(data.decode("utf-8"), object_pairs_hook=no_duplicate_keys,
                            parse_constant=reject_constant)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise IntegrityError("invalid-json: {}: {}".format(label, error)) from None
    require(isinstance(result, dict), "invalid-schema", label + " must be an object")
    return result


def load_json(root, relative):
    return load_json_bytes(read_file(root, relative), relative)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def git_blob_sha1(data):
    header = b"blob " + str(len(data)).encode("ascii") + b"\0"
    return hashlib.sha1(header + data).hexdigest()


def validate_digest_record(record, label):
    require(isinstance(record, dict), "invalid-schema", label + " must be an object")
    require(type(record.get("bytes")) is int and record["bytes"] >= 0,
            "invalid-size", label)
    require(isinstance(record.get("sha256"), str) and bool(HEX256.fullmatch(record["sha256"])),
            "invalid-sha256", label)


def check_bytes(data, record, label):
    validate_digest_record(record, label)
    require(len(data) == record["bytes"], "size-mismatch", label)
    require(sha256(data) == record["sha256"], "sha256-mismatch", label)


def file_records(document, label):
    require(type(document.get("schema_version")) is int and document["schema_version"] == 1,
            "invalid-schema", label + " requires schema_version 1")
    require(isinstance(document.get("files"), list), "invalid-schema", label + ".files")
    result = {}
    paths = []
    for record in document["files"]:
        require(isinstance(record, dict) and set(record) == {"path", "bytes", "sha256"},
                "invalid-schema", label + " file fields must be path, bytes, sha256")
        path = safe_path(record["path"], label + ".path")
        require(path not in result, "duplicate-entry", label + ": " + path)
        validate_digest_record(record, path)
        result[path] = record
        paths.append(path)
    require(paths == sorted(paths), "unsorted-entries", label)
    return result


def compare_sets(actual, expected, label):
    missing, extra = sorted(expected - actual), sorted(actual - expected)
    require(not missing and not extra, "inventory-mismatch",
            "{}; missing={!r}; extra={!r}".format(label, missing, extra))


def verify_mandatory_inventory(root, allow_missing_generated=False):
    files, _ = scan_tree(root)
    required = REQUIRED_RELEASE_FILES - GENERATED_FILES if allow_missing_generated else REQUIRED_RELEASE_FILES
    require(required <= files, "required-file", "mandatory release inventory missing: "
            + repr(sorted(required - files)))
    return files


def verify_manifest(root):
    records = file_records(load_json(root, "MANIFEST.json"), "MANIFEST.json")
    require(not (set(records) & MANIFEST_EXCLUSIONS), "manifest-recursion",
            "MANIFEST.json and SHA256SUMS must not be listed")
    required = REQUIRED_RELEASE_FILES - MANIFEST_EXCLUSIONS
    require(required <= set(records), "required-file", repr(sorted(required - set(records))))
    actual_files, actual_dirs = scan_tree(root)
    expected_files = set(records) | MANIFEST_EXCLUSIONS
    compare_sets(actual_files, expected_files, "release files")
    expected_dirs = set()
    for path in expected_files:
        parts = path.split("/")
        expected_dirs.update("/".join(parts[:index]) for index in range(1, len(parts)))
    compare_sets(actual_dirs, expected_dirs, "release directories")
    for path, record in records.items():
        check_bytes(read_file(root, path), record, path)
    return records


def verify_hash_list(root, records):
    data = read_file(root, "SHA256SUMS")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        raise IntegrityError("invalid-hash-list: SHA256SUMS is not UTF-8") from None
    require(text.endswith("\n"), "invalid-hash-list", "final newline is required")
    found = {}
    order = []
    for line in text.splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None, "invalid-hash-list", repr(line))
        digest, path = match.groups()
        safe_path(path, "SHA256SUMS.path")
        require(path not in found, "duplicate-entry", "SHA256SUMS: " + path)
        found[path] = digest
        order.append(path)
    require(order == sorted(order), "unsorted-entries", "SHA256SUMS")
    expected = set(records) | {"MANIFEST.json"}
    compare_sets(set(found), expected, "SHA256SUMS entries")
    for path in sorted(expected):
        require(sha256(read_file(root, path)) == found[path], "hash-list-mismatch", path)
    canonical = "".join("{}  {}\n".format(found[path], path) for path in sorted(found))
    require(data == canonical.encode("utf-8"), "invalid-hash-list", "noncanonical line endings")


def verify_dependencies(root):
    document = load_json(root, "DEPENDENCIES.json")
    inputs = document.get("inputs")
    require(isinstance(inputs, list) and len(inputs) == 57,
            "dependency-count", "DEPENDENCIES.json must contain exactly 57 inputs")
    paths, copies = set(), set()
    for record in inputs:
        require(isinstance(record, dict), "invalid-schema", "dependency input")
        path = safe_path(record.get("path"), "dependency.path")
        local = safe_path(record.get("local_copy"), "dependency.local_copy")
        require(path not in paths and local not in copies, "duplicate-entry", "dependency: " + path)
        paths.add(path)
        copies.add(local)
        require(local == "sources/" + path, "dependency-location", local)
        require(isinstance(record.get("git_blob"), str) and bool(HEX160.fullmatch(record["git_blob"])),
                "invalid-git-blob", path)
        data = read_file(root, local)
        check_bytes(data, record, local)
        require(git_blob_sha1(data) == record["git_blob"], "git-blob-mismatch", path)
    compare_sets(copies, REQUIRED_DEPENDENCY_FILES, "fixed dependency source paths")
    return len(inputs)


def extract_protected(data):
    start_marker, stop_marker = rb"\section{Exact overlap", rb"\section{Source-overlap"
    require(data.count(start_marker) == data.count(stop_marker) == 1,
            "section-markers", "each protected Section 1 boundary must occur exactly once")
    start, stop = data.index(start_marker), data.index(stop_marker)
    require(start < stop, "section-markers", "protected section boundaries are reversed")
    section = data[start:stop]
    environments, opened = [], None
    for token in ENV_TOKEN.finditer(data):
        direction, environment_type = token.group(1), token.group(2)
        if direction == b"begin":
            require(opened is None, "environment-structure", "nested protected environments")
            opened = (environment_type, token.start())
        else:
            require(opened is not None and opened[0] == environment_type,
                    "environment-structure", "unmatched protected environment end")
            environments.append((environment_type.decode("ascii"), data[opened[1]:token.end()]))
            opened = None
    require(opened is None, "environment-structure", "unclosed protected environment")
    require(len(environments) == 10, "environment-count", "expected exactly 10 protected environments")
    return section, environments


def verify_protected_math(root):
    provenance = load_json(root, "provenance/PROTECTED_MATHEMATICS.json")
    require(isinstance(provenance.get("source_sha256"), str)
            and bool(HEX256.fullmatch(provenance["source_sha256"])),
            "invalid-sha256", "protected prior source_sha256")
    section, environments = extract_protected(read_file(root, "synthesis.tex"))
    check_bytes(section, provenance.get("section_1"), "protected Section 1")
    records = provenance.get("environments")
    require(isinstance(records, list) and len(records) == 10,
            "environment-count", "provenance must pin exactly 10 protected environments")
    for index, ((environment_type, data), record) in enumerate(zip(environments, records), 1):
        require(isinstance(record, dict) and type(record.get("index")) is int
                and record["index"] == index and record.get("type") == environment_type,
                "environment-order", "protected environment {}".format(index))
        check_bytes(data, record, "protected {} {}".format(environment_type, index))
    return len(environments)


def source_eligible(path):
    return path not in SOURCE_EXCLUSIONS and not path.lower().endswith(".pdf")


def canonical_tar_bytes(root, records, manifest_bytes):
    """Build the specified USTAR stream; no filesystem metadata is inherited."""
    contents = {path: read_file(root, path) for path in records}
    contents["SOURCE_MANIFEST.json"] = manifest_bytes
    require(sum(map(len, contents.values())) < MAX_ARCHIVE_BYTES,
            "archive-size", "source contents exceed the 256 MiB safety limit")
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w", format=tarfile.USTAR_FORMAT) as archive:
        for path in sorted(contents):
            data = contents[path]
            member = tarfile.TarInfo(ARCHIVE_PREFIX + path)
            member.type = tarfile.REGTYPE
            member.size = len(data)
            member.uid = member.gid = member.mtime = 0
            member.uname = member.gname = ""
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    result = buffer.getvalue()
    require(len(result) < MAX_ARCHIVE_BYTES, "archive-size", "tar exceeds the 256 MiB safety limit")
    return result


def canonical_gzip_bytes(tar_bytes):
    buffer = io.BytesIO()
    with gzip.GzipFile(fileobj=buffer, mode="wb", filename="", mtime=0, compresslevel=9) as stream:
        stream.write(tar_bytes)
    return buffer.getvalue()


def verify_source_archive(root, release_records):
    manifest_bytes = read_file(root, "SOURCE_MANIFEST.json")
    document = load_json_bytes(manifest_bytes, "SOURCE_MANIFEST.json")
    records = file_records(document, "SOURCE_MANIFEST.json")
    require(document.get("archive") == ARCHIVE_PATH and document.get("prefix") == ARCHIVE_PREFIX,
            "archive-contract", "unexpected source archive path or member prefix")
    expected = {path for path in release_records if source_eligible(path)}
    compare_sets(set(records), expected, "source manifest files")
    for path, record in records.items():
        require(record == release_records[path], "source-record-mismatch", path)
        check_bytes(read_file(root, path), record, path)
    canonical_tar = canonical_tar_bytes(root, records, manifest_bytes)
    compressed = read_file(root, ARCHIVE_PATH)
    require(compressed[:10] == GZIP_HEADER, "gzip-metadata",
            "expected zero mtime, empty filename, level-9 gzip header")
    try:
        with gzip.GzipFile(fileobj=io.BytesIO(compressed), mode="rb") as stream:
            raw_tar = stream.read(len(canonical_tar) + 1)
            require(len(raw_tar) <= len(canonical_tar), "archive-size", "extra decompressed archive data")
    except (OSError, EOFError, zlib.error) as error:
        raise IntegrityError("invalid-gzip: {}".format(error)) from None
    expected_members = {ARCHIVE_PREFIX + path for path in records} | {ARCHIVE_PREFIX + "SOURCE_MANIFEST.json"}
    found, order = set(), []
    try:
        with tarfile.open(fileobj=io.BytesIO(raw_tar), mode="r:") as archive:
            for member in archive:
                safe_path(member.name, "archive member")
                require(member.name not in found, "duplicate-entry", "archive: " + member.name)
                require(member.name in expected_members, "unexpected-archive-member", member.name)
                require(member.type == tarfile.REGTYPE and not member.pax_headers,
                        "unsafe-archive-member", member.name)
                require(member.uid == member.gid == member.mtime == 0
                        and member.uname == member.gname == "" and member.mode == 0o644
                        and member.linkname == "" and member.devmajor == member.devminor == 0,
                        "archive-metadata", member.name)
                relative = member.name[len(ARCHIVE_PREFIX):]
                expected_data = manifest_bytes if relative == "SOURCE_MANIFEST.json" else read_file(root, relative)
                require(member.size == len(expected_data), "archive-member-size", member.name)
                stream = archive.extractfile(member)
                require(stream is not None, "archive-member-read", member.name)
                with stream:
                    actual_data = stream.read(len(expected_data) + 1)
                require(actual_data == expected_data, "archive-member-bytes", member.name)
                found.add(member.name)
                order.append(member.name)
    except tarfile.TarError as error:
        raise IntegrityError("invalid-tar: {}".format(error)) from None
    compare_sets(found, expected_members, "source archive members")
    require(order == sorted(order), "unsorted-entries", "archive members")
    require(raw_tar == canonical_tar, "noncanonical-tar", "USTAR encoding, padding, or trailing data differs")
    # Reject trailing compressed garbage, even if the gzip reader tolerates it.
    decoder = zlib.decompressobj(wbits=31)
    decoded = decoder.decompress(compressed, len(canonical_tar) + 1)
    require(decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail
            and decoded == canonical_tar, "gzip-trailing-data", "gzip must contain exactly one stream")
    return len(found)


def verify(root):
    root = checked_root(root)
    records = verify_manifest(root)
    verify_hash_list(root, records)
    dependencies = verify_dependencies(root)
    environments = verify_protected_math(root)
    members = verify_source_archive(root, records)
    return {"release_files": len(records) + 2, "dependency_inputs": dependencies,
            "protected_environments": environments, "archive_members": members}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("root", nargs="?", type=Path, default=Path(__file__).absolute().parent.parent,
                        help="release root (default: parent of this verification directory)")
    args = parser.parse_args(argv)
    try:
        result = verify(args.root)
    except (IntegrityError, OSError, ValueError, OverflowError, zlib.error) as error:
        print("FAIL: {}".format(error), file=sys.stderr)
        return 1
    print("PASS: {release_files} release files; {dependency_inputs} pinned inputs; protected Section 1 and "
          "{protected_environments} environments; {archive_members} canonical source archive members".format(**result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
