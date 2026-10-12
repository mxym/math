#!/usr/bin/env python3
"""Create deterministic source and complete supplement archives.

Uses only Python's standard library. Run after the article and recorded
verification output are ready. Sources and reports are pinned by an exact whitelist;
build intermediates and external dependency checkouts are never collected.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "notes/quantitative-symmetric-projection-stability-bibliographic-correction"
NAME = "quantitative-symmetric-projection-stability-bibliographic-correction"
PIN = "6785c1c830f8e19e2eb07b0bb89f4d475a8b154a"
SOURCE_FILES = (
    'AUDIT.md',
    'BUILD.md',
    'CORRECTIONS.md',
    'DEPENDENCIES.json',
    'DEPENDENCIES.md',
    'LITERATURE.md',
    'PDF_QA.md',
    'PRIMARY_LOCATORS.md',
    'PUBLICATION.md',
    'README.md',
    'RELEASE_WHITELIST.txt',
    'VERIFICATION.md',
    'build.sh',
    'code/check_balanced_defect.py',
    'code/check_editorial.py',
    'code/check_package.py',
    'code/check_rank_identities.py',
    'code/check_truncation_obstruction.py',
    'code/dependency-inputs.json',
    'code/package_release.py',
    'code/verify.py',
    'corrections/LITERATURE.md.patch',
    'corrections/baseline-identifiers.json',
    'corrections/editorial-replacements.json',
    'corrections/paper.md.patch',
    'corrections/public-proposal-source-check.json',
    'corrections/supporting-documentation.patch',
    'corrections/unchanged-mathematical-files.json',
    'corrections/v4-attribution.patch',
    'corrections/v4-paper.after.md',
    'corrections/v4-paper.before.md',
    'header.tex',
    'paper.md',
    'paper.tex',
    'results/balanced_defect.log',
    'results/build.json',
    'results/corrected-package-replay.json',
    'results/corrected-replay.json',
    'results/editorial-preservation.json',
    'results/package-tests.json',
    'results/rank_identities.log',
    'results/truncation_obstruction.log',
    'results/typeset.log',
    'results/verification.json',
    'results/with-dependencies/balanced_defect.log',
    'results/with-dependencies/inherited/v2.json',
    'results/with-dependencies/inherited/v2.log',
    'results/with-dependencies/inherited/v3.json',
    'results/with-dependencies/inherited/v3.log',
    'results/with-dependencies/inherited/v4.log',
    'results/with-dependencies/rank_identities.log',
    'results/with-dependencies/truncation_obstruction.log',
    'results/with-dependencies/verification.json',
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def manifest(names: list[str], schema: str) -> bytes:
    records = {}
    for name in sorted(names):
        path = ROOT / name
        if not path.is_file() or path.is_symlink():
            raise RuntimeError(f"Missing or symlinked source: {name}")
        data = path.read_bytes()
        records[name] = {"bytes": len(data), "sha256": digest(data)}
    return (json.dumps({
        "schema": schema, "date": "2026-10-07", "archive_prefix": PREFIX,
        "dependency_commit": PIN, "files": records,
        "release_kind": "separate bibliographic correction; original release immutable",
        "baseline_paper_sha256": "08f6f55c6a694da05d348d3dcbda18be186044fd39570c51bf786507aaef862c",
        "scope": "Byte identity and packaging; not mathematical certification.",
    }, indent=2, sort_keys=True) + "\n").encode("utf-8")


def write_archive(path: Path, names: list[str]) -> dict:
    with ZipFile(path, "w", ZIP_DEFLATED, compresslevel=9) as archive:
        for name in sorted(names):
            entry = ZipInfo(f"{PREFIX}/{name}", date_time=(2026, 10, 7, 0, 0, 0))
            entry.create_system = 3
            mode = 0o100755 if name.endswith((".sh", ".py")) else 0o100644
            entry.external_attr = mode << 16
            entry.compress_type = ZIP_DEFLATED
            archive.writestr(entry, (ROOT / name).read_bytes(), compresslevel=9)
    data = path.read_bytes()
    return {"file": path.name, "bytes": len(data), "sha256": digest(data)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "dist")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    if output == ROOT or output == ROOT / "code" or output == ROOT / "results":
        raise RuntimeError("Use a separate archive output directory.")
    source = list(SOURCE_FILES)
    (ROOT / "SOURCE_MANIFEST.json").write_bytes(
        manifest(source, "quantitative-symmetric-projection-stability-source-v1"))
    complete = source + ["SOURCE_MANIFEST.json", "paper.pdf"]
    (ROOT / "MANIFEST.json").write_bytes(
        manifest(complete, "quantitative-symmetric-projection-stability-complete-v1"))
    output.mkdir(parents=True, exist_ok=True)
    archives = [
        write_archive(output / f"{NAME}-source.zip", source + ["SOURCE_MANIFEST.json"]),
        write_archive(output / f"{NAME}.zip", complete + ["MANIFEST.json"]),
    ]
    sums = "".join(f"{record['sha256']}  {record['file']}\n" for record in archives)
    (output / "SHA256SUMS").write_text(sums)
    print(json.dumps({"status": "packaged", "archives": archives}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
