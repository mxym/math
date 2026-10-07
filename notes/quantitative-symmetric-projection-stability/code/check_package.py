#!/usr/bin/env python3
"""Regression tests for archive portability and safe verification output.

Python 3.10+, standard library only; Git is used solely for a local negative
fixture. Tests extract a minimal self-contained source archive, run its driver
from an unrelated directory in ordinary and optimized Python, and check that
invalid dependency inputs fail before output creation or modification. This
tests packaging behavior, not mathematical claims.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import NamedTemporaryFile, TemporaryDirectory
from zipfile import ZipFile, ZIP_DEFLATED


ROOT = Path(__file__).resolve().parents[1]
FILES = (
    "code/verify.py", "code/dependency-inputs.json",
    "code/check_balanced_defect.py", "code/check_rank_identities.py",
    "code/check_truncation_obstruction.py",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def snapshot(directory: Path, ignore_build: bool = False) -> dict[str, str]:
    result = {}
    for file in sorted(directory.rglob("*")):
        if not file.is_file():
            continue
        relative = file.relative_to(directory)
        if ignore_build and relative.parts[0] == "build":
            continue
        result[str(relative)] = hashlib.sha256(file.read_bytes()).hexdigest()
    return result


def run(command: list[str], cwd: Path, expect_success: bool = True,
        environment: dict[str, str] | None = None,
        stdin: str | None = None) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                            env=environment, input=stdin)
    require(
        (result.returncode == 0) == expect_success,
        f"Unexpected exit code {result.returncode}: {command}\n{result.stdout}\n{result.stderr}",
    )
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, help="Optional packaging-test report outside shipped results/.")
    parser.add_argument("--dependency-checkout", type=Path,
                        help="Optional pinned checkout for positive and corrupt-hash preflight tests.")
    args = parser.parse_args()
    report_path = args.report.resolve() if args.report else None
    dependency_checkout = args.dependency_checkout.resolve() if args.dependency_checkout else None
    if report_path is not None:
        require(
            ROOT not in report_path.parents or ROOT / "build" in report_path.parents,
            "An internal test report must be below build/.",
        )
        require(not report_path.is_dir(), "The test report path is a directory.")
        require(
            dependency_checkout is None or
            (report_path != dependency_checkout and dependency_checkout not in report_path.parents),
            "The test report must be outside the supplied dependency checkout.",
        )
    # Keep fixtures out of the release tree even if ambient TMPDIR points there.
    candidates = [Path(value).resolve() for variable in ("TMPDIR", "TEMP", "TMP")
                  if (value := os.environ.get(variable))]
    candidates += [Path("/tmp"), Path("/var/tmp"), Path.cwd()]
    temporary_parent = next((path for path in candidates
                             if path.is_dir() and os.access(path, os.W_OK)
                             and path != ROOT and ROOT not in path.parents
                             and (dependency_checkout is None or
                                  (path != dependency_checkout and dependency_checkout not in path.parents))), None)
    require(temporary_parent is not None, "No writable temporary directory outside source package.")
    optional_checks = []
    with TemporaryDirectory(prefix="upper-end-package-test-", dir=temporary_parent) as temporary:
        scratch = Path(temporary)
        archive = scratch / "source.zip"
        with ZipFile(archive, "w", ZIP_DEFLATED) as zipped:
            for name in FILES:
                zipped.writestr(name, (ROOT / name).read_bytes())
            zipped.writestr("results/reference.json", '{"immutable": true}\n')
        extracted = scratch / "unpacked"
        with ZipFile(archive) as zipped:
            zipped.extractall(extracted)
        require(not (extracted / "repo").exists(), "Archive fixture unexpectedly includes a checkout.")
        default_output = extracted / "build/verification"
        default_output.mkdir(parents=True)
        os.link(extracted / "results/reference.json", default_output / "balanced_defect.log")
        initial = snapshot(extracted, ignore_build=True)
        driver = extracted / "code/verify.py"
        ordinary = run([sys.executable, "-B", str(driver)], scratch)
        first = json.loads((default_output / "verification.json").read_text())
        require(first["new_exact_cases"] == 5696, "Clean archive did not run all exact checks.")
        require(first["dependency_validation"] is None, "Standalone mode attempted dependency validation.")
        require(snapshot(extracted, ignore_build=True) == initial, "Standalone replay changed shipped inputs.")
        before_external = snapshot(extracted)
        external_output = scratch / "external-verification"
        environment = dict(os.environ)
        environment["TMPDIR"] = str(extracted / "code")
        optimized = run([sys.executable, "-B", "-O", str(driver),
                         "--output-dir", str(external_output)], scratch, environment=environment)
        require(snapshot(default_output) == snapshot(external_output),
                "Ordinary and optimized archive-driver reports differ.")
        require(snapshot(extracted) == before_external, "External-output replay changed the source package.")

        # A real local Git checkout at a deliberately different HEAD exercises
        # the commit check without relying on any preexisting repository.
        invalid_checkout = scratch / "wrong-commit"
        run(["git", "init", "--quiet", str(invalid_checkout)], scratch)
        run(["git", "-c", "user.name=Package Test", "-c", "user.email=package-test@example.invalid",
             "commit", "--quiet", "--allow-empty", "-m", "Local packaging negative fixture"], invalid_checkout)
        before = snapshot(external_output)
        rejected = run([sys.executable, "-B", str(driver), "--output-dir", str(external_output),
                        "--dependency-checkout", str(invalid_checkout)], scratch, expect_success=False)
        require("required 6785c1c" in rejected.stderr, "Wrong dependency HEAD did not reach the pin check.")
        require(snapshot(external_output) == before, "Failed dependency preflight changed existing output.")
        absent_output = scratch / "not-created"
        run([sys.executable, "-B", str(driver), "--output-dir", str(absent_output),
             "--dependency-checkout", str(invalid_checkout)], scratch, expect_success=False)
        require(not absent_output.exists(), "Failed dependency preflight created output.")

        # An explicit output path cannot overwrite the shipped report directory.
        run([sys.executable, "-B", str(driver), "--output-dir", str(extracted / "results")],
            scratch, expect_success=False)
        require(snapshot(extracted, ignore_build=True) == initial, "Rejected output path changed shipped files.")
        before = snapshot(external_output)
        run([sys.executable, "-B", str(driver), "--output-dir", str(external_output),
             "--run-inherited-checks"], scratch, expect_success=False)
        require(snapshot(external_output) == before, "Missing dependency argument changed output.")
        require(not ordinary.stderr and not optimized.stderr, "Successful archive replay emitted stderr.")

        if dependency_checkout is not None:
            checkout = dependency_checkout
            manifest = json.loads((extracted / "code/dependency-inputs.json").read_text())
            pin = manifest["commit"]
            validated = run([sys.executable, "-B", str(driver), "--output-dir", str(external_output),
                             "--dependency-checkout", str(checkout)], scratch)
            report = json.loads((external_output / "verification.json").read_text())
            require(report["dependency_validation"]["status"] == "passed", "Positive dependency preflight failed.")
            require(report["inherited_checks"] == [], "Validation-only mode ran inherited checkers.")
            # Construct a minimal isolated fixture carrying the genuine commit
            # object and copied pinned inputs, then corrupt one working file.
            # Neither the supplied checkout nor its reports are changed.
            fixture = scratch / "corrupt-pinned-input"
            run(["git", "init", "--quiet", str(fixture)], scratch)
            commit_data = run(["git", "cat-file", "commit", pin], checkout).stdout
            fixture_commit = run(["git", "hash-object", "-t", "commit", "-w", "--stdin"],
                                 fixture, stdin=commit_data).stdout.strip()
            require(fixture_commit == pin, "Pinned commit object did not copy exactly.")
            (fixture / ".git/HEAD").write_text(pin + "\n")
            for name in manifest["inputs"]:
                target = fixture / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((checkout / name).read_bytes())
            corrupted = fixture / "preprints/005-simplex-product-optimum/v2/paper.md"
            corrupted.write_bytes(corrupted.read_bytes() + b"\ncorrupt hash fixture\n")
            before = snapshot(external_output)
            invalid = run([sys.executable, "-B", str(driver), "--output-dir", str(external_output),
                           "--dependency-checkout", str(fixture)], scratch, expect_success=False)
            require("SHA-256 mismatch" in invalid.stderr, "Corrupted input did not reach hash validation.")
            require(snapshot(external_output) == before, "Hash mismatch changed existing output.")
            run([sys.executable, "-B", str(driver), "--output-dir", str(absent_output),
                 "--dependency-checkout", str(fixture)], scratch, expect_success=False)
            require(not absent_output.exists(), "Hash mismatch created output.")
            require(not validated.stderr, "Positive validation-only replay emitted stderr.")
            optional_checks = [
                "Pinned checkout validates without running inherited checkers.",
                "Corrupted working-file hash at pinned HEAD preserves existing output.",
                "Corrupted working-file hash at pinned HEAD creates no output.",
            ]
    report = {
        "schema": "upper-end-stability-packaging-test-v1",
        "status": "passed",
        "checks": [
            "Extracted archive runs from unrelated cwd without a repository.",
            "Default output is unpacked-package/build/verification.",
            "Explicit external output works in optimized Python.",
            "Ordinary and optimized driver reports are byte-identical.",
            "All 5696 exact cases pass in each archive-driver run.",
            "Shipped inputs and reference reports are unchanged.",
            "Atomic report replacement preserves hardlinked shipped reference files.",
            "Unsafe TMPDIR is ignored; external-output replay changes no package files.",
            "Wrong dependency HEAD leaves existing output byte-identical.",
            "Wrong dependency HEAD creates no new output directory.",
            "Writing into shipped results/ is rejected before mutation.",
            "Inherited replay without dependency argument is rejected before mutation.",
        ] + optional_checks,
        "scope": "Package behavior only; not mathematical proof verification.",
    }
    serialized = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if report_path is not None:
        report_path.parent.mkdir(parents=True, exist_ok=True)
        temporary_file = None
        try:
            with NamedTemporaryFile(prefix=".package-test-", dir=report_path.parent, delete=False) as stream:
                temporary_file = Path(stream.name)
                stream.write(serialized.encode("utf-8"))
            os.replace(temporary_file, report_path)
            temporary_file = None
        finally:
            if temporary_file is not None:
                temporary_file.unlink(missing_ok=True)
    print(serialized, end="")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, OSError, ValueError, KeyError) as error:
        print(f"Package regression failed: {error}", file=sys.stderr)
        raise SystemExit(1)
