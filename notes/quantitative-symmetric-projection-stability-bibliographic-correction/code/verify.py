#!/usr/bin/env python3
"""Replay the finite exact checks without a repository or external packages.

Python 3.10 or newer. Reports are written only beneath --output-dir, after
preflight and every requested check succeed. The optional dependency checkout
must have the pinned Git HEAD and matching working-file hashes. Its checkers
run only with --run-inherited-checks; they receive explicit temporary report
paths and never use their source-tree report defaults.

These finite computations supplement the English proof in paper.md. They do
not formally verify its general measure-theoretic or convex-geometric claims.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
from tempfile import NamedTemporaryFile, TemporaryDirectory


ROOT = Path(__file__).resolve().parents[1]
CODE = ROOT / "code"
PIN = "6785c1c830f8e19e2eb07b0bb89f4d475a8b154a"
BASE = "preprints/005-simplex-product-optimum"
CASES = (
    ("balanced_defect", 4930),
    ("rank_identities", 750),
    ("truncation_obstruction", 16),
)
REQUIRED_INPUTS = frozenset(
    [f"{BASE}/{version}/paper.md" for version in ("v2", "v3", "v4")]
    + [f"{BASE}/{version}/{suffix}"
       for version in ("v2", "v3")
       for suffix in ("code/check.py", "certificates/exact.json", "results/check.json")]
    + [f"{BASE}/v4/code/check_examples.py"]
)


class VerificationError(Exception):
    """A failed explicit check; unaffected by Python optimization."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def is_inside(path: Path, parent: Path) -> bool:
    return path == parent or parent in path.parents


def checked_run(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
    require(
        result.returncode == 0,
        f"Command failed ({result.returncode}): {command[0]} "
        f"{' '.join(command[1:])}\n{result.stderr.strip()}",
    )
    return result


def validate_output_path(output: Path, checkout: Path | None) -> None:
    # Protect all shipped files, including results/. Only build/ is writable
    # within the package. Resolving paths also resolves existing symlinks.
    require(output != ROOT / "build", "Use a separate subdirectory of build/.")
    require(
        not is_inside(output, ROOT) or is_inside(output, ROOT / "build"),
        "An output directory inside the package must be below build/.",
    )
    require(not is_inside(ROOT, output), "Output must not contain the source package.")
    if checkout is not None:
        require(
            not is_inside(output, checkout) and not is_inside(checkout, output),
            "Output and dependency checkout must be separate directories.",
        )
    if output.exists():
        require(output.is_dir(), "The output path exists and is not a directory.")


def validate_dependencies(checkout: Path) -> dict:
    """Read-only preflight; no output path is created or changed here."""
    require(checkout.is_dir(), "Dependency checkout does not exist or is not a directory.")
    manifest = json.loads((CODE / "dependency-inputs.json").read_text())
    require(
        manifest.get("schema") == "upper-end-stability-dependency-inputs-v1",
        "Unsupported dependency manifest schema.",
    )
    require(manifest.get("commit") == PIN, "Dependency manifest commit is not the pinned commit.")
    require(set(manifest.get("inputs", {})) == REQUIRED_INPUTS, "Unexpected dependency input set.")
    head = checked_run(["git", "rev-parse", "--verify", "HEAD^{commit}"], checkout).stdout.strip()
    require(head == PIN, f"Dependency HEAD is {head}; required {PIN}.")
    hashes = {}
    for name, expected in sorted(manifest["inputs"].items()):
        relative = PurePosixPath(name)
        require(
            not relative.is_absolute() and ".." not in relative.parts,
            f"Invalid dependency path: {name}",
        )
        path = checkout.joinpath(*relative.parts)
        require(path.is_file(), f"Missing dependency input: {name}")
        require(is_inside(path.resolve(), checkout), f"Dependency input leaves checkout: {name}")
        data = path.read_bytes()
        digest = sha256(data)
        require(digest == expected["sha256"], f"Dependency SHA-256 mismatch: {name}")
        require(len(data) == expected["bytes"], f"Dependency byte count mismatch: {name}")
        hashes[name] = digest
    return {
        "status": "passed",
        "repository": manifest["repository"],
        "commit": head,
        "working_file_hashes": hashes,
        "scope": "Pinned HEAD and specified inputs only; other checkout files are not audited.",
    }


def scratch_parent(checkout: Path | None) -> Path:
    """Respect a safe ambient temp directory, otherwise use an OS temp path."""
    # Avoid gettempdir(): its first-call writability probe can itself create a
    # file beneath an unsafe ambient TMPDIR before we have filtered the path.
    candidates = [Path(value) for variable in ("TMPDIR", "TEMP", "TMP")
                  if (value := os.environ.get(variable))]
    candidates += [Path("/tmp"), Path("/var/tmp"), Path.cwd()]
    for candidate in candidates:
        resolved = candidate.resolve()
        if is_inside(resolved, ROOT) or (checkout and is_inside(resolved, checkout)):
            continue
        if resolved.is_dir() and os.access(resolved, os.W_OK):
            return resolved
    raise VerificationError("No writable temporary directory outside source trees is available.")


def replay_standalone(case: tuple[str, int], scratch: Path) -> tuple[dict, dict[str, bytes]]:
    name, expected_count = case
    script = CODE / f"check_{name}.py"
    ordinary = checked_run([sys.executable, "-B", str(script)], scratch)
    optimized = checked_run([sys.executable, "-B", "-O", str(script)], scratch)
    require(ordinary.stdout == optimized.stdout, f"Ordinary/optimized output differs: {name}")
    require(not ordinary.stderr and not optimized.stderr, f"Unexpected stderr: {name}")
    if name == "balanced_defect":
        data = json.loads(ordinary.stdout)
        actual_count = data["total_cases"]
        require(data["status"] == "passed", "Balanced-defect report did not pass.")
    elif name == "rank_identities":
        match = re.fullmatch(
            r"Exact Fraction audit passed: (\d+) omitted-index cofactor identities "
            r"in dimensions 3 through 7 \(seed 541\)\.\n", ordinary.stdout
        )
        require(match is not None, "Unexpected cofactor checker output.")
        actual_count = int(match.group(1))
    else:
        lines = ordinary.stdout.splitlines()
        require(lines[-1] == "16 exact facet-minor cases verified independently.",
                "Unexpected corner-truncation summary.")
        actual_count = sum(line.endswith("; exact minors PASS") for line in lines)
    require(actual_count == expected_count, f"Unexpected case count: {name}")
    result = {
        "name": name,
        "status": "passed",
        "exact_cases": actual_count,
        "ordinary_and_optimized_outputs_identical": True,
        "source": f"code/{script.name}",
        "source_sha256": sha256(script.read_bytes()),
        "stdout": ordinary.stdout,
    }
    files = {f"{name}.log": ordinary.stdout.encode("utf-8")}
    return result, files


def replay_inherited(version: str, checkout: Path, scratch: Path) -> tuple[dict, dict[str, bytes]]:
    source = checkout / BASE / version
    files = {}
    outputs = []
    reports = []
    for label, optimize in (("ordinary", False), ("optimized", True)):
        command = [sys.executable, "-B"] + (["-O"] if optimize else [])
        if version == "v4":
            command += [str(source / "code/check_examples.py")]
        else:
            destination = scratch / f"{version}-{label}.json"
            command += [str(source / "code/check.py"), str(source / "certificates/exact.json"),
                        "--self-test", "--report", str(destination)]
        run = checked_run(command, scratch)
        require(not run.stderr, f"Unexpected inherited-check stderr: {version}/{label}")
        outputs.append(run.stdout)
        if version != "v4":
            reports.append(destination.read_bytes())
    require(outputs[0] == outputs[1], f"Inherited ordinary/optimized stdout differs: {version}")
    if reports:
        require(reports[0] == reports[1], f"Inherited ordinary/optimized reports differ: {version}")
        reference = (source / "results/check.json").read_bytes()
        require(reports[0] == reference, f"Inherited report differs from pinned reference: {version}")
        files[f"inherited/{version}.json"] = reports[0]
    files[f"inherited/{version}.log"] = outputs[0].encode("utf-8")
    return {
        "version": version,
        "status": "passed",
        "ordinary_and_optimized_outputs_identical": True,
        "report_matches_pinned_reference": True if reports else None,
        "stdout": outputs[0],
    }, files


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir", type=Path, default=ROOT / "build/verification",
        help="Separate report directory (default: package build/verification).",
    )
    parser.add_argument(
        "--dependency-checkout", type=Path,
        help="Optional external mxym/math checkout at the exact pinned commit.",
    )
    parser.add_argument(
        "--run-inherited-checks", action="store_true",
        help="Also replay v2–v4 checkers; requires --dependency-checkout.",
    )
    args = parser.parse_args()
    require(sys.version_info >= (3, 10), "Python 3.10 or newer is required.")
    require(not args.run_inherited_checks or args.dependency_checkout is not None,
            "--run-inherited-checks requires --dependency-checkout.")
    checkout = args.dependency_checkout.resolve() if args.dependency_checkout else None
    output = args.output_dir.resolve()
    validate_output_path(output, checkout)
    dependency = validate_dependencies(checkout) if checkout else None
    for name, _ in CASES:
        require((CODE / f"check_{name}.py").is_file(), f"Missing standalone checker: {name}")
    # Every process and its optional temporary report stay outside both source
    # trees. Output is not touched until all requested checks have passed.
    files = {}
    with TemporaryDirectory(prefix="upper-end-verification-", dir=scratch_parent(checkout)) as temporary:
        scratch = Path(temporary)
        with ThreadPoolExecutor(max_workers=3) as pool:
            replayed = list(pool.map(lambda case: replay_standalone(case, scratch), CASES))
        tests = []
        for result, generated in replayed:
            tests.append(result)
            files.update(generated)
        inherited = []
        if args.run_inherited_checks:
            with ThreadPoolExecutor(max_workers=3) as pool:
                replayed_inherited = list(pool.map(
                    lambda version: replay_inherited(version, checkout, scratch), ("v2", "v3", "v4")
                ))
            for result, generated in replayed_inherited:
                inherited.append(result)
                files.update(generated)
    report = {
        "schema": "upper-end-stability-verification-v1",
        "status": "passed",
        "arithmetic": "Exact integers and fractions.Fraction; no third-party packages.",
        "python": sys.version.split()[0],
        "new_exact_cases": sum(test["exact_cases"] for test in tests),
        "ordinary_and_optimized_outputs_identical": True,
        "tests": tests,
        "dependency_validation": dependency,
        "inherited_checks_requested": args.run_inherited_checks,
        "inherited_checks": inherited,
        "driver_sha256": sha256(Path(__file__).read_bytes()),
        "verification_scope": (
            "Finite exact regressions only. General probability-law, "
            "measure-theoretic and convex-geometric assertions are written "
            "proofs in paper.md; these checks are not formal proof verification."
        ),
    }
    files["verification.json"] = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8")
    # Check every destination before any output mutation. Atomic replacement
    # severs any preexisting hardlink rather than writing through to its inode.
    for name in files:
        destination = output / name
        require(is_inside(destination.resolve(), output), f"Report path leaves output: {name}")
        require(not destination.is_dir(), f"Report destination is a directory: {name}")
    output.mkdir(parents=True, exist_ok=True)
    for name, data in sorted(files.items()):
        destination = output / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        temporary_file = None
        try:
            with NamedTemporaryFile(prefix=".verification-", dir=destination.parent, delete=False) as stream:
                temporary_file = Path(stream.name)
                stream.write(data)
            os.replace(temporary_file, destination)
            temporary_file = None
        finally:
            if temporary_file is not None:
                temporary_file.unlink(missing_ok=True)
    print(json.dumps({
        "status": "passed", "new_exact_cases": report["new_exact_cases"],
        "ordinary_and_optimized_outputs_identical": True,
        "dependency_validation": dependency["status"] if dependency else "not requested",
        "inherited_checks": [test["version"] for test in inherited],
        "report": str(output / "verification.json"),
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (VerificationError, OSError, ValueError, KeyError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        raise SystemExit(1)
