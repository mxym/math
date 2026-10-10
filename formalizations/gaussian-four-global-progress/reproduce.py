#!/usr/bin/env python3
"""Fresh source compilation and trust-zero replay; no old project objects are visible."""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
MODULES = json.loads((ROOT / "MODULES.json").read_text())
LEAN_COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def strip_comments(text: str) -> str:
    """Remove nested Lean block comments and line comments for the lexical screen."""
    out = []
    i = depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise RuntimeError("Unterminated Lean block comment")
    return "".join(out)


def source_snapshot() -> dict[str, str]:
    expected = json.loads((ROOT / "SOURCE_BLOBS.json").read_text())
    for rel, wanted in expected.items():
        path = ROOT / rel
        if not path.is_file() or git_blob(path.read_bytes()) != wanted:
            raise RuntimeError(f"Source blob mismatch: {rel}")
    for module in MODULES:
        text = (ROOT / MODULES[module]).read_text()
        if re.search(r"\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b", strip_comments(text)):
            raise RuntimeError(f"Forbidden trust extension or placeholder in {module}")
    return {rel: sha256(ROOT / rel) for rel in sorted(expected)}


def dependency_check(directory: Path, revision: str) -> dict:
    observed = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
    if observed != revision:
        raise RuntimeError(f"Dependency pin mismatch: {directory.name}: {observed} != {revision}")
    tree = subprocess.check_output(["git", "-C", str(directory), "ls-tree", "-rz", "--full-tree", "HEAD"])
    checked = 0
    mismatches = []
    configs = {"lakefile.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"}
    for entry in tree.split(b"\0"):
        if not entry:
            continue
        meta, raw_path = entry.split(b"\t", 1)
        mode, kind, expected = meta.decode().split()
        rel = raw_path.decode()
        if kind != "blob" or not (rel.endswith(".lean") or rel in configs):
            continue
        path = directory / rel
        if not path.exists():
            mismatches.append(rel + " (missing)")
            continue
        data = os.readlink(path).encode() if mode == "120000" else path.read_bytes()
        if git_blob(data.replace(b"\r\n", b"\n")) != expected:
            mismatches.append(rel)
        checked += 1
    if mismatches:
        raise RuntimeError(f"Modified pinned dependency sources in {directory}: {mismatches[:20]}")
    return {"revision": observed, "lf_normalized_git_blobs_checked": checked, "status": "PASS"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-dir", type=Path, default=ROOT / ".lake/packages/mathlib")
    parser.add_argument("--output-dir", type=Path, required=True, help="Must not already exist")
    parser.add_argument("--lean", default=shutil.which("lean"))
    args = parser.parse_args()
    if not args.lean:
        parser.error("Lean is not on PATH; activate the pinned toolchain first")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"status": "RUNNING", "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
              "module_order": MODULES, "commands": [], "scope": "PARTIAL four-cell formalization: separation, quartile profile, collinear obstruction, actual price compactness, upper normal cones and regularization residuals; NOT the global sharp theorem"}
    try:
        before = source_snapshot()
        report["source_sha256"] = before
        report["source_manifest_sha256"] = sha256(ROOT / "SOURCE_BLOBS.json")
        lean = Path(args.lean).resolve()
        version = subprocess.check_output([str(lean), "--version"], text=True).strip()
        if "version 4.34.1," not in version or LEAN_COMMIT not in version:
            raise RuntimeError(f"Unexpected Lean toolchain: {version}")
        report["lean_version"] = version
        report["lean_executable_sha256"] = sha256(lean)
        lock = json.loads((ROOT / "lake-manifest.json").read_text())
        mathlib = args.mathlib_dir.resolve()
        paths = []
        deps = {}
        dependency_dirs = {}
        for package in lock["packages"]:
            if package["type"] != "git":
                continue
            if package["name"] == "mathlib":
                directory = mathlib
            else:
                candidates = [mathlib.parent / package["name"], mathlib / ".lake/packages" / package["name"]]
                directory = next((p.resolve() for p in candidates if p.is_dir()), None)
                if directory is None:
                    raise RuntimeError(f"Missing dependency checkout: {package['name']}")
            deps[package["name"]] = dependency_check(directory, package["rev"])
            paths.append(str(directory / ".lake/build/lib/lean"))
            dependency_dirs[package["name"]] = directory
        report["dependencies"] = deps
        # Reconstruct repository-relative Lake packages with no owned objects.
        lake_source = output / "lake-source/formalizations/gaussian-four-global-progress"
        lake_source.mkdir(parents=True)
        for rel in before:
            target = lake_source / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, target)
        packages = lake_source / ".lake/packages"
        packages.mkdir(parents=True)
        for name, directory in dependency_dirs.items():
            (packages / name).symlink_to(directory, target_is_directory=True)
        lake_env = os.environ.copy()
        lake_env["PATH"] = str(lean.parent) + os.pathsep + lake_env.get("PATH", "")
        lake_env.pop("LEAN_PATH", None)
        lake_env.pop("LEAN_SRC_PATH", None)
        start = time.monotonic()
        with (output / "lake-build.log").open("w") as stream:
            lake_run = subprocess.run([str(lean.parent / "lake"), "build"], cwd=lake_source,
                env=lake_env, stdout=stream, stderr=subprocess.STDOUT, timeout=3600)
        report["fresh_lake_build"] = {"returncode": lake_run.returncode,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "log": "lake-build.log", "initial_owned_objects": 0}
        if lake_run.returncode:
            raise RuntimeError("Fresh Lake build failed; see lake-build.log")
        print("FRESH_LAKE_BUILD_PASS", flush=True)
        work = output / "fresh"
        work.mkdir()
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([str(work)] + paths)
        env.pop("LEAN_SRC_PATH", None)
        report["fresh_project_olean_count_before"] = len(list(work.glob("*.olean")))
        for module in MODULES:
            dest = work / (module.replace(".", "/") + ".lean")
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / MODULES[module], dest)

        def run(arguments: list[str], logfile: str, cwd: Path = work, expected_failure: bool = False) -> None:
            start = time.monotonic()
            with (output / logfile).open("w") as stream:
                proc = subprocess.run([str(lean)] + arguments, cwd=cwd, env=env,
                                      stdout=stream, stderr=subprocess.STDOUT, timeout=1800)
            text = (output / logfile).read_text(errors="replace")
            record = {"arguments": arguments, "cwd": str(cwd), "returncode": proc.returncode,
                      "elapsed_seconds": round(time.monotonic() - start, 3), "log": logfile}
            report["commands"].append(record)
            print(json.dumps(record), flush=True)
            if text:
                print(text, flush=True)
            if expected_failure:
                if proc.returncode == 0 or "error" not in text.lower():
                    raise RuntimeError(f"Negative control unexpectedly accepted: {logfile}")
                if any(s in text.lower() for s in ["unknown module prefix", "object file", "already been declared"]):
                    raise RuntimeError(f"Negative control failed for an infrastructure reason: {logfile}")
            elif proc.returncode != 0:
                raise RuntimeError(f"Compilation/replay failed: {logfile}")

        for module in MODULES:
            relative = module.replace(".", "/")
            run(["-o", f"{relative}.olean", f"{relative}.lean"], f"build-{module}.log")
        report["object_sha256"] = {str(p.relative_to(work)): sha256(p) for p in sorted(work.rglob("*.olean"))}
        for name in ["Audit", "Replay"]:
            shutil.copyfile(ROOT / "audit" / f"{name}.lean", work / f"{name}.lean")
            run([f"{name}.lean"], f"{name.lower()}.log")
        replay_log = (output / "replay.log").read_text()
        match = re.search(r"EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero", replay_log)
        if not match:
            raise RuntimeError("The replay completion marker is missing")
        axioms = set((work / "replayed-axioms.txt").read_text().splitlines())
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"Unexpected replayed axioms: {sorted(axioms)}")
        report["empty_kernel_replay"] = {"status": "PASS", "trust_level": 0,
            "declarations": int(match.group(1)), "roots": int(match.group(2)), "axioms": sorted(axioms)}
        for name in ["replayed-axioms.txt", "replayed-closure.txt"]:
            shutil.copyfile(work / name, output / name)
        controls = [
            ("GaussianFour.Profile", "quarterQuantile < 7 / 10 := by", "quarterQuantile < 0 := by"),
            ("GaussianFour.QuartileIntervals", "a = -quarterQuantile ∧ b = 0 ∧ c = quarterQuantile", "a = quarterQuantile ∧ b = 0 ∧ c = quarterQuantile"),
            ("GaussianFour.QuartileIntervals", "![-quarterDensity, quarterDensity - standardDensity 0,", "![quarterDensity, quarterDensity - standardDensity 0,")]
        controls += [
            ("GaussianFour.PriceBounds", "|b i - b j| ≤ quarterQuantile * ‖v i - v j‖", "|b i - b j| ≤ 0 * ‖v i - v j‖"),
            ("GaussianFour.NormalCone", "(A * (Y - Q)).trace ≤ 0", "(A * (Y - Q)).trace ≥ 0"),
            ("GaussianFour.RegularizedResidual", "ε * (L * Q).trace ^ 2 := by", "0 * (L * Q).trace ^ 2 := by")]
        report["negative_controls"] = []
        for index, (module, old, new) in enumerate(controls, 1):
            text = (ROOT / MODULES[module]).read_text()
            if text.count(old) != 1:
                raise RuntimeError(f"Ambiguous negative-control mutation: {module}")
            directory = output / f"negative-{index}"
            directory.mkdir()
            relative = module.replace(".", "/")
            (directory / relative).parent.mkdir(parents=True, exist_ok=True)
            (directory / f"{relative}.lean").write_text(text.replace(old, new))
            run(["-o", f"{relative}.olean", f"{relative}.lean"], f"negative-{index}.log", directory, True)
            report["negative_controls"].append({"module": module, "old": old, "new": new, "status": "REJECTED"})
        if before != source_snapshot():
            raise RuntimeError("Source files changed during verification")
        report["source_hashes_unchanged"] = True
        report["status"] = "PASS"
        return 0
    except Exception as exc:
        report["status"] = "FAIL"
        report["error"] = str(exc)
        print(f"VERIFICATION_FAIL: {exc}", file=sys.stderr, flush=True)
        return 1
    finally:
        report["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        (output / "verification.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print("VERIFICATION_REPORT_BEGIN", flush=True)
        print(json.dumps(report, sort_keys=True), flush=True)
        print("VERIFICATION_REPORT_END", flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
