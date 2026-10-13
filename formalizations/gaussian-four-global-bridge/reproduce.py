#!/usr/bin/env python3
"""Fresh Lake/direct builds, source pins, trust-zero replay, and false-claim rejection.
Only the partial analytic core is certified, never the two unproved target propositions.
Dependency caches may be reused; every owned/base source module is rebuilt from scratch.
"""
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
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def canonical(path: Path) -> bytes:
    return path.read_bytes().replace(b"\r\n", b"\n")


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def lean_code(text: str) -> str:
    """Remove nested Lean comments and strings before the lexical safety audit."""
    out = []
    i = depth = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth:
            if text.startswith("-/", i):
                depth -= 1; i += 2
            else:
                i += 1
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            continue
        if text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\": i += 2; continue
                if text[i] == '"': i += 1; break
                i += 1
            out.append(" ")
            continue
        out.append(text[i]); i += 1
    if depth:
        raise RuntimeError("Unterminated source comment")
    return "".join(out)


def source_path(module: str, registry: dict) -> Path:
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", module):
        raise RuntimeError(f"Invalid module name: {module}")
    directory = ROOT.parent / "gaussian-measure-primal-dual" if module in registry["base"] else ROOT
    return directory / f"{module}.lean"


def source_snapshot(registry: dict) -> tuple[dict, dict]:
    expected = json.loads((ROOT / "SOURCE_BLOBS.json").read_text())
    canonical_hashes, raw_hashes = {}, {}
    for rel, wanted in expected.items():
        path = (ROOT / rel).resolve()
        if not path.is_relative_to(ROOT.parent) or not path.is_file():
            raise RuntimeError(f"Source path is unavailable or outside formalizations: {rel}")
        if git_blob(canonical(path)) != wanted:
            raise RuntimeError(f"LF-normalized source blob mismatch: {rel}")
        canonical_hashes[rel] = digest(canonical(path))
        raw_hashes[rel] = sha256(path)
    for module in registry["base"] + registry["proof"] + registry["entry"] + registry["target_statements"]:
        code = lean_code(source_path(module, registry).read_text())
        if re.search(r"\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern|run_cmd|elab|macro)\b", code):
            raise RuntimeError(f"Forbidden trust extension or placeholder in {module}")
        if "skipKernelTC" in code:
            raise RuntimeError(f"Kernel checking cannot be disabled: {module}")
    return canonical_hashes, raw_hashes


def dependency_check(directory: Path, revision: str) -> dict:
    """Check the actual tracked Lean/config bytes, not just the Git HEAD label."""
    observed = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
    if observed != revision:
        raise RuntimeError(f"Dependency pin mismatch: {directory}: {observed} != {revision}")
    tree = subprocess.check_output(["git", "-C", str(directory), "ls-tree", "-rz", "--full-tree", "HEAD"])
    checked, mismatches = 0, []
    configs = {"lakefile.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"}
    for entry in tree.split(b"\0"):
        if not entry: continue
        meta, raw_path = entry.split(b"\t", 1)
        mode, kind, expected = meta.decode().split()
        rel = raw_path.decode()
        if kind != "blob" or not (rel.endswith(".lean") or rel in configs): continue
        path = directory / rel
        if not path.exists():
            mismatches.append(rel + " (missing)"); continue
        data = os.readlink(path).encode() if mode == "120000" else path.read_bytes()
        if git_blob(data.replace(b"\r\n", b"\n")) != expected: mismatches.append(rel)
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
    if not args.lean: parser.error("Activate Lean 4.34.1 first, or provide --lean")
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"status": "RUNNING", "scope": "PARTIAL analytic core; global bound and equality UNPROVED",
              "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(), "commands": []}
    try:
        registry = json.loads((ROOT / "MODULES.json").read_text())
        modules = registry["base"] + registry["proof"] + registry["entry"] + registry["target_statements"]
        report["module_registry"] = registry
        before = source_snapshot(registry)
        report["source_sha256_lf_normalized"], report["input_source_sha256_raw"] = before
        report["source_manifest_sha256"] = sha256(ROOT / "SOURCE_BLOBS.json")
        report["roots_manifest_sha256"] = sha256(ROOT / "ROOTS.json")
        report["source_git_revision"] = subprocess.check_output(
            ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
        pins = json.loads((ROOT / "TOOLCHAIN_PINS.json").read_text())
        lean = Path(args.lean).resolve()
        lake = lean.parent / "lake"
        version = subprocess.check_output([str(lean), "--version"], text=True).strip()
        if f"version {pins['version']}," not in version or pins["commit"] not in version:
            raise RuntimeError(f"Unexpected Lean toolchain: {version}")
        report["lean_version"] = version
        report["toolchain_binary_sha256"] = {}
        for rel, wanted in pins["binaries"].items():
            observed = sha256(lean.parent.parent / rel)
            if observed != wanted: raise RuntimeError(f"Toolchain binary mismatch: {rel}")
            report["toolchain_binary_sha256"][rel] = observed
        mathlib = args.mathlib_dir.resolve()
        lock = json.loads((ROOT / "lake-manifest.json").read_text())
        dependencies, paths, directories = {}, [], {}
        for item in lock["packages"]:
            if item["name"] == "mathlib": directory = mathlib
            else:
                candidates = [mathlib.parent / item["name"], mathlib / ".lake/packages" / item["name"]]
                directory = next((p.resolve() for p in candidates if p.is_dir()), None)
                if directory is None: raise RuntimeError(f"Missing dependency {item['name']}")
            dependencies[item["name"]] = dependency_check(directory, item["rev"])
            directories[item["name"]] = directory
            paths.append(str(directory / ".lake/build/lib/lean"))
        report["dependencies"] = dependencies
        env = os.environ.copy()
        env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
        env.pop("LEAN_PATH", None); env.pop("LEAN_SRC_PATH", None)
        env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
        def run(command: list[str], cwd: Path, logfile: str, run_env: dict,
                expected_failure: bool = False) -> None:
            started = time.monotonic()
            with (output / logfile).open("w") as stream:
                stream.write("COMMAND " + json.dumps(command) + "\nCWD " + str(cwd) + "\n")
                stream.flush()
                proc = subprocess.run(command, cwd=cwd, env=run_env, stdout=stream,
                                      stderr=subprocess.STDOUT, timeout=3600)
            text = (output / logfile).read_text(errors="replace")
            entry = {"command": command, "cwd": str(cwd), "returncode": proc.returncode,
                     "elapsed_seconds": round(time.monotonic() - started, 3), "log": logfile,
                     "log_sha256": sha256(output / logfile)}
            report["commands"].append(entry)
            print(json.dumps(entry), flush=True)
            if expected_failure:
                if proc.returncode == 0 or "error" not in text.lower():
                    raise RuntimeError(f"False-claim control unexpectedly accepted: {logfile}")
                infrastructure = ["unknown module prefix", "object file", "already been declared",
                                  "no such file", "unknown identifier", "failed to load"]
                if any(word in text.lower() for word in infrastructure):
                    raise RuntimeError(f"Negative failed for an infrastructure reason: {logfile}")
                if not any(word in text.lower() for word in ["unsolved goals", "type mismatch", "tactic"]):
                    raise RuntimeError(f"No mathematical rejection diagnostic: {logfile}")
            elif proc.returncode != 0:
                print("\n".join(text.splitlines()[-60:]), flush=True)
                raise RuntimeError(f"Verification command failed: {logfile}")

        # A genuinely fresh Lake project: both reusable base and new owned modules
        # have no objects. Only the audited fixed external dependency caches are reused.
        lake_root = output / "fresh-lake/formalizations"
        project = lake_root / "gaussian-four-global-progress"
        base = lake_root / "gaussian-measure-primal-dual"
        project.mkdir(parents=True); base.mkdir()
        for module in modules:
            destination = (base if module in registry["base"] else project) / f"{module}.lean"
            destination.write_bytes(canonical(source_path(module, registry)))
        for name in ["lakefile.lean", "lake-manifest.json", "lean-toolchain"]:
            (project / name).write_bytes(canonical(ROOT / name))
        packages = project / ".lake/packages"
        packages.mkdir(parents=True)
        for name, directory in directories.items():
            (packages / name).symlink_to(directory, target_is_directory=True)
        report["lake_owned_objects_before"] = len(list(project.glob("*.olean"))) + len(list(base.glob("*.olean")))
        run([str(lake), "build"], project, "lake-build.log", env)
        lake_objects = project / ".lake/build/lib/lean"
        if any(not (lake_objects / f"{m}.olean").is_file() for m in modules):
            raise RuntimeError("Fresh Lake build did not produce every registered module")
        report["fresh_lake_build"] = {"status": "PASS", "modules": len(modules),
            "object_sha256": {m: sha256(lake_objects / f"{m}.olean") for m in modules}}

        # Independent source elaboration order, separate from all Lake-owned objects.
        work = output / "fresh-direct"
        work.mkdir()
        direct_env = env.copy()
        direct_env["LEAN_PATH"] = os.pathsep.join([str(work)] + paths)
        report["direct_owned_objects_before"] = len(list(work.glob("*.olean")))
        for module in modules:
            (work / f"{module}.lean").write_bytes(canonical(source_path(module, registry)))
            run([str(lean), "-o", f"{module}.olean", f"{module}.lean"], work,
                f"build-{module}.log", direct_env)
        report["direct_object_sha256"] = {m: sha256(work / f"{m}.olean") for m in modules}
        for name in ["Audit", "Replay"]:
            (work / f"{name}.lean").write_bytes(canonical(ROOT / "audit" / f"{name}.lean"))
            run([str(lean), f"{name}.lean"], work, f"{name.lower()}.log", direct_env)
        replay_log = (output / "replay.log").read_text()
        match = re.search(r"EMPTY_KERNEL_REPLAY_PASS (\d+) declarations; (\d+) roots; trust level zero", replay_log)
        if not match: raise RuntimeError("Empty-kernel completion marker is missing")
        wanted_roots = json.loads((ROOT / "ROOTS.json").read_text())["all_roots"]
        if int(match.group(2)) != len(wanted_roots):
            raise RuntimeError("Replay root count does not match the pinned root manifest")
        axioms = set((work / "replayed-axioms.txt").read_text().splitlines())
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError(f"Unexpected kernel axioms: {sorted(axioms)}")
        report["empty_kernel_replay"] = {"status": "PASS", "trust_level": 0,
            "declarations": int(match.group(1)), "roots": int(match.group(2)), "axioms": sorted(axioms)}
        for name in ["replayed-axioms.txt", "replayed-closure.txt"]:
            shutil.copyfile(work / name, output / name)
        shutil.copyfile(ROOT / "ROOTS.json", output / "verified-roots.json")
        (output / "source-sha256.json").write_text(json.dumps(before[0], indent=2, sort_keys=True) + "\n")

        controls = json.loads((ROOT / "audit/NEGATIVE_CONTROLS.json").read_text())
        report["negative_controls"] = []
        for control in controls:
            directory = output / "negative" / control["name"]
            directory.mkdir(parents=True)
            if "module" in control:
                filename = control["module"] + ".lean"
                text = source_path(control["module"], registry).read_text()
                if text.count(control["old"]) != 1:
                    raise RuntimeError(f"Ambiguous negative mutation: {control['name']}")
                text = text.replace(control["old"], control["new"])
            else:
                filename = control["file"]
                text = (ROOT / "audit" / filename).read_text()
            (directory / filename).write_text(text)
            run([str(lean), "-o", str(Path(filename).with_suffix(".olean")), filename], directory,
                f"negative-{control['name']}.log", direct_env, expected_failure=True)
            report["negative_controls"].append({**control, "status": "REJECTED",
                "mutated_source_sha256": sha256(directory / filename)})

        if before != source_snapshot(registry):
            raise RuntimeError("Owned/reused source files changed during verification")
        if report["source_manifest_sha256"] != sha256(ROOT / "SOURCE_BLOBS.json"):
            raise RuntimeError("Source manifest changed during verification")
        for item in lock["packages"]:
            dependency_check(directories[item["name"]], item["rev"])
        report["source_hashes_unchanged"] = True
        report["dependencies_rechecked_after_build"] = True
        report["dependency_cache_reused"] = True
        report["full_mathlib_rebuilt_from_source"] = False
        report["ci"] = {key: os.environ.get(key) for key in
                        ["GITHUB_ACTIONS", "GITHUB_RUN_ID", "GITHUB_SHA", "GITHUB_REF"]}
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
        print("VERIFICATION_STATUS " + report["status"], flush=True)
        print("VERIFICATION_REPORT " + str(output / "verification.json"), flush=True)


if __name__ == "__main__":
    raise SystemExit(main())