#!/usr/bin/env python3
"""Source-bound independent output rebuild and trust-zero replay of the actual pure iid symmetric support."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, signal, subprocess, time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def inventory():
    names = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "reproduce.py",
             "README.md", "ROOTS.txt", "Audit.lean", "Check.lean", "SymmetricSupport.lean",
             "SymmetricSupportVerification.lean", "SymmetricSupportVerification/ReplaySupport.lean"]
    selected = {ROOT / n for n in names}
    selected.update((ROOT / "SymmetricSupport").glob("*.lean"))
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(selected)}

def run_read(cmd):
    return subprocess.check_output(cmd, cwd=ROOT, text=True).strip()

def check():
    if inventory() != json.loads((ROOT / "SOURCE_HASHES.json").read_text()):
        raise RuntimeError("Source binding changed")
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.1":
        raise RuntimeError("Wrong Lean toolchain")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    if [p.get("rev") for p in manifest["packages"] if p["name"] == "mathlib"] != [PIN]:
        raise RuntimeError("Wrong Mathlib manifest pin")
    for p in manifest["packages"]:
        if p["type"] != "git":
            continue
        package = ROOT / ".lake/packages" / p["name"]
        if not package.exists():
            continue
        if run_read(["git", "-C", str(package), "rev-parse", "HEAD"]) != p["rev"]:
            raise RuntimeError("Wrong actual dependency pin: " + p["name"])
        if subprocess.run(["git", "-C", str(package), "diff", "--quiet"],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).returncode:
            raise RuntimeError("Tracked dependency edits: " + p["name"])
    for p in (ROOT / "SymmetricSupport").glob("*.lean"):
        code = re.sub(r"/\-.*?\-/|--[^\n]*", "", p.read_text(), flags=re.S)
        if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", code):
            raise RuntimeError("Forbidden mathematical proof token: " + str(p))
    roots = (ROOT / "ROOTS.txt").read_text().splitlines()
    if len(roots) != len(set(roots)) or len(roots) != 74:
        raise RuntimeError("Root metadata changed")
    print("SOURCE_BINDING_PASS", len(inventory()), flush=True)

def safe_remove_build(p):
    p = Path(p)
    if p.is_symlink() or not p.resolve().is_relative_to(REPO.resolve()) or p.name != "build":
        raise RuntimeError("Unsafe output removal: " + str(p))
    if p.exists():
        shutil.rmtree(p)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--write-manifest", action="store_true")
    ap.add_argument("--check-only", action="store_true")
    ap.add_argument("--fresh", action="store_true")
    args = ap.parse_args()
    if args.write_manifest:
        (ROOT / "SOURCE_HASHES.json").write_text(json.dumps(inventory(), indent=2) + "\n")
        print("MANIFEST_WRITTEN_NOT_VERIFICATION")
        return
    check()
    if args.check_only:
        return
    if args.fresh:
        safe_remove_build(ROOT / ".lake/build")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out = ROOT / "verification" / ("reproduction-" + stamp)
    out.mkdir(parents=True, exist_ok=False)
    records = []
    def stage(name, cmd, limit):
        log = out / (name + ".log")
        start = time.monotonic()
        with log.open("w") as f:
            p = subprocess.Popen(cmd, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT,
                                 start_new_session=True)
            try:
                code = p.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                code = 124
        record = {"stage": name, "command": cmd, "exit_code": code,
                  "seconds": round(time.monotonic() - start, 3),
                  "log": log.name, "sha256": sha(log)}
        records.append(record)
        (out / "STAGES.json").write_text(json.dumps(records, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if code:
            print(log.read_text()[-10000:])
            raise RuntimeError("Failed stage " + name)
        return log.read_text()
    stage("toolchain", ["lake", "env", "lean", "--version"], 60)
    stage("build", ["lake", "build", "SymmetricSupport", "SymmetricSupportVerification"], 600)
    stage("types-and-axioms", ["lake", "env", "lean", "-j1", "-M6000", "Check.lean"], 120)
    audit = stage("kernel", ["lake", "env", "lean", "-j1", "-M6000", "Audit.lean"], 600)
    if audit.count("EMPTY_KERNEL_REPLAY_PASS") != 1 or audit.count("CORRUPTED_PROOF_REJECTED") != 11:
        raise RuntimeError("Incomplete audit markers")
    axioms = set((ROOT / "verification/symmetric-kernel-axioms.txt").read_text().splitlines())
    if not axioms <= ALLOWED_AXIOMS:
        raise RuntimeError("Unexpected kernel axioms")
    for p in (ROOT / "verification").glob("symmetric-*.txt"):
        shutil.copy2(p, out / p.name)
    snapshot = out / "source_snapshot"
    snapshot.mkdir()
    for rel in inventory():
        destination = snapshot / rel
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / rel, destination)
    shutil.copy2(ROOT / "SOURCE_HASHES.json", snapshot / "SOURCE_HASHES.json")
    check()
    count = int(re.search(r"EMPTY_KERNEL_REPLAY_PASS (\d+) declarations", audit).group(1))
    result = {
        "status": "PASS",
        "scope": "Actual symmetric projector in D^k coordinates, exact choose rank, normalized pure iid span, density support, exact effect identity, finite-phase plus Gamma Wick frame with integrability, and worst-pure-promise guarantee bounded by the actual normalized symmetric state. NOT literal Haar equality or general rank-s Schur theory.",
        "fresh_own_output_build": args.fresh,
        "source_files": len(inventory()),
        "roots": 74,
        "kernel_declarations": count,
        "kernel_trust": 0,
        "axioms": sorted(axioms),
        "same_type_forged_proof_controls": 11,
        "source_manifest_sha256": sha(ROOT / "SOURCE_HASHES.json"),
        "stages": records
    }
    (out / "SUMMARY.json").write_text(json.dumps(result, indent=2) + "\n")
    (ROOT / "verification/LATEST.json").write_text(json.dumps({
        "directory": out.name, "summary_sha256": sha(out / "SUMMARY.json")}, indent=2) + "\n")
    print("SYMMETRIC_SUPPORT_REPRODUCTION_PASS", str(out), flush=True)

if __name__ == "__main__":
    main()
