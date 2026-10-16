#!/usr/bin/env python3
"""Source-bound rebuild and separate trust-zero replay of the iid spectrum scope."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, signal, subprocess, time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
CORE = ROOT.parent / "spectral-extraction-core"
PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ROOT_COUNT = 180
CONTROL_COUNT = 23

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def inventory():
    names = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "reproduce.py",
             "README.md", "ROOTS.txt", "Audit.lean", "Check.lean", "Spectrum.lean",
             "SpectrumVerification.lean", "SpectrumVerification/ReplaySupport.lean", ".gitignore"]
    selected = {ROOT / n for n in names}
    selected.update((ROOT / "Spectrum").glob("*.lean"))
    selected.add(CORE / "SOURCE_HASHES.json")
    selected.update(REPO / n for n in json.loads((CORE / "SOURCE_HASHES.json").read_text()))
    return {p.relative_to(REPO).as_posix(): sha(p) for p in sorted(selected)}

def without_comments(txt):
    out, depth, i = [], 0, 0
    while i < len(txt):
        if txt[i:i+2] == "/-": depth += 1; i += 2
        elif depth and txt[i:i+2] == "-/": depth -= 1; i += 2
        elif depth:
            if txt[i] == "\n": out.append("\n")
            i += 1
        elif txt[i:i+2] == "--":
            end = txt.find("\n", i)
            i = len(txt) if end < 0 else end
        else: out.append(txt[i]); i += 1
    if depth: raise RuntimeError("Unclosed Lean block comment")
    return "".join(out)

def check():
    if inventory() != json.loads((ROOT / "SOURCE_HASHES.json").read_text()):
        raise RuntimeError("Source binding changed")
    baseline = json.loads((CORE / "SOURCE_HASHES.json").read_text())
    for name, digest in baseline.items():
        if sha(REPO / name) != digest: raise RuntimeError("Frozen core input changed: " + name)
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.1":
        raise RuntimeError("Wrong toolchain")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    if [p.get("rev") for p in manifest["packages"] if p["name"] == "mathlib"] != [PIN]:
        raise RuntimeError("Wrong Mathlib pin")
    for dep in manifest["packages"]:
        if dep["type"] != "git": continue
        source = ROOT / ".lake/packages" / dep["name"]
        if not source.exists(): continue
        actual = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
        if actual != dep["rev"]: raise RuntimeError("Wrong actual dependency pin: " + dep["name"])
        if subprocess.run(["git", "-C", str(source), "diff", "--quiet"], capture_output=True).returncode:
            raise RuntimeError("Tracked dependency modifications: " + dep["name"])
    declared = []
    for p in sorted((ROOT / "Spectrum").glob("*.lean")):
        code = without_comments(p.read_text())
        if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", code):
            raise RuntimeError("Forbidden mathematical proof token in " + p.name)
        declared += ["ExtractionSpectrum." + n for n in re.findall(r"^theorem\s+([\w\u2080-\u209f]+)", code, re.M)]
    roots = (ROOT / "ROOTS.txt").read_text().splitlines()
    if len(roots) != ROOT_COUNT or len(set(roots)) != ROOT_COUNT or set(declared) != set(roots):
        raise RuntimeError("Root declaration inventory mismatch")
    print("SOURCE_BINDING_PASS", len(inventory()), "ROOTS", ROOT_COUNT, flush=True)

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
    if args.check_only: return
    if args.fresh:
        output = ROOT / ".lake/build"
        if output.is_symlink() or not output.resolve().is_relative_to(ROOT.resolve()) or output.name != "build":
            raise RuntimeError("Unsafe owned output path")
        if output.exists(): shutil.rmtree(output)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out = ROOT / "verification" / ("reproduction-" + stamp)
    out.mkdir(parents=True, exist_ok=False)
    records = []
    def stage(name, cmd, limit):
        log = out / (name + ".log")
        start = time.monotonic()
        with log.open("w") as f:
            process = subprocess.Popen(cmd, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
            try: code = process.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL); process.wait(); code = 124
        rec = dict(stage=name, command=cmd, exit_code=code,
                   seconds=round(time.monotonic()-start, 3), log=log.name, sha256=sha(log))
        records.append(rec)
        (out / "STAGES.json").write_text(json.dumps(records, indent=2) + "\n")
        print(json.dumps(rec), flush=True)
        if code:
            print(log.read_text()[-12000:])
            raise RuntimeError("Failed stage " + name)
        return log.read_text()
    stage("toolchain", ["lake", "env", "lean", "--version"], 90)
    stage("build", ["lake", "build", "Spectrum", "SpectrumVerification"], 900)
    stage("types-and-axioms", ["lake", "env", "lean", "-j1", "-M9000", "Check.lean"], 180)
    audit = stage("kernel", ["lake", "env", "lean", "-j1", "-M9000", "Audit.lean"], 900)
    if audit.count("EMPTY_KERNEL_REPLAY_PASS") != 1 or audit.count("CORRUPTED_PROOF_REJECTED") != CONTROL_COUNT:
        raise RuntimeError("Incomplete audit markers")
    axioms = set((ROOT / "verification/spectrum-kernel-axioms.txt").read_text().splitlines())
    if not axioms <= ALLOWED_AXIOMS: raise RuntimeError("Unexpected kernel axioms")
    for p in (ROOT / "verification").glob("spectrum-*.txt"): shutil.copy2(p, out / p.name)
    check()
    closure = int(re.search(r"EMPTY_KERNEL_REPLAY_PASS (\d+) declarations", audit).group(1))
    result = dict(status="PASS", scope="Actual density and canonical iid tensor spectrum converses; internally constructed finite iid LLN/CLT and moving CDF; physical rate strong converse and Gaussian limsup upper. Attained escort scalar identities on actual positive eigensupport; finite Holder and optimized variational exponential converse for physical channel sequences; exact finite type counting and universal empirical-entropy LLN/Gaussian mass lower bounds. Exact finite and moving-threshold strict-direct empirical compression-error upper bounds, with attained positive variational rate and actual-density rank bridge. Constructed optimized escort typical subsets with exact positive-support value, full escort mass, original iid mass lower bounds and integer cardinality bounds; arbitrary-subset-to-prefix mass comparison. Not physical universal achievability, composed matching operational exponent lower bounds, local-cap high-rate exponent composition, reliability converses or Berry--Esseen.",
                  fresh_owned_output_build=args.fresh, source_files=len(inventory()), roots=ROOT_COUNT,
                  kernel_declarations=closure, kernel_trust=0, axioms=sorted(axioms),
                  same_type_forged_proof_controls=CONTROL_COUNT,
                  source_manifest_sha256=sha(ROOT / "SOURCE_HASHES.json"), stages=records)
    (out / "SUMMARY.json").write_text(json.dumps(result, indent=2) + "\n")
    (ROOT / "verification/LATEST.json").write_text(json.dumps(dict(directory=out.name,
      summary_sha256=sha(out / "SUMMARY.json")), indent=2) + "\n")
    print("EXTRACTION_SPECTRUM_REPRODUCTION_PASS", str(out), flush=True)

if __name__ == "__main__": main()
