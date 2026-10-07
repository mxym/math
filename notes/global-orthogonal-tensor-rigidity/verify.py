"""Read-only package verification; optional Lean build uses ignored artifacts."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CACHE_DIRS = {".lake", ".elan", ".cache", "__pycache__"}
EXPECTED_EXPORTS = {
    "distinct_zero", "repeated_sum_zero", "derivative_kernel_is_rotation",
    "binary_norm_identity", "binary_commutator_identity",
    "angular_amplitude_identity", "optimal_binary_scalar_bound",
}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def run(args, cwd=ROOT):
    p = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, check=False)
    if p.returncode:
        sys.stderr.buffer.write(p.stdout)
        raise RuntimeError(f"command failed with status {p.returncode}: {args[0]}")
    return p.stdout


def payload_files():
    return {str(p.relative_to(ROOT)) for p in ROOT.rglob("*") if p.is_file()
            and not CACHE_DIRS.intersection(p.relative_to(ROOT).parts)
            and p.name not in {"MANIFEST.json", "SHA256SUMS"}}


def verify_integrity():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    require(payload_files() == set(manifest["sha256"]), "payload inventory mismatch")
    for name, expected in manifest["sha256"].items():
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected,
                f"file hash mismatch: {name}")
    sums = {}
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        require(name not in sums, "duplicate checksum entry")
        sums[name] = digest
    require(set(sums) == payload_files() | {"MANIFEST.json"}, "checksum inventory")
    for name, digest in sums.items():
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest,
                f"checksum mismatch: {name}")
    sources = json.loads((ROOT / "SOURCES.json").read_text())
    for entry in sources["copied_files"]:
        require(hashlib.sha256((ROOT / entry["local_path"]).read_bytes()).hexdigest()
                == entry["sha256"], "upstream byte preservation")
    print(f"Integrity: {len(manifest['sha256'])} payload files and upstream pins PASS")


def verify_python():
    for name in ("linearization", "truncation", "global_odeco", "all_orders"):
        file = ROOT / "checks" / f"check_{name}.py"
        ordinary = run([sys.executable, "-B", str(file)])
        optimized = run([sys.executable, "-B", "-O", str(file)])
        require(ordinary == optimized, f"optimized result mismatch: {name}")
        require(ordinary == (ROOT / "results" / f"{name}.txt").read_bytes(),
                f"recorded result mismatch: {name}")
        print(f"Exact {name}: ordinary/optimized reports match")
    source = ROOT / "sources" / "openai101" / "verify_scalar.py"
    report = run([sys.executable, "-B", str(source)])
    require(b"ALL CHECKS PASSED" in report, "upstream scalar outcome")
    print("Upstream scalar certificate PASS (analytic source theorem remains unaudited)")


def verify_lean():
    formal = ROOT / "formal"
    require((formal / ".lake" / "packages").is_dir(), "run formal/bootstrap.sh first")
    pins = json.loads((formal / "lake-manifest.json").read_text())
    for pin in pins["packages"]:
        require(pin["type"] == "git", "unsupported dependency source")
        folder = formal / pins["packagesDir"] / pin["name"]
        actual = run(["git", "rev-parse", "--verify", "HEAD^{commit}"], folder).strip()
        require(actual.decode() == pin["rev"], f"dependency revision: {pin['name']}")
    version = run(["lake", "env", "lean", "--version"], formal)
    require(b"4.34.1" in version and b"5045d0056413266e57c625dcd7c365b10e377c52" in version,
            "Lean compiler pin")
    run(["lake", "build", "GlobalAlgebra"], formal)
    report = run(["lake", "env", "lean", "JacobianKernel.lean"], formal)
    report += run(["lake", "env", "lean", "BinaryCubic.lean"], formal)
    matches = re.findall(
        rb"'QuantitativeJacobian\.([^']+)' depends on axioms: \[([^\]]*)\]", report)
    exports = {}
    for name, axioms in matches:
        require(name.decode() not in exports, "duplicate Lean export")
        exports[name.decode()] = {a.strip().decode() for a in axioms.split(b",") if a.strip()}
    require(set(exports) == EXPECTED_EXPORTS, "Lean export inventory")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    require(all(a <= allowed for a in exports.values()), "unexpected Lean logical axiom")
    for file in ("JacobianKernel.lean", "BinaryCubic.lean", "GlobalAlgebra.lean"):
        text = (formal / file).read_text()
        require(not re.search(r"\b(sorry|admit|native_decide)\b", text),
                "forbidden proof placeholder or native shortcut")
    print(f"Lean: {len(exports)} algebraic exports, compiler and 9 dependency pins PASS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true")
    args = parser.parse_args()
    verify_integrity()
    verify_python()
    if args.lean:
        verify_lean()
    print("Verification complete; partial formalization and conditional boundaries unchanged.")


if __name__ == "__main__":
    main()
