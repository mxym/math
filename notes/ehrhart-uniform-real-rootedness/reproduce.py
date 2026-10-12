"""Reproduce the exact scalar/induction certificates; not a theorem prover."""
from pathlib import Path
from fractions import Fraction
import argparse, hashlib, json, os, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
PROGRAMS = {
    "verify_small_x_majorant.py": "small_x_majorant_certificate.json",
    "verify_majorant_tail_constants.py": "majorant_tail_certificates.jsonl",
    "verify_large_x_intervals.py": "large_x_interval_results.jsonl",
}

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def integrity():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    for item in manifest["files"]:
        p = ROOT / item["path"]
        require(p.is_file(), "Missing payload: " + item["path"])
        require(p.stat().st_size == item["bytes"], "Size mismatch: " + item["path"])
        require(digest(p) == item["sha256"], "Digest mismatch: " + item["path"])
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        expected, relative = line.split("  ", 1)
        require(digest(ROOT / relative) == expected, "Checksum mismatch: " + relative)
    return len(manifest["files"])

def run(args, cwd):
    env = dict(os.environ)
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return subprocess.run([sys.executable] + args, cwd=cwd, env=env,
                          capture_output=True, timeout=180)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--modes", nargs="+", choices=["normal", "O", "OO"],
                        default=["normal", "O", "OO"])
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    count = integrity()
    runs = []
    flags = {"normal": [], "O": ["-O"], "OO": ["-OO"]}
    for mode in args.modes:
        for program, witness in PROGRAMS.items():
            result = run(flags[mode] + [program], ROOT / "verification")
            require(result.returncode == 0, "Program failed: " + program)
            require(not result.stderr, "Unexpected stderr: " + program)
            expected = (ROOT / "certificates" / witness).read_bytes()
            require(result.stdout == expected, "Witness differs: " + witness)
            runs.append({"mode": mode, "program": program, "exit": 0,
                         "witness_sha256": hashlib.sha256(result.stdout).hexdigest()})
    supplemental = run(["independent_residual_checks.py"], ROOT / "verification")
    require(supplemental.returncode == 0 and not supplemental.stderr,
            "Independent residual check failed")
    require(supplemental.stdout ==
            (ROOT / "certificates/independent_residual_checks.json").read_bytes(),
            "Independent residual witness differs")
    intervals = [json.loads(x) for x in
                 (ROOT / "certificates/large_x_interval_results.jsonl").read_text().splitlines()]
    require(len(intervals) == 33, "Wrong interval count")
    require(Fraction(intervals[0]["a"]) == Fraction(1, 10) and
            Fraction(intervals[-1]["b"]) == 15, "Wrong covering endpoints")
    for i, row in enumerate(intervals):
        require(Fraction(row["a"]) < Fraction(row["b"]) and
                Fraction(row["total_upper"]) < 1, "Invalid closed interval certificate")
        if i:
            require(Fraction(intervals[i-1]["b"]) == Fraction(row["a"]), "Coverage gap")
    controls = []
    if args.negative_controls:
        for which in ("q_underestimate", "invalid_margin"):
            with tempfile.TemporaryDirectory(prefix="ehrhart-negative-") as tmp:
                tmp = Path(tmp)
                for p in (ROOT / "verification").glob("*.py"):
                    (tmp / p.name).write_bytes(p.read_bytes())
                if which == "q_underestimate":
                    program = "verify_small_x_majorant.py"
                    old, new = "q=F(53,200)", "q=F(1,10)"
                    expected_error = "critical q upper"
                else:
                    program = "verify_large_x_intervals.py"
                    old, new = "+F(1,1000))", "+F(2))"
                    expected_error = "uniform interval positivity envelope"
                source = (tmp / program).read_text()
                require(source.count(old) == 1, "Negative-control anchor changed")
                (tmp / program).write_text(source.replace(old, new))
                for mode in ("normal", "O", "OO"):
                    result = run(flags[mode] + [program], tmp)
                    require(result.returncode != 0 and
                            expected_error.encode() in result.stderr,
                            "Invalid scalar input was accepted")
                    controls.append({"mutation": which, "mode": mode,
                                     "rejected": True, "expected_error": expected_error})
    worst = max(intervals, key=lambda r: Fraction(r["total_upper"]))
    print(json.dumps({"status": "PASS", "scope": "exact scalar/base certificates and "
                      "reviewed analytic reductions; not Lean or original finite-data reconstruction",
                      "payload_files": count, "normal_runs": runs,
                      "additional_exact_residual_checks": 39,
                      "negative_controls": controls, "closed_intervals": 33,
                      "worst_interval": [worst["a"], worst["b"]],
                      "worst_total_upper": worst["total_upper"]}, indent=2))

if __name__ == "__main__":
    main()
