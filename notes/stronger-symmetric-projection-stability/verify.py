#!/usr/bin/env python3
"""Portable exact finite-regression runner; these checks are not analytic proofs."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
SUITES = (
    {
        "name": "matching",
        "file": "check_matching_improvement.py",
        "independent_cases": 2432,
        "scope": (
            "Exact rational finite regressions for omitted-basis cofactor "
            "identities, truncation perturbations, adjacent weighted edges, "
            "and the rational bounded-law obstruction; no integral proof."
        ),
        "expected": {
            "status": "PASS",
            "cofactor_formula_cases": 900,
            "truncation_bound_cases": 900,
            "adjacent_edge_bound_cases": 600,
            "obstruction_formula_cases": 32,
            "total_cases": 2432,
            "arithmetic": "exact rational",
        },
    },
    {
        "name": "halfmass",
        "file": "check_halfmass_sharpness.py",
        "independent_cases": 8,
        "scope": (
            "Eight exact rational cone-law parameter cases in dimensions "
            "three and four, checking determinant mass, signed defect, "
            "fourth cofactor, weighted half-mass tail, and support surplus."
        ),
    },
    {
        "name": "geometry",
        "file": "check_geometry_next.py",
        "independent_cases": 520,
        "scope": (
            "Exact rational weighted corner-cut identities and squared "
            "normal distances in dimensions three through twelve: "
            "480 corner-cut cases and 40 near-axis counterexample cases."
        ),
        "expected": {
            "status": "PASS",
            "weighted_corner_cut_cases": 480,
            "near_axis_counterexample_cases": 40,
            "total_cases": 520,
            "arithmetic": "exact rational; squared normal distances",
        },
    },
    {
        "name": "global",
        "file": "check_global_slanted.py",
        "independent_cases": 5032,
        "scope": (
            "Five thousand ordered four-direction tuples at eight rational "
            "parameters, each with sixteen sign averages, plus thirty-two "
            "product-dimension parameter cases in dimensions three through "
            "six. Also checks the displayed section and coordinate-block "
            "formulas; it does not prove unrestricted geometric distance."
        ),
        "expected": {
            "status": "PASS",
            "rational_parameters": 8,
            "ordered_four_type_tuples": 5000,
            "sign_averages_per_tuple": 16,
            "product_dimension_cases": 32,
            "section_and_block_formulas": "PASS",
        },
    },
)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def parse_result(suite, stdout):
    if suite["name"] == "halfmass":
        match = re.fullmatch(
            r"PASS ([0-9]+) exact cone-law cases: determinants, signs, tail, "
            r"support\n", stdout
        )
        require(match is not None, "halfmass: unexpected stdout")
        cases = int(match.group(1))
        require(cases == 8, "halfmass: expected eight parameter cases")
        return {
            "status": "PASS",
            "total_cases": cases,
            "dimensions": [3, 4],
            "rational_parameters_per_dimension": 4,
            "arithmetic": "exact rational; full signed determinant enumeration",
        }
    try:
        result = json.loads(stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"{suite['name']}: invalid JSON stdout") from error
    require(isinstance(result, dict), f"{suite['name']}: JSON is not an object")
    for key, expected in suite["expected"].items():
        require(result.get(key) == expected,
                f"{suite['name']}: unexpected {key}: {result.get(key)!r}")
    if suite["name"] == "matching":
        count = sum(result[key] for key in (
            "cofactor_formula_cases", "truncation_bound_cases",
            "adjacent_edge_bound_cases", "obstruction_formula_cases"
        ))
        require(count == result["total_cases"], "matching: inconsistent total")
    elif suite["name"] == "geometry":
        count = (result["weighted_corner_cut_cases"]
                 + result["near_axis_counterexample_cases"])
        require(count == result["total_cases"], "geometry: inconsistent total")
    elif suite["name"] == "global":
        count = (result["ordered_four_type_tuples"]
                 + result["product_dimension_cases"])
        require(count == suite["independent_cases"],
                "global: inconsistent independent-case total")
    return result


def run(args):
    inputs = [ROOT / suite["file"] for suite in SUITES] + [ROOT / "verify.py"]
    # Validate every required input before creating output directories or logs.
    for path in inputs:
        require(path.is_file(), f"missing input: {path.name}")
        require(not path.is_symlink(), f"symlink input is not supported: {path.name}")
    source_hashes = {path.name: sha256(path.read_bytes()) for path in inputs}
    output_dir = args.output_dir.resolve()
    require(output_dir != ROOT, "use a separate output directory")
    for path in inputs:
        require(output_dir != path, "output directory collides with an input")
    output_dir.mkdir(parents=True, exist_ok=True)
    log_suffix = ".optimized" if args.optimized else ""
    suites = []
    for suite in SUITES:
        command = [sys.executable]
        if args.optimized:
            command.append("-O")
        command.append(str(ROOT / suite["file"]))
        completed = subprocess.run(
            command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=args.timeout, check=False
        )
        (output_dir / f"{suite['name']}{log_suffix}.stdout.log").write_bytes(
            completed.stdout)
        (output_dir / f"{suite['name']}{log_suffix}.stderr.log").write_bytes(
            completed.stderr)
        require(completed.returncode == 0,
                f"{suite['name']}: exit code {completed.returncode}; see logs")
        require(not completed.stderr,
                f"{suite['name']}: unexpected stderr; see logs")
        try:
            stdout = completed.stdout.decode("utf-8")
        except UnicodeDecodeError as error:
            raise RuntimeError(f"{suite['name']}: stdout is not UTF-8") from error
        result = parse_result(suite, stdout)
        suites.append({
            "suite": suite["name"],
            "source": suite["file"],
            "status": "PASS",
            "independent_cases": suite["independent_cases"],
            "finite_scope": suite["scope"],
            "stdout_sha256": sha256(completed.stdout),
            "stderr_sha256": sha256(completed.stderr),
            "result": result,
        })
    for path in inputs:
        require(sha256(path.read_bytes()) == source_hashes[path.name],
                f"source changed during verification: {path.name}")
    total = sum(suite["independent_cases"] for suite in suites)
    require(total == 7992, f"unexpected aggregate independent-case count: {total}")
    report = {
        "schema_version": 1,
        "status": "PASS",
        "arithmetic": "exact rational; no floating-point certification",
        "independent_cases": total,
        "scope": (
            "Finite regression checks only. They verify the enumerated "
            "identities and bounds and are not analytic proofs, human peer "
            "review, or proof-assistant verification of the universal theorems."
        ),
        "three_dimensional_global_sign_averages": 80000,
        "source_sha256": source_hashes,
        "suites": suites,
    }
    data = (json.dumps(report, sort_keys=True, indent=2) + "\n").encode("utf-8")
    report_name = ("verification-optimized.json" if args.optimized
                   else "verification.json")
    (output_dir / report_name).write_bytes(data)
    print(f"PASS {total} independent finite cases across {len(suites)} suites")
    print(f"Report: {output_dir / report_name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--optimized", action="store_true",
        help="run every child regression with Python -O"
    )
    parser.add_argument(
        "--output-dir", type=Path, default=ROOT / "results",
        help="separate directory for deterministic JSON and subprocess logs"
    )
    parser.add_argument(
        "--timeout", type=int, default=300,
        help="maximum seconds for each regression subprocess (default: 300)"
    )
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    try:
        run(args)
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f"verification failed: {error}\n")


if __name__ == "__main__":
    main()
