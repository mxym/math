#!/usr/bin/env python3
"""Independent audit of entry005; does not import the published verifier.

Uses a dimension-coin outer loop, rather than the manuscript's first-part DP.
Each unordered dimension multiset is represented exactly once. All decisions
use Fraction. The saved certificate is checked as input, not regenerated only.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import hashlib
import argparse
import json

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo-root', type=Path, default=HERE.parents[1])
parser.add_argument('--output', type=Path, default=HERE/'results/simplex.json')
args = parser.parse_args()
PUB = args.repo_root / "preprints/005-simplex-product-optimum/v1.1"
EXPECTED = {
    "build/main.tex":"f709b04734073d0cf2d63eb958da68370d38a21a419301630b404279dc9428f0",
    "verification/verify_exact.py":"cb224bbc33bbca0f09df6693030febebf1d4b1c0ce54d7a46631ef596cb41c18",
    "verification/exact_certificate.json":"ca96820a672d2c514962dc774387e5b0a86127607477f81871d87ef98273d104",
}
for relative, expected in EXPECTED.items():
    if hashlib.sha256((PUB/relative).read_bytes()).hexdigest() != expected:
        raise ValueError("Input differs from audited snapshot: "+relative)

N = 300

def require(ok, message):
    if not ok:
        raise ArithmeticError(message)

def primitive_c(d):
    # Derived from n+1 unit zonotope determinants and simplex volume 1/n!.
    return Q(d + 1, factorial(d - 1)**d) / Q(1, factorial(d))**(d - 1)

cs = [Q(1)] + [primitive_c(d) for d in range(1, N + 1)]
for d in range(1, N + 1):
    require(cs[d] == Q((d+1)*d**d, factorial(d)), f"geometric constant {d}")

def balanced(n, k):
    q, r = divmod(n, k)
    return cs[q]**(k-r) * cs[q+1]**r if r else cs[q]**k

# At stage d, states optimize partitions using only parts at most d.
# Ascending total permits repetition of the current part. Counts are counts
# of unordered optimizing partitions, as opposed to ordered decompositions.
best = [None] * (N + 1)
counts = [0] * (N + 1)
parts = [None] * (N + 1)
best[0], counts[0], parts[0] = Q(1), 1, ()
for d in range(1, N + 1):
    for n in range(d, N + 1):
        if best[n-d] is None:
            continue
        candidate = cs[d] * best[n-d]
        if best[n] is None or candidate > best[n]:
            best[n], counts[n], parts[n] = candidate, counts[n-d], parts[n-d] + (d,)
        elif candidate == best[n]:
            counts[n] += counts[n-d]

for n in range(1, N + 1):
    require(counts[n] == 1, f"unordered uniqueness at {n}")
    ks = {max(1, n//13), max(1, (n+12)//13)}
    require(best[n] == max(balanced(n,k) for k in ks), f"formula at {n}")

cert = json.loads((PUB / "verification/exact_certificate.json").read_text())
expected_ratios = {
    "root_13_beats_12": cs[13]**12 / cs[12]**13,
    "root_13_beats_14": cs[13]**14 / cs[14]**13,
    "strict_concavity_at_13": cs[13]**2 / cs[12] / cs[14],
    "residue_8_prefers_14": cs[14]**8 / cs[12]**5 / cs[13]**4,
    "residue_9_prefers_12": cs[12]**4 * cs[13]**6 / cs[14]**9,
    "runner_up_14_beats_12": cs[14]**6 / cs[12]**7,
    "stability_constant_112": cs[13]**16 * cs[12]**13 / cs[14]**26,
}

def check_record(rec, expected, positive=True):
    num, den = int(rec["numerator"]), int(rec["denominator"])
    require(den > 0 and Q(num, den) == expected, "certificate ratio equality")
    if positive:
        require(num > den, "strict certificate sign")
        require(int(rec["positive_integer_margin"]) == num-den, "integer margin")

require(set(cert["strict_certificates"]) == set(expected_ratios), "exact seven certificates")
for name, ratio in expected_ratios.items():
    check_record(cert["strict_certificates"][name], ratio)
expected_no_ties = {str(n) for n in range(14,100) if n % 13}
require(set(cert["finite_no_tie_certificates"]) == expected_no_ties, "complete no-tie domain")
for ns, rec in cert["finite_no_tie_certificates"].items():
    n, win, lose = int(ns), rec["winning_count"], rec["losing_count"]
    require({win,lose} == {n//13,(n+12)//13}, "candidate counts")
    check_record(rec, balanced(n,win)/balanced(n,lose))
    require(len(parts[n]) == win, "independent winner count")

for ns, example in cert["examples"].items():
    n = int(ns)
    require(tuple(example["parts"]) == parts[n], "independent example parts")
    check_record(example["value"], best[n], positive=False)
require(best[99] == cs[12]**5 * cs[13]**3, "threshold obstruction optimizer")
require(best[112] > cs[13]*best[99], "threshold obstruction strict sign")
require(parts[112] == (14,)*8, "sharp additive constant")
require(all(best[n] == cs[n] for n in range(1,20)), "small dimensions")
require(best[20] > cs[20] and parts[20] == (10,10), "first excess")

# Exact endpoint checks, independent of decimal exponentiation.
rho = cert["rho_interval"]
lo = Q(int(rho["lower"]["numerator"]), int(rho["lower"]["denominator"]))
hi = Q(int(rho["upper"]["numerator"]), int(rho["upper"]["denominator"]))
require(lo**13 < cs[13] < hi**13, "rho isolation")

feasibility = []
for r in range(1,13):
    minimum_m = r if r<=8 else 12-r
    last_bad_n = 13*(minimum_m-1)+r if minimum_m else None
    feasibility.append({"residue":r,"preferred_factor_count":"m" if r<=8 else "m+1",
                        "minimum_m":minimum_m,"last_infeasible_dimension":last_bad_n})
require(max(x["last_infeasible_dimension"] or 0 for x in feasibility) == 99,
        "analytic feasibility cutoff")

failures = [n for n in range(1,N-12) if best[n+13] != cs[13]*best[n]]
require(failures == cert["recurrence_failures_in_checked_range"], "full failure list")

def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

result = {
    "status":"PASS",
    "method":"ascending-dimension coin dynamic program; exact unordered optimum counts",
    "dimensions":[1,N],
    "every_optimal_unordered_multiset_unique":all(x==1 for x in counts),
    "published_json_records_independently_validated":True,
    "strict_rational_certificates":len(expected_ratios),
    "finite_no_tie_certificates":len(expected_no_ties),
    "recurrence_last_failure_in_finite_check":max(failures),
    "residue_feasibility":feasibility,
    "source_sha256":sha256(PUB/"build/main.tex"),
    "published_verifier_sha256":sha256(PUB/"verification/verify_exact.py"),
    "published_certificate_sha256":sha256(PUB/"verification/exact_certificate.json"),
    "limitations":"Finite arithmetic verification only; infinite analytic and geometric arguments audited separately."
}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
