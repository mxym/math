# Gaussian mass envelope — analytic core (in progress)

This is a standalone, pinned Lean project for the self-contained analytic part of
`research/gaussian-centroid-mass-envelope/paper.md`. It is **not a complete Lean
formalization of the paper's two-sided mass-envelope theorem**.

## Exact mathematical scope

Write `q(a)` for the actual standard-Gaussian upper-tail probability,
`phi(a)` for its actual density, and `a_p` for the unique threshold with `q(a_p)=p`.
The checked entry points in this stage are:

* `GaussianMeasureBridge.squared_hazard_log_lipschitz`: for every `0 < p ≤ q < 1`,
  `0 ≤ (phi(a_p)/p)^2 - (phi(a_q)/q)^2 ≤ 2 log(q/p)`.
* `GaussianMeasureBridge.prescribed_mass_measurable_sets_bound`: for every finite
  family of actual measurable Gaussian sets with prescribed masses in `(0,1)`,
  the sum of squared norms of their actual Bochner first moments is at most
  `sum_i phi(a_{p_i})^2`. No convexity, smoothness, finite grid, or halfspace
  hypothesis is imposed on the input sets. The result in particular applies to
  every measurable partition.
* `GaussianMeasureBridge.gaussian_profile_entropy_bound`:
  `phi(a_p)^2 ≤ 2 p^2 log(1/p)` for every `0 < p < 1`.

The quantiles, tail derivatives, first/second truncated moments, and nonnegative
conditional variance needed here are proved, not assumed. `GaussianSets.lean`
constructs the exact indicator/complement partition and proves its mass and
Bochner-moment identities; the original set problem is not replaced by an
unproved fractional-model interface.

## Verification status of this development revision

The exact source at commit `46f8894ac0c2e36544a8db91c8434a560f1bd868` passed
[CI run 38025117038](https://github.com/mxym/math/actions/runs/38025117038).
All **9 project modules** were rebuilt in a new empty build directory; all
**47 named roots** and their **53,046-declaration transitive closure** passed
empty-kernel replay at trust level zero. Only `propext`, `Classical.choice`, and
`Quot.sound` occurred. Both deliberately corrupted analytic statements were
rejected. Source and pinned-dependency hashes were checked before/after the run.
This is a fresh run, completed at `2026-10-10T04:48:17Z`, not a historical log
relabeled as a new verification. The detailed [evidence](evidence/ci-38025117038/README.md)
is committed beside the sources.

## Reproduce

Lean is fixed to `4.34.1`, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`. Mathlib is fixed to
`d13f23b723b8a846827a245b89c10fc7d3f11612`; all transitive revisions are recorded in
`lake-manifest.json` and checked against the dependency checkouts.

```sh
cd formalizations/gaussian-mass-envelope-progress
bash fetch_cache.sh
lake build
python3 reproduce.py --output-dir /tmp/gaussian-mass-envelope-fresh-check
```

The output directory must not exist. The verifier validates source Git-blob
hashes, checks all pinned dependency Lean/configuration sources against their Git
trees (explicitly normalizing CRLF), rebuilds all nine project modules without
exposing old project objects on `LEAN_PATH`, prints the axioms of all named roots,
and replays their transitive proof closure into an empty Lean kernel at trust
level zero. It then rejects two deliberately mutated analytic statements and
checks that source SHA-256 hashes did not change during the run. The generated
`verification.json`, logs, closure list and source/object hashes give the actual
scope and results. There are no proof placeholders, custom axioms, or
`native_decide` proofs. The permitted foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

The replay is independent of the original elaboration and imported theorem
acceptance, but uses the same Lean kernel implementation; it is not an
independently implemented kernel or external peer review.

## Remaining gap to the full paper

The ordered residual-entropy inequality, the arbitrary-mass staircase partition
with exact Gaussian masses and moments, and the complete lower-bound/supremum
assembly are not proved in this package. The two-log-scale refinements are also
outside its present scope. See `THEOREM_MAP.md` and `PROOF.md`.

## Attribution

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding; AI-assisted research and
formalization. This work makes no claim of priority for a new mathematical
solution and is not a substitute for external peer review. Original materials
retain all rights unless separately licensed. See `THIRD_PARTY.md` for unchanged
inherited sources and the existing third-party licenses.
