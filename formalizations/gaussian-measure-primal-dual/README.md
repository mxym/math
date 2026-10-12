# Actual Gaussian price and primal-dual formalization

This package proves a complete optimization stage using Mathlib's actual
`stdGaussian (EuclideanSpace ℝ (Fin d))`, actual probabilities, and actual Bochner
first moments. It supports the repository's Gaussian first-moment research.
It does **not** formalize the complete sharp geometric Gaussian theorem,
its facet/profile Hessian, or the Milman–Neeman geometric comparison theorem.
No new mathematical priority claim is made for these standard optimization facts.

The nine proof sources were rebuilt from frozen bytes and passed independent
empty-kernel replay: **50 roots; 52,742 dependency declarations; trust level zero**.
The checked closure has only `propext`, `Classical.choice`, and `Quot.sound` as
axioms. There is no `sorry`, custom axiom, Gaussian-property assumption package,
assumed price-existence theorem, or assumed optimization duality theorem.
The replay executable uses a meta-level collector to enumerate dependencies;
its collector is outside the mathematical proof closure.

## Precise statements

Write γ for the actual standard Gaussian on ℝᵈ. A fractional partition has
measurable labels fᵢ with 0 ≤ fᵢ ≤ 1 and Σᵢfᵢ = 1 almost everywhere. Its mass and
moment are pᵢ = ∫fᵢ dγ and mᵢ = ∫fᵢ(x)x dγ. The package proves their integrability,
Σpᵢ = 1, and Σmᵢ = 0. For any finite score vectors vᵢ and prices bᵢ it proves

    Σᵢ ⟨vᵢ,mᵢ⟩ ≤ ∫ maxᵢ(⟨vᵢ,x⟩ − bᵢ) dγ + Σᵢ pᵢbᵢ.

For k ≥ 1, distinct score vectors vᵢ, and pᵢ > 0 summing to one, it proves:

- Prices exist whose strictly winning cells have the prescribed actual masses.
- Any two balancing price vectors differ by a common additive constant.
- The winning cells form a measurable fractional partition attaining the minimum
  price objective and maximizing the actual Bochner moment objective over all
  fractional partitions of those masses.
- Equality in the price dual forces the fractional labels to be the winning-cell
  indicators almost everywhere.

The price-objective minimizer theorem itself does not require distinct vectors.
The zero-mass and coincident-score extensions of the optimization endpoint are
outside this package. Dimensions d = 0 and k = 1 are included whenever the stated
hypotheses are satisfiable.

The main endpoint is `GaussianMeasureBridge.actual_gaussian_primal_dual` in
[GaussianPrimalDual.lean](GaussianPrimalDual.lean). Fractional equality is
`GaussianMeasureBridge.fractional_dual_equality_ae_winning` in
[GaussianFractionalEquality.lean](GaussianFractionalEquality.lean).

## Proof structure

1. Bounded scalar labels multiplied by the integrable Gaussian coordinate give
   integrable Bochner moments. Finite sums commute with integration; the actual
   Gaussian mean is zero. Nonnegative fractional weighted averages give the dual.
2. The expected finite maximum is 1-Lipschitz in the price sup norm. Common price
   shifts leave the objective invariant. Subtracting the smallest price makes
   all prices nonnegative, with one zero. The positive prescribed masses then
   bound every price on an objective sublevel. A compact cube gives a global
   minimizer; the proof explicitly covers competitors outside that cube.
3. A nonzero Gaussian linear functional has a non-atomic real Gaussian law.
   Thus score ties have zero probability. The maximum's coordinate price
   derivative is minus the winning-label indicator. Its Lipschitz bound permits
   dominated differentiation of the actual integral. Fermat's theorem at the
   minimizer gives the exact prescribed cell masses.
4. The winning indicators attain the dual. Conversely a balancing price vector
   is a global minimizer. For two minimizers, the continuous nonnegative midpoint
   Jensen gap has integral zero. Actual Gaussian full support makes it vanish
   everywhere. The two maxima therefore share a maximizer at every point.
   Their continuous difference takes only finitely many price differences;
   connectedness makes it constant. Positive cell masses force every label's
   price difference to equal that constant.
5. The fractional dual gap is a nonnegative integrable function with integral
   zero. Almost everywhere it is zero, and the unique winning score strictly
   exceeds every other score. Every nonwinning label is consequently zero;
   the partition constraint makes the winning label one.

## Reproduction

Requires Python 3, Lean **4.34.1**, and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`; every dependency Git pin is recorded in
`DEPENDENCY_PINS.json`. No compiled `.olean` artifacts are distributed.

Prepare the usual pinned Lake dependencies in this directory:

```
lake update
lake exe cache get
python3 -O integrity.py
python3 reproduce.py
```

To reuse an already prepared pinned dependency project without modifying it:

```
python3 reproduce.py --dependency-project /path/to/pinned/project --lean /path/to/lean
```

The reproduction script explicitly verifies all bytes, dependency commits, the
Lean version, and Lean Git commit `5045d0056413266e57c625dcd7c365b10e377c52`.
It records the actual toolchain Lean binary's SHA256. It creates a fresh
directory, compiles all nine sources there,
audits the allowed axioms and unsafe/partial dependencies, then replays the
entire closure in an empty kernel and compares the root types. It also checks
the exact closure and axiom lists against the recorded evidence. `--work-dir`
can select a nonexistent directory for preserving the run. Shared dependencies
are read only. Integrity checks use explicit failures and remain active under
`python -O`.

`--preflight-only` exercises the same file, dependency, and actual-toolchain
checks without compiling sources or replaying any proof. Its output explicitly
distinguishes this limited check from `REPRODUCTION_PASS`.

`evidence/VERIFICATION.json` records the completed fresh run and all source and
artifact hashes. The `.olean` hashes identify that local run; they are not a
requirement that compiled byte layouts agree on another machine. The source
hashes and successful proof-closure replay are the relevant checks. The
verified replay checker adds only post-success textual closure exports to the
original checker; both checker hashes and that exact change are recorded.

`evidence/PUBLIC_REPRODUCTION.json` records a second fresh compilation and
successful 50-root replay performed by the public runner. The runner was
updated after that process started to strengthen its toolchain and record
checks; its launch-time script hash was not captured. The final runner's
preflight was executed separately, with its exact script hash, Git commit,
and binary hash recorded in `evidence/FINAL_PREFLIGHT.json`. The proof sources
and replay checker were identical in both runs. This evidence does not claim
a byte-identical end-to-end execution of the final runner revision.

The separate [semantic source review](../reviews/gaussian-measure-primal-dual-2026-10-08.md)
checks the exact nine proof sources and their scope. It is not an additional
kernel replay or a proof of the remaining sharp geometric endpoint.
