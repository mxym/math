# High-dimensional APPT: mathematical review and Lean verification

**The full research program remains partially formalized. The fixed-local purity supremum limit and its first excess-purity coefficient are now complete, and the purity upper half is verified uniformly over all dimension pairs as total dimension grows. The two-level projection plateau is also optimized exactly within the plateau family in the even-rank case. Matching growing-local-dimension lower limits, exact finite maxima/classification beyond that family, full entropy and rigidity claims remain unclosed.**

Every physical endpoint uses actual complex density matrices and the original all-global-unitary APPT definition. No spectral ansatz, unproved quantum characterization, graph cap or claimed main conclusion is assumed in the final physical theorems.

## Purity-ball sufficiency and the singular APPT locus

For D=mn>1, `density_appt_of_purity_ball` proves that every actual density matrix with purity at most 1/(D-1) is APPT under every global unitary. The proof establishes partial-transpose invariance of the Hermitian Hilbert--Schmidt square and derives positivity from the actual matrix eigenvalues. No Schmidt or Hildebrand criterion is assumed.

For 2<=m<=n, `singular_density_appt_iff_spectrum` proves a necessary-and-sufficient statement for a density matrix with determinant zero: it is APPT exactly when its sorted eigenvalues are one zero and D-1 copies of 1/(D-1). Equivalently its purity is 1/(D-1). `exists_singular_appt_density` constructs an actual normalized complementary coordinate projection and proves its density, APPT, determinant-zero and exact-purity properties. The purity-ball condition is only sufficient without singularity; a physical 2x3 counterexample to necessity is included.

Recovered unpublished WSL work was independently read and subjected to a fresh source-bound build/replay before publication. Independent GitHub run **38189500302**, source **4e647075a83f317c16dcecac50b0dc6d91e86d35**, then passed all stages: **2,852 Lake tasks, 42,271 declarations, 139 explicit roots**, trust level zero, and only propext, Classical.choice and Quot.sound. All **65 pinned inputs** and uploaded sources matched. The final singular equivalence, purity-ball theorem and singular-attainment theorem reject forged proofs with unchanged types. Literal evidence and corruption dependencies are in `verification/ci-4e647075/`.

These standard finite-dimensional facts close previously missing sufficiency and classification dependencies. They are not new priority claims, the three-level 10x38 joint sufficiency, an exact unrestricted purity maximum, or the dimension-varying multiscale lower limit. See `REVIEW_SINGULAR_CONTINUATION.md`. No preprint or immutable Release is changed.

## Finite-dimensional attainment checkpoint

The physical APPT set is now proved compact. `exists_appt_purity_isGreatest` and `exists_appt_purity_eq_sup` prove that the original supremum is attained by a genuine complex density matrix for every 2<=m<=n. `apptPurityValues_eq_Icc` gives the exact attainable interval [1/(mn), P_sup(m,n)], without evaluating its upper endpoint. The maximally mixed density uniquely minimizes purity. `appt_maximizing_mixture_rigid` proves that a strict mixture attaining maximal purity has identical endpoints; this is not a maximizing-spectrum classification. The subsequence result concerns fixed dimensions, not the unproved dimension-varying graph limit.

Independent run **38162415802**, source **0d7760e7d33eb38cc72778e4d7ac872216b9d11a**, passed: 2,849 Lake tasks, 42,246 transitive declarations, 122 explicit roots, trust level zero. The only axioms are propext, Classical.choice and Quot.sound. The interval, actual IsGreatest, and mixture-rigidity theorem statements rejected deliberately forged proofs. All 62 pinned inputs and uploaded sources matched the tested commit; literal evidence is in `verification/ci-0d7760e7/`. Existing historical checkpoints retain their original scopes and hashes.

Five modules add this chain: StateTopology, CompactMaximum, PurityMixing, PurityInterval and CompactControls. No numerical unrestricted maximum, multiscale lower limit, full entropy theorem or dimensional rigidity is inferred. These are standard compactness and convex-quadratic arguments formally connected to the actual quantum definitions, not a claim of new mathematical priority. No preprint or Release is changed.

## 1. Fixed-local purity: both bounds and a genuine limit

Let D=mn, C_m=m^2/(m^2-1), and let P_sup(m,n) be the supremum of trace(A*A).re over actual APPT density matrices on C^m tensor C^n. `apptPurityValues` defines this physical objective set, and `appt_purity_values_nonempty_bounded` proves it nonempty and bounded for 2<=m<=n. Positive scaling of its supremum is also proved; totalized empty/unbounded-supremum conventions do not supply the result.

For m>=2 and n>=2m the finite bounds are

    C_m - 1/n^2 <= (mn)*P_sup(m,n) <= C_m + 13m/n.

The upper inequality holds for every physical state. The lower inequality is witnessed by an actual coordinate-projection state of integer rank k=ceil((m-1)n/2), whose density, APPT and purity were connected previously. The new exact rounding identity proves the stated lower error, without using a noninteger projection rank.

`appt_fixed_local_purity_sup_tendsto` establishes the actual filter limit

    Tendsto (fun n => (mn)*P_sup(m,n)) atTop (nhds C_m)

for every fixed integer m>=2. This closes the complementary fixed-m regime; it is not an extrapolation of the earlier growing-m theorem. This endpoint does not assert finite-dimensional `IsGreatest` or classify maximizing spectra.

The companion theorem `appt_fixed_local_excess_sup_tendsto` subtracts the maximally
mixed baseline and proves the exact first excess coefficient

    Tendsto (fun n => (mn) * (P_sup(m,n) - 1/(mn))) atTop
      (nhds (1/(m^2-1))).

This is a direct physical supremum limit, with no spectral ansatz or unproved
attainment assumption. Separately, `PlateauOptimizer.lean` proves the exact square
deficit for every two-level projection plateau and shows that when `(m-1)*n` is even,
rank `((m-1)*n)/2` reaches the continuous two-level value and is maximal among all
plateau ranks. This is a family-restricted optimization statement, not the full
rectangular APPT maximum or a classification of all maximizing states.

## 2. One upper bound over all dimensional growth regimes

`appt_total_dimension_uniform_upper` proves: for every real epsilon>0 there is one natural N such that for all integers 2<=m<=n with mn>=N, and for every actual APPT density matrix A,

    (mn)^2*(purity(A)-1/(mn))
      <= (1+epsilon)*max(8,4+mn/(m^2-1)).

The threshold works simultaneously for fixed m, growing m, and arbitrarily unbalanced dimensions. The proof combines the new finite fixed-local bound with the previously verified growing-m upper theorem. It remains an UPPER theorem; the matching lower construction when m grows depends on still-unformalized graph limits.

The earlier finite pivot bound, its dimension-only normalization, and the explicit growing-m estimate remain in the same proof closure. The latter is valid for 8<=m<=n with coefficient [m/(m-7)]^2*max(8,4+n/m).

## 3. Independent kernel evidence

Run **38153054623**, tested source **57bc1b6f60a9a10b9c4f289f1644d402799b4369**, passed every independent job and reproduction stage. The fresh review-package Lake build completed **2,844 tasks**, retaining external dependency caches. The empty kernel at trust level **zero** replayed **42,101 transitive declarations and 87 explicit roots**. Its only axioms were `propext`, `Classical.choice`, and `Quot.sound`.

Both final endpoints were tested against forged proofs. The exact fixed-local supremum-limit theorem was rejected after only its proof was replaced by `True.intro`, following a full positive proof replay. A second independently checked type closure of **8,578 declarations** supported the same rejection test for the total-dimension uniform upper theorem. Neither theorem's type or universe parameters were altered.

All **57 pinned local inputs**, including original quantum definitions and replay support, matched both the tested commit and the publication worktree. Uploaded source modules, aggregate, regression, audit, runner and manifest were compared byte-for-byte. Literal logs, roots, declarations, axioms, both corruption controls, source hashes and workflow/artifact metadata are retained in **`verification/ci-57bc1b6f/`**.

These are independent CI and Lean-kernel checks, not external mathematical peer review. Earlier audit records retain their own source bindings and are not relabeled as the newer theorem.

## 4. Failure diagnosis and negative controls

The first independent run (38152532117, aa49f7fc) successfully built all mathematical modules and replayed 42,101 declarations with 87 roots, including the fixed-local theorem. It nevertheless FAILED overall: the added second `run_cmd` invocation ended before its arguments because of Lean's command layout. Joining that invocation onto one line fixed the audit wrapper. No mathematical module, theorem type, axiom policy or verification timeout was weakened. The complete workflow was rerun, and the literal failed record remains under `verification/failed-aa49f7fc/`.

The new physical regression roots include a 2x4 APPT state with scaled purity 4/3, rejecting a unit coefficient or the incorrect 1+1/m^2. A 4x5 APPT state has exact positive rounding gap 1/5415, rejecting equality with the continuous-rank optimum at that finite dimension. Existing false-PPT/APPT, wrong dimension constant, signed graph, row-order, summation-scope and zero-denominator controls remain audited.

An isolated development compiler was used while the authorized Windows builder was offline. Its receipts explicitly report compiler errors and are not proof certificates. That session was stopped. This checkpoint instead uses the separate normal proof workflow with the original committed module paths and full trust-zero audit.

## 5. Reproduction and dependencies

Lean **4.34.1** and Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** remain pinned. On Linux or WSL, from this directory:

```sh
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

The runner verifies source pins and the actual dependency checkout, builds only the imported review closure, compiles replay support with an explicit source root, runs physical controls, and replays all selected roots. Every stage has a finite timeout with process-group termination on timeout and retained diagnostics. `--write-manifest` records intended sources but does not verify them.

The new chain uses `FixedLocalRatio`, `IntervalMoment`, `FixedLocalUpper`, `PlateauApproximation`, `FixedLocalLimit`, `PlateauOptimizer`, `AllDimensionUpper`, and `FixedLocalChecks`. `REVIEW_FIXED_LOCAL_20261011.md` gives their mathematical dependency map. Earlier sorted entropy-head, contraction-sufficiency, projection-attainment and finite purity chains remain checked.

## 6. What is not yet certified

See `COVERAGE.md`. The growing-m matching lower bound still requires multiscale and two-ended graph compactness, simultaneous spectral levels, compatible lower witnesses, finite-dimensional positivity margins and justified limit order. No such lower bound follows from the now-verified all-regime upper half.

The joint projection-plus-spike sufficiency for the three-level counterexample, exact finite rectangular optimization and equality classification, full entropy minima and outlier/phase rigidity remain substantive formal obligations. Finite-dimensional attainment is now proved separately by the compactness checkpoint above; the older fixed-local theorem remains unchanged. No new preprint or Release was made, and the earlier qutrit proof, research notes and publication trees were not changed by these commits.
