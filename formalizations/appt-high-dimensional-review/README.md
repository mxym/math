# High-dimensional APPT: mathematical review and Lean verification

**The full research program remains partially formalized. The fixed-local purity supremum limit and its first excess-purity coefficient are now complete, and the purity upper half is verified uniformly over all dimension pairs as total dimension grows. The two-level projection plateau is also optimized exactly within the plateau family in the even-rank case. Matching growing-local-dimension lower limits, exact finite maxima/classification beyond that family, full entropy and rigidity claims remain unclosed.**

Every physical endpoint uses actual complex density matrices and the original all-global-unitary APPT definition. No spectral ansatz, unproved quantum characterization, graph cap or claimed main conclusion is assumed in the final physical theorems.

## Strengthened counterexample statement and physical failure controls

`proposedAPPTPurity` records the proposed dimension-dependent formula with its actual integer ceiling. `not_proposedAPPTPurity_upper` proves that it is NOT a universal purity upper bound on the original domain 2<=m<=n and n>2, using the actual 10x38 APPT density matrix. This is a fully quantified formula refutation, not just an unconnected numerical inequality. The source paper's separate polytope-optimization theorem is not claimed as formalized here.

The white-noise state

    rho_int = (999/1000) rho + (1/1000) I/380

is proved to be a density matrix and APPT, still has purity strictly exceeding the proposed value, and satisfies

    (U rho_int U*)^Gamma - I/380000 >= 0

for every global unitary U. `counterexample1038Interior_margin` proves this uniform positive orbit margin; the endpoint is that matrix inequality, not an independently stated topological-relative-interior classification.

The actual trace-one matrix `boundaryPerturbation1038` increases the spike coefficient from 24 to 25 in the explicit boundary layout. It is positive semidefinite but NOT APPT. The proof uses a genuine rectangular Hadamard-unitary witness and rejects it by exact arithmetic, rather than assuming a failed sampled orbit. Its support has 147 coordinates and includes the spike: the unnormalized levels are 42 once, 17 on the remaining 146 support coordinates and 15 on the other 233 coordinates, with trace 6019. `joint_scalar_boundary_and_failure` separately records the zero-to-negative scalar boundary, and `zero_schmidt_model` checks that zero test vectors are admitted by the general Schmidt construction.

**Final independent verification:** run **38202563748**, tested source **c129497bc843d2054533c405cf5d5201855c0a99**, passed every stage. The build completed **2869 tasks**; an empty trust-zero kernel replayed **42,496 transitive declarations and 208 explicit roots**, with only the three standard axioms. All **82 pinned inputs** matched the exact committed and uploaded source. The primary corrupted-proof control targets the full negation of the proposed universal upper formula. Ten additional corruption controls remain, including joint sufficiency, actual counterexample membership, its positive margin and the non-APPT perturbation. Literal logs and all source/control bindings are in `verification/ci-c129497b/`.

## Joint sufficiency and the original three-level counterexample

**New complete finite result:** `jointSpike_absolutelyPPT` proves all-global-unitary APPT for `(2m-5)I+2P+4(m-4)|v><v|` whenever m>=4, P and I-P are positive semidefinite, and v has squared norm one. The positivity theorem does not assume v lies in range(P), a supplied Schmidt decomposition, a graph inequality, or any APPT spectral criterion. It constructs a Schmidt row factorization from the actual complex matrix, including zero singular values, proves the signed partial-transpose model and trace duality, and applies the joint sum-of-squares inequality.

`counterexample1038_refutes_formula` then proves density, actual APPT, and the strict purity comparison for the original product-coordinate state

    rho = diag(41, 17 [146 copies], 15 [233 copies]) / 6018,
    purity(rho) = 2675/1006009 > max(97/36481,5/1881).

`counterexample1038_diagonal` verifies that these are the entries of the actual defined matrix, rather than an externally supplied spectrum. The finite support has exactly 147 coordinates; that count is kernel-decided and is not used as a replacement for the dimension-uniform quantum proof. The result refutes the displayed proposed purity formula at 10x38. It does not assert that this state is optimal, that these are the smallest counterexample dimensions, or that all subsequent research claims have been certified.

Independent Actions run **38200910959**, source **c7bd84ed1df6602d511fbee67f1c66f66809932f**, passed every stage: **2,866 Lake tasks**, **42,442 transitive declarations and 194 roots** replayed at trust level zero, with only `propext`, `Classical.choice`, `Quot.sound`. All **79 pinned inputs** matched the tested commit and downloaded artifact. The primary forged-proof test targets the final physical counterexample theorem. Additional tests preserve the exact theorem types and reject corrupted proofs of generic joint APPT sufficiency, actual counterexample membership, and the unnormalized Schmidt model. Literal evidence is in `verification/ci-c7bd84ed/` and the exact dependency map is in `REVIEW_JOINT_SUFFICIENCY.md`.

## Purity-ball sufficiency and the singular APPT locus

### Integrated source verification

Combined source **72f774d8e8400b58d342e7d9c460c5b138583467** also preserves the concurrent fixed-local excess-limit and even-rank projection-family optimization. Independent run **38190512755** passed all stages: **2,853 Lake tasks, 42,281 declarations, 142 roots, 66 pinned inputs**, trust level zero and only the three standard axioms. Evidence is in `verification/ci-72f774d8/`. The original singular-state checkpoint below retains its own source binding; the merge was independently verified rather than presumed correct from parent builds.



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

The joint projection-plus-spike sufficiency and the original 10x38 physical counterexample are now certified above. Exact finite rectangular optimization and equality classification, full entropy minima and outlier/phase rigidity remain substantive formal obligations. Finite-dimensional attainment is now proved separately by the compactness checkpoint above; the older fixed-local theorem remains unchanged. No new preprint or Release was made, and the earlier qutrit proof, research notes and publication trees were not changed by these commits.
