# High-dimensional APPT: mathematical review and Lean verification

## Constructive wide-sector continuation

The new finite rational-parameter construction, all-total-dimension lower branch, complete wide-sector purity asymptotic, and fixed-aspect limit for every gamma>=4 have passed a fresh local build and trust-zero replay. Independent CI for the exact committed source is pending at this source checkpoint. See `REVIEW_EFFECTIVE_LOWER.md` and the retained local audit. The coefficient eight for 1<=gamma<4, full entropy laws and dimension-varying rigidity remain unclosed.

**The exact rectangular purity maximum and all its maximizing spectra/unitary orbits are now complete in Lean. The overall high-dimensional research remains partially formalized: growing-dimension multiscale matching lower bounds, complete entropy extrema and asymptotic rigidity are not yet certified.**

Every physical endpoint uses actual complex density matrices, the original trace(A*A).re purity, and positivity after partial transposition of EVERY global-unitary conjugate. No spectral ansatz, supplied graph cap, unproved quantum characterization or assumed optimizing conclusion replaces those hypotheses.

## 1. Exact rectangular maximum and complete equality classification

For all integers m>=3 and n>=m^3-m-2, put D=mn and t=ceil((m-1)n/2). The final numerical theorem `appt_rectangular_maximum_formula` proves IsGreatest of the actual physical purity-value set with value

    [D(m-1)^2+4mt]/[D(m-1)+2t]^2.

`density_appt_rectangular_maximizer_iff` proves that an APPT density attains this maximum if and only if its canonically sorted eigenvalues are

    (m+1 repeated t times, m-1 repeated D-t times)/[D(m-1)+2t].

`appt_rectangular_isGreatest_iff_unitary` gives the complete state-level version: for an actual density matrix A, APPT together with IsGreatest of its purity is equivalent to existence of a global unitary U with A=U*roundedPlateauMatrix*U^*. The fixed representative is explicitly defined and proved density, APPT, and attaining. Neither APPT nor optimality is assumed on the orbit side. All integer ranks, parity cases, shortened supports and arbitrary convex combinations are included.

The proof first derives the exact top-R versus bottom-S cut from physical APPT. Explicit finite mass transport reduces every ordered spectrum to surviving prefixes and crossing edges. The rational edge objective is transformed into a convex quadratic, including strict endpoint inequalities. In the stated region every early or late prefix and every shortened support is strictly suboptimal. The sole remaining full-support middle prefix has the unique integer ceiling rank. The generic convex unique-boundary sublevel argument then classifies arbitrary mixtures. Exact coordinate identities and the unitary spectral theorem finish the physical orbit equivalence.

The cutoff is sufficient, not asserted minimal. For example m=10 requires n>=988, so this theorem does not contradict the independently verified 10x38 counterexample. The relaxation's complete behavior below the cutoff and the true smallest onset of two-level optimality are not being inferred here. See `REVIEW_RECTANGULAR_MAXIMUM.md` and `REVIEW_RECTANGULAR_CLASSIFICATION.md`.

## 2. Independent verification of the complete finite theorem

Run **38241340424**, tested source **e1f7774e267a5a15bc56d19d2301b4c5111cb8a6**, passed all jobs and all five reproduction stages. The fresh review-package Lake build completed **2,891 tasks**, retaining external dependency caches. An empty kernel with trust level **zero** replayed **42,729 transitive declarations and 268 explicit roots**. The only axioms were `propext`, `Classical.choice`, and `Quot.sound`.

The primary proof-corruption control targets `appt_rectangular_isGreatest_iff_unitary`. There are **15** checked exact-type rejection controls in this audit, including the sorted-spectrum equivalence and the arbitrary-spectrum cut equality theorem. Original proof closures passed first; the controls replace only the proof by True.intro and retain its exact type and universe parameters. All dependency lists and literal rejection diagnostics are preserved.

All **104 pinned inputs** match the exact tested commit and the current source. Every uploaded module, audit, regression, runner and manifest was compared byte-for-byte. Stage log hashes were checked. Evidence: **`verification/ci-e1f7774e/`**. The local WSL fresh build and trust-zero replay also passed for the same input manifest; its kernel log SHA-256 is 9859354b146e1a34869b10697c02cbfa348aa9c9b848972f2724496758cec8c6.

The preceding maximum-only checkpoint independently passed run 38238377463, source 1a3f6275d7979121f6babd6608567fdecbe304fa: 2,886 Lake tasks, 42,670 declarations, 247 roots, and 99 pinned inputs. That historical scope and evidence remain in `verification/ci-1a3f6275/`; it is not relabeled as the later equality proof. The earlier integer-rank/cut-reduction checkpoint remains in `verification/ci-8a0ec9ba/`.

## 3. Other completed results retained in the proof closure

The original 10x38 state diag(41,17 repeated 146 times,15 repeated 233 times)/6018 has a verified actual APPT proof and purity 2675/1006009 exceeding both proposed values. The full universal-formula negation retains its integer ceiling. The joint contraction-plus-spike sufficiency, arbitrary-vector signed Schmidt construction including zero singular rows, robust white-noise positive margin, and actual trace-one non-APPT boundary perturbation are verified. Their earlier independent records are `ci-c7bd84ed` and `ci-c129497b`.

Finite physical APPT compactness, actual attainment of the purity supremum, the entire attainable-purity interval, unique maximally mixed minimum and strict-mixture rigidity are verified. Purity-ball sufficiency and the necessary-and-sufficient singular APPT spectrum/purity classification, with an actual singular witness, are also verified. These are finite statements, not dimension-varying compactness/rigidity conclusions. Earlier evidence: `ci-0d7760e7`, `ci-4e647075`, and `ci-72f774d8`.

For each fixed m>=2, the physical supremum satisfies

    (mn)*P_sup(m,n) -> m^2/(m^2-1),
    (mn)*(P_sup(m,n)-1/(mn)) -> 1/(m^2-1).

The state set is proved nonempty and bounded, positive scaling of the supremum is justified, and actual integer-rank projection states provide the lower bound. For n>=2m the scaled errors are at most 1/n^2 below and 13m/n above. See `FixedLocalLimit`, `PlateauOptimizer`, and `verification/ci-57bc1b6f/`.

The all-total-dimension purity UPPER theorem proves that for every epsilon>0, one N works for every 2<=m<=n with mn>=N and every APPT density A:

    (mn)^2*(purity(A)-1/(mn)) <= (1+epsilon)*max(8,4+mn/(m^2-1)).

Its matching lower construction when m grows remains unclosed. The exact sorted physical entropy-head inequality is verified, but is only one dependency of the full entropy laws. `COVERAGE.md` distinguishes every such endpoint.

## 4. Reproduction, failures and provenance

Lean **4.34.1** and Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** remain pinned. On Linux/WSL, from this directory:

```sh
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

The runner checks the actual dependency checkout and source manifest, builds the imported review closure, compiles replay support with its explicit source root, runs physical controls and performs trust-zero replay. Every stage has a finite timeout, process-group termination on timeout and retained diagnostics. --write-manifest records intended inputs but does not prove them. The 2,891 build tasks include Mathlib/dependency targets, not that many newly written source modules; replay counts likewise include dependencies.

This continuation recovered unpublished maximum modules, read their proofs and reran a fresh complete build/replay before publication. A CRLF/LF discrepancy was detected and normalized BEFORE source-bound independent verification, followed by another complete local build. New equality modules compiled individually and then in a full fresh package. Initial local parsing/cast/simplification errors were repaired rather than bypassed. The checked controls include exact even/odd spectrum boundaries, a rejected wrong-floor spectrum, actual representative density/APPT/purity, and the earlier actual 10x38 counterexample to dropping the cutoff.

Windows GitHub transport was intermittent; exact SHA-256-checked source transfer to the authorized VPS was used. Concurrent main changes are preserved. No original quantum definition, axiom policy, verification workflow, preprint or immutable Release is changed. These are Lean-kernel and independent CI checks, not external mathematical peer review or new historical-priority claims.

## 5. Remaining program obligations

The main outstanding chain is the matching lower bound when both dimensions grow in the multiscale regime: joint graph compactness, simultaneous levels, compatible nested witnesses, finite-dimensional APPT margins and the order of limits. The complete all-regime asymptotic equivalence cannot be inferred merely from its verified upper half.

Full von Neumann/Renyi entropy extrema, dimensional outlier/bulk rigidity and other asymptotic equality claims remain unclosed. The unrestricted finite maximum outside the stated rectangular region is not evaluated by the new theorem. All such research claims remain explicitly separate from the completed finite rectangular maximum and its complete maximizing-state classification.
