# High-dimensional APPT: verified sharp purity law

## Full entropy upper and saturation continuation

The full von Neumann fixed-finite-aspect upper bound and the equivalence between entropy-coefficient saturation and flat purity-coefficient saturation are now independently checked. `appt_full_entropy_head_saturation` closes the previous missing implication from the FULL entropy objective to head saturation. This does not prove existence of an entropy-attaining family or the complete minimum-entropy law. See `ENTROPY_GLOBAL_COVERAGE.md`, `REVIEW_ENTROPY_GLOBAL.md`, and source-bound evidence in `verification/entropy-ci-d2a9ff63/` (run 38536151448, 75 inputs, 41806 declarations, 53 roots, trust zero). The original purity and entropy-head audits retain their own unchanged scopes.

**The complete leading excess-purity asymptotic is now Lean-verified uniformly over all dimension pairs 2<=m<=n as mn grows. The overall research is not fully formalized: complete entropy extrema, dimension-varying spectral rigidity, and several more refined hierarchy claims remain separate obligations.**

All physical endpoints use actual complex density matrices, the original trace(A*A).re purity, and positivity after partial transposition of EVERY global-unitary conjugate. No assumed graph cap, spectral ansatz, lower bound, or main conclusion is a final physical hypothesis.

## 1. Complete sharp purity formula

Let D=mn and P_sup(m,n) be the existing supremum over the actual physical APPT states, proved nonempty, bounded and attained. Set K(m,n)=max(8,4+mn/(m^2-1)). The final quantified theorem `appt_sharp_purity_relative_error` proves

    for every epsilon>0, there is ONE N such that every 2<=m<=n, mn>=N satisfies
    |D^2*(P_sup(m,n)-1/D)/K(m,n)-1| <= epsilon.

`appt_purity_excess_equivalent` proves the corresponding actual filter limit along EVERY sequence with growing total dimension. Fixed, growing, oscillating and arbitrarily unbalanced smaller dimensions are all covered. This completes the matching coefficient-eight lower half, not just the previously verified upper bound or wide-sector result.

`appt_all_aspect_purity_limit` proves D^2*(P_sup-1/D)->max(8,4+gamma) for every finite fixed gamma>=1 with m->infinity and n/m->gamma. The critical ratio four may be approached from either side or crossed repeatedly. `appt_balanced_excess_limit` gives m^4*(P_sup(m,m)-1/m^2)->8. These are leading excess asymptotics, not exact finite-dimensional interpolation formulas or effective moderate-dimensional thresholds.

## 2. Proof mechanism and review

The prior lacunary common-measure compactness, finite sparse localization, rank-sensitive Schmidt compression, spike decoupling and actual normalized projection-state APPT theorem remain in the full checked closure. The new moment argument proves nonnegative cross traces of arbitrary positive semidefinite matrices. It needs no nesting or commutation hypothesis for the projections. Every integer floor, trace-centering term and denominator loss is retained; the lower expression converges uniformly in n>=m for each fixed finite hierarchy.

Choose J=2h^2 distinct scales 1/3,...,3^(-J), energy 2h^2/(h+1)^4 at each scale, and spike 2h/(h+1). The APPT budget equals the spike and is strictly below two. The total target energy is 4(h/(h+1))^2+4(h/(h+1))^4>=8-24/(h+1). For a requested error, h is fixed BEFORE the dimension threshold. No unproved interchange with a growing hierarchy is used. The construction uses exact real coefficients; rational matrix entries are not claimed for this implementation.

The coefficient-eight construction combines with the earlier all-dimensional broad branch. Bounded smaller dimensions automatically fall in the broad branch when total dimension is large enough. The existing physical upper bound then yields the complete relative equivalent. See `REVIEW_SHARP_PURITY.md` for the dependency map, normalization algebra and review boundaries.

Nine unpublished modules were recovered, independently read and recompiled; four further modules assemble the final all-regime and all-aspect laws and controls. Earlier development receipts were not treated as fresh full verification.

## 3. Independent source-bound verification

Independent run **38441930508**, exact tested source **abf3fb4eb3efb4efa2847838005c63f70ab03c27**, passed every job and all five reproduction stages. The fresh review-package build completed **3,157 tasks**, retaining external dependency caches. A trust-zero empty kernel replayed **50,788 transitive declarations and 444 explicit roots**. Its only axioms were `propext`, `Classical.choice`, and `Quot.sound`.

All **154 pinned inputs** matched the tested commit and downloaded sources. Stage logs were hash-checked. The primary proof corruption test targets the full formula `appt_purity_excess_equivalent`; **30 exact-type controls** were rejected after positive proof replay, including the actual coefficient-eight existence theorem, finite canonical matrix lower bound and all-aspect limit. No failed proof, missing dependency or timeout counts as a passing control. Evidence: `verification/ci-abf3fb4e/`.

The new mathematical controls reject dropping trace centering, replacing an integer floor by a real rank, or erasing nonzero positive cross moments. Every finite hierarchy is proved strictly below eight, and the balanced physical supremum limit is a separate audit root. Earlier counterexample, APPT-versus-PPT, wrong dimension constant, parity, signed-matrix and cutoff controls remain in the same closure. This is independent CI and kernel verification, not external peer review or a new priority claim.

## 4. Earlier completed finite results remain verified

The qutrit result is unchanged in its separate full package. This review package retains the actual 10x38 counterexample and its robust positive margin, joint spike/contraction sufficiency, complete singular-state locus, physical compactness and attainment, exact attainable-purity interval, and the finite nonlinear entropy-head bridge. The exact rectangular maximum and complete maximizing-spectrum/unitary-orbit classification hold for m>=3,n>=m^3-m-2; that cutoff is sufficient, not asserted minimal.

The fixed-m limit, wide-sector law and integer plateau optimizer remain verified predecessors. The new theorem subsumes their leading-asymptotic scalar scopes without relabeling their historical audits. Earlier source-bound directories and original failure records are retained.

## 5. Reproduction

Lean **4.34.1** and Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** remain pinned. From this directory on Linux or WSL:

```sh
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

The runner checks actual source and dependency hashes, rebuilds the review closure, compiles replay support with an explicit source root, runs mathematical controls and replays every selected root at trust level zero. Every stage has a finite timeout and process-group termination. `--write-manifest` records an intended source set, not verification.

## 6. Remaining scope

Complete von Neumann/Renyi extrema and dimension-varying bulk/outlier rigidity are still unclosed in Lean. The exact optimal energy of every finite hierarchy and the full two-ended graph theory are not inferred from the sufficient lacunary bound used here. Exact finite maxima outside the already verified rectangular region, next-order expansions, minimal rectangular cutoffs, efficient dimension thresholds, and APPT versus absolute separability remain separate. This checkpoint creates no preprint or Release and changes no original quantum definition.
