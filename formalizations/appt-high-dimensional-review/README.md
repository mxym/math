# High-dimensional APPT: mathematical review and Lean verification

## Lacunary probability and compactness checkpoint

The canonical measurable bipartition, arbitrary common-probability-measure energy inequality, moving-strip weak limit, and one uniform strip-width threshold over all probability measures on [0,1] have passed a fresh local build and trust-zero replay. Independent CI of this exact source is pending at this checkpoint. No finite atomic approximation or presumed moving-set Portmanteau rule supplies these results. The sparse-graph localization, physical multiscale lower construction, coefficient-eight sharpness below aspect ratio four, full entropy and asymptotic rigidity remain separate obligations.

**The constructive broad-plateau lower branch and the complete wide-sector purity asymptotic are now verified. Every fixed finite aspect ratio gamma>=4 is covered, including approach to four from either side. The overall program remains partial: the matching multiscale coefficient eight for 1<=gamma<4, full entropy extrema and dimension-varying rigidity remain unclosed.**

All physical endpoints use actual complex density matrices, the original trace(A*A).re purity and positivity after partial transposition of EVERY global-unitary conjugate. No spectral ansatz or unproved graph limit replaces those objects.

## 1. Complete asymptotic results added in this checkpoint

Write D=mn and P_max for the actual attained APPT purity maximum. `appt_total_dimension_branch_lower` constructs states giving, uniformly over all integer 2<=m<=n as D grows,

    D^2 [Tr(rho^2)-1/D] >= (1-epsilon)[4+D/(m^2-1)].

Together with the unrestricted upper theorem, `appt_wide_relative_error` proves a two-sided relative asymptotic uniformly for n>=4m:

    D^2 [P_max(m,n)-1/D] / [4+D/(m^2-1)] -> 1.

`appt_wide_purity_asymptotic` is a genuine Tendsto theorem along every eventually admissible dimension sequence with total dimension tending to infinity. The smaller dimension may stay fixed, grow, or oscillate. Separately, `appt_large_aspect_purity_limit` proves

    D^2 [P_max(m,n)-1/D] -> 4+gamma

when m tends to infinity and n/m tends to any fixed finite gamma>=4. At gamma=4, ratios below four are allowed. These are unrestricted physical extrema, not optimization within the construction family. Existence, boundedness and attainment of the objective are connected through the previously verified compactness theorems.

## 2. Effective finite construction without multiscale compactness

For h>=1 and m>=2h^2+4h, put k=ceil(mn/2) and b=(h+1)m+2h^2+h. A rank-k coordinate projection P and a coordinate unit vector v in its range define

    B=b I+2h P+2mh |v><v|,
    rho=B/[mn b+2h(k+m)].

`effectiveSpike_absolutelyPPT` proves generic joint sufficiency for every positive contraction P and unit vector, with no range assumption needed for positivity. The coordinate range condition is used for the exact trace-square calculation. `exists_effective_lower` constructs the integer support and proves actual density, APPT and

    D^2 [purity(rho)-1/D] >= (h/(h+2))^2 (4+n/m).

All integer-parameter coefficients are explicit rational expressions. A finite Young/Cauchy sum-of-squares identity supplies positivity; no asymptotic Schmidt model, sampled unitary, compactness or interchange of hierarchy limits is assumed. `effective_ratio_error` provides the explicit parameter approximation h>=4/epsilon. See `REVIEW_EFFECTIVE_LOWER.md` for the complete dependency map and normalization identities.

The exact even 6x24 and odd 7x29 controls check support cardinalities, true APPT density and purity. A positive trace-one 2x2 matrix diag(8,8,26,8)/50 is proved NOT APPT after the finite interaction reserve is deleted. A separate exact test rejects replacing a finite family member by its limiting coefficient.

## 3. Independent verification

Run **38272300965**, exact source **c1bc61aa861f3d270c0f4ca669d8b154f5b81b98**, passed all jobs and all five reproduction stages. A fresh package build completed **2,900 tasks**, retaining external dependency caches. Empty-kernel replay at trust level **zero** checked **42,804 transitive declarations and 304 explicit roots**. Only `propext`, `Classical.choice` and `Quot.sound` were found as axioms.

All **113 pinned inputs** match the tested commit and the current source. Uploaded sources, audit, regressions, runner, manifest and every stage log were checked against exact hashes. **19 exact-type corruption controls** reject forged proofs after the original positive replay, including the final aspect limit, the all-total-dimension wide limit, generic physical joint sufficiency, the actual finite lower witness and the uniform total-dimension lower branch. No theorem type or universe parameter is altered. Evidence: `verification/ci-c1bc61aa/`.

The local WSL fresh build/replay also passed. Its source-bound logs are retained separately in `verification/local-effective-20261012/`. Only this working branch was added to the existing workflow push trigger; all verification jobs, commands, axiom policies and limits stayed unchanged. This is independent CI and Lean-kernel verification, not external mathematical peer review or a priority claim.

## 4. Earlier complete finite and asymptotic results retained

The exact rectangular maximum for m>=3,n>=m^3-m-2 and its complete sorted-spectrum/global-unitary-orbit classification remain verified (`ci-e1f7774e`). The actual 10x38 counterexample, universal formula refutation, generic joint sufficiency, white-noise positive margin and physical failing perturbation remain verified (`ci-c129497b`). Finite physical compactness, attained maxima, the attainable purity interval, unique mixed minimum, singular APPT spectrum/purity equivalence and purity-ball sufficiency remain verified in their corresponding historical checkpoints.

For every fixed m>=2, the actual purity supremum has the complete limit (mn)P_max -> m^2/(m^2-1), with matching finite errors and exact integer projection rounding. The all-total-dimension upper coefficient max(8,4+mn/(m^2-1)) and the finite spectral-pivot upper inequalities remain in the same audited closure. The finite nonlinear entropy-head statement is verified, not the entire entropy law. See `COVERAGE.md`; historical records retain their original source bindings.

## 5. Reproduce and remaining scope

Lean **4.34.1** and Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** remain pinned. On Linux or WSL, from this directory:

```sh
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

The runner checks actual dependency/source pins, uses finite stage timeouts, terminates timed-out process groups, retains failures, and replays the full selected proof closure. The new modules are EffectiveJointScalar, EffectiveJoint, EffectiveLowerScalar, EffectiveState, EffectiveAsymptotic, TotalBranchLower, WideAsymptotic, LargeAspectLimit and EffectiveControls.

The remaining sharp lower coefficient eight for fixed 1<=gamma<4 requires the multiscale graph argument or another valid construction. This checkpoint proves 4+gamma there as a lower branch, not equality with the true optimum. Full entropy minima, dimension-varying phase/outlier rigidity and the multiscale/two-ended compactness dependencies remain unverified. Exact finite maxima outside the rectangular theorem remain a separate research question. No new preprint or immutable Release is made; the original quantum definitions and published proof trees remain unchanged.
