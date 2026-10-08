# Actual floor-based geometric scale synthesis

Implementation: `Entry002/GenericGeometricScale.lean`.
Source: pinned OpenAI family028 `MultiscaleSchedule.lean` lines212–322,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a` (Apache-2.0).

`geometric_fresh_scale_from_scale` constructs all `GeometricFreshScale` fields,
index positivity/order/capacity/ratio, and the actual finite-ball displacement
cost for `n=floor(exp(gU))`, `q=floor(U/μ)`, `m=floor(g²U/μ)`, at margin `2g`.
The mean μ is the actual finite selected-prime mean logarithm. The proof preserves
the upstream floor and scalar arithmetic, while replacing Gaussian constants by
proved true lattice constants: C from all-walk packing, A from cell area and A4,
H from the actual walk frame, and B from actual metric-ball quadratic packing.
`wordStepBall_eq_planarLatticeBall` proves the two existing actual metric-ball
constructions equal; `displacementPackingConstant_spec` derives the cost rather
than assuming it.

`eventually_uniform_geometric_fresh_scales` proves all fixed-lattice guards
for every sufficiently large U, uniformly over actual batches with
`1≤μ≤2X`, `1280X≤g⁵U`, and `floor(U/μ)≤|S|`. Its scale threshold is independent
of S and X. The proof combines explicit linear thresholds; it assumes no
fresh-information, rectangle probability, or margin result.

The varying-grid strengthening `uniform_geometric_fresh_scales_of_guard`
uses the explicit fixed lattice constant `geometricGuardConstant`, defined as
the maximum of 1 and the four original guard coefficients. For every
`0<g≤1/200`, the single inequality `geometricGuardConstant≤g²U` implies all
four guard inequalities and positive U. Equivalently, its sufficient threshold
is `geometricGuardConstant/g²`. The constant is independent of g and S;
the proof uses only `g²≤g≤1` and the actual fixed lattice coefficients. This
provides quantitative control for accurate grids with g varying in m, which
does not follow from an existential threshold for each fixed g.

The remaining batch mean/relative-size/capacity hypotheses are numerical
constraints on the actual selected prime set. The actual density and schedule
selection modules supply those separately.

Validation: Lean 4.34.1 and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
Logs: `logs/GenericGeometricScale-build.log`,
`logs/GenericGeometricScale-axioms.log`.
The explicit varying-grid additions also appear in
`logs/GenericGeometricExplicit-build.log`.
