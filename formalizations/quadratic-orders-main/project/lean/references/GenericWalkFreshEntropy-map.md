# Walk fresh entropy: actual geometric and sampling chain

Source: `upstream-028/GaussianMoat/PointEnrichment.lean`, OpenAI family028,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; Apache-2.0. Adapted
spans: `differenceLaw_fresh` (263–289), scalar `fresh_error_bounds` /
`fresh_gap_bound` (365–409), `differenceLaw_fresh_lower` (410–457), and
`walk_fresh_lower` (473–573).
Implementation: `Entry002/GenericWalkFreshEntropy.lean`, namespace
`Entry002.WalkFreshEntropy`.

The module uses the genuine `walkDifferenceLaw`: uniform over the actual finite
vertex difference set, pushed to proved representative endpoint pairs. Fresh
observations are the supplied maps `data.phi` and shared
`Entry002.signedFreshCoordinate`. The geometry is `ActualWalkFrame`, itself
proved from actual planar metric steps, self-avoidance, attained diameter,
minimum lattice separation, discrete path geometry, and actual rectangle packing.
No supplied fresh-entropy, many-differences, or signed-rectangle result substitutes
for these dependencies.

| Dependency | Generic theorem |
| --- | --- |
| Actual uniform displacement transfer | `differenceLaw_fresh` |
| Differences of displacements in fourfold true rectangle | `frame_difference_differences` |
| Scalar event-error and gap bounds | `fresh_error_bounds`, `fresh_gap_bound` |
| Scalar fresh-coordinate lower synthesis | `differenceLaw_fresh_lower` |
| Walk size to area from true packing | `frame_log_packing` |
| Actual displacement cardinality lower bound | `frame_log_difference_size` |
| Actual displacement support upper bound | `frame_log_difference_support` |
| Frame-backed actual fresh estimate | `frame_fresh_lower` |
| Fixed lattice constants and automatic all-walk frame | `walkFrameConstants_spec`, `walk_fresh_lower` |

The strongest theorem `walk_fresh_lower` applies to every actual finite
self-avoiding bounded-step walk in every full rank-two integral planar lattice,
with its actual unchanged `ArithmeticInterface`. It proves an admissible fresh
index `m<|S|` and
`(1−30g)*batchMeanLog S ≤ signedFreshCoordinate(data,S,walkDifferenceLaw z n,...)`.
It chooses the auxiliary prefix length internally. Constants C (packing), H
(frame factor), and A (cell area/A4 scale) are fixed by the lattice/interface
before selecting any walk or starting position.

Its remaining hypotheses are explicit scalar bounds, with
`u=log n−log C`: `mean≤g*u`, `5120*mean≤g^4*u`, `m*mean≤g*u`,
`log(16A)+log(H*max(1,D,actual4Dball.card*cellArea))≤g*u`, and
`2*(2log n+log(16A)+2log D)≤|S|*mean`, together with ordinary dyadic prime
bounds, `mean≥1`, `0<g≤1/100`, `D≥1`, and `n≥1`.
The final multiscale/A5 synthesis must arrange these scalar inequalities; this
module does not claim that parameter selection. Its mean is
`Entry002.FreshEntropy.batchMeanLog`, literally the same finite expectation as
`Entry002.batchMeanLog`; it avoids importing the latter's separately edited
batch-selection module solely for this definitional bridge.

Validation: Lean 4.34.1 and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
Logs: `logs/GenericWalkFreshEntropy-build.log`,
`logs/GenericWalkFreshEntropy-axioms.log`.
