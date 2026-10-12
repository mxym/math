# Actual common-window schedule geometry and endpoint entropy

Implementation: `Entry002/GenericWindowSchedule.lean`,
`Entry002/GenericWindowEntropy.lean`, `Entry002/GenericWindowTopEntropy.lean`,
and `Entry002/GenericWindowBandSizes.lean`.

Pinned source: OpenAI family028, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (Apache-2.0).
The source spans used are:

- `CommonBlocks.lean` lines 9–18 and 45–121: literal common/middle blocks,
  lengths, ordered-window tail bounds.
- `Smoothing.lean` lines 108–145: numerical suffix log-cost estimate.
- `BatchCertificate.lean` lines 247–267: schedule sum/log estimate, already
  ported as `GenericNumericalSchedule.schedule_log_bound`.
- `EntropyBand.lean` lines 205–242: subband-to-literal-schedule entropy transport.
- `AccurateScales.lean` lines 219–281: eventual accurate-band guards and suffix
  control; lines 284–317: size positivity/capacity arithmetic.
- `CommonBlocks.lean` lines 137–208: selected-window middle and bottom endpoints.
- `WindowParameters.lean` lines 271–341: separated selected top suffix and
  top-window anchor estimate.

The generic implementation preserves arbitrary additive L, a genuine
`Basis (Fin 2) ℤ L`, the full planar real linear equivalence e, actual dyadic
prime batches, and `ArithmeticInterface`. The only norms used are the actual
planar metric norms. The true `displacementPackingConstant` replaces the
Gaussian numeric coefficient 36.

`GenericWindowSchedule` defines the literal lists `commonBlocks` and
`middleBlocks`. `eventually_window_tail_bounds` derives the actual finite
metric-ball alphabet bounds Hbottom ≤ exp(3X/50) and Hrest ≤ exp(13X/50),
X=100^w exp(m), uniformly over every actual selected-bin list obeying the
window bounds. No displacement-entropy conclusion is presumed. Empty suffixes
are handled by enlarging the actual metric ball by one unit.

`GenericWindowEntropy.commonSchedule_subband_geometric_entropy` places a
proved geometric band between arbitrary literal pre/post lists. It derives the
actual endpoint bound after the suffix, using the actual finite-ball entropy
loss. Its exact-start form is supplied for backward coverage. The accurate
wrapper discharges geometric guards, batch capacity, and true suffix cost using
actual density. `eventually_window_band_entropy` gives the true middle and
bottom endpoint bounds with deficit 91*accurateGrid, for every actual walk and
every TimeLaw P. Thus it also holds at every natural future start.

`GenericWindowTopEntropy.eventually_window_top_entropy` proves the anchor after
**all** current-window selected top blocks, paying for the smaller selected-bin
suffix inside the anchor estimate. It gives deficit 1/10000, positive/capacity
ktop, actual mean 1≤μ≤2X, and
ktop≥topCoefficient(a)*T/(4log T). The threshold precedes every walk and start
law. The only separation premise is the actual bin gap produced by density
selection. No prior entropy or EntropyBand conclusion is an input.

`GenericWindowBandSizes.eventually_window_band_sizes` supplies positive middle
and bottom floor sizes and their true actual-batch capacities. These follow
from the proved density guards at the last accurate iteration.

No desired endpoint/coverage result is stored in an assumed certificate. The
new modules leave MainTarget, FiniteSieveTarget, and prime-supply files untouched.
The graph/engine integration modules combine these proved endpoints with actual
common-law factorization, backward coverage, and posterior entropy charges.

Validation: official Lean 4.34.1, pinned mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
Build evidence: `logs/GenericWindowChain-build.log`,
`logs/GenericWindowTopEntropy-build.log`, and
`logs/GenericWindowBandSizes-build.log` (clean).
Axiom audit: `logs/GenericWindowChain-audit.lean` and
`logs/GenericWindowChain-axioms.log`.
