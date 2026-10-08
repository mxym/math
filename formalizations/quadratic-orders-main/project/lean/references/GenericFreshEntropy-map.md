# Actual fresh entropy: source-to-interface map

Source: `upstream-028/GaussianMoat/FreshEntropy.lean`, OpenAI family 028,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; Apache-2.0.
Implementation: `Entry002/GenericFreshEntropy.lean`, namespace
`Entry002.FreshEntropy`.

This module generalizes the source argument to an actual rank-two integral
lattice `L`, a full actual planar embedding, `SignedResidueData`, and its unchanged
`ArithmeticInterface`. Every observation is the shared genuine
`signedResidueVector data S σ x`, namely the natural-number value of the actual
`ZMod p` image. Coding injectivity is proved with `ZMod.val_injective` at actual
prime moduli. No Gaussian factorization, complex multiplicative norm, or entropy
result is assumed.

| Upstream dependency | Generic replacement | Inputs |
| --- | --- | --- |
| Uniform sign restriction | `expect_precomp_injective`, `expect_sign_restriction` | Actual finite sign maps and injective prefix indices |
| `prefixSet`, `prefixIndex` | `batchPrefixSet`, `batchPrefixIndex` | Literal finite selected-prime enumeration and permutation |
| `prefix_injective_of_no_bad` | `prefix_injective_of_no_bad` | Actual additive residue maps and prescribed difference-region containment |
| `prefix_entropy_rectangle` | `prefix_entropy_rectangle` | Proved generic signed-rectangle probability, not a probability assumption |
| `prefix_product_tail` | `prefix_product_tail` | Generic permutation interval concentration; actual prime log products |
| `signed_prefix_entropy` | `signed_prefix_entropy` | Prefix product concentration and proved rectangle probability |
| `residue_prefix_entropy_le` | `residue_prefix_entropy_le` | Actual prime alphabet entropy budget from GenericResidues |
| `actual_fresh_entropy` | `actual_fresh_entropy` | Generic finite-law prefix/fresh accounting and actual difference identity |
| Shared enrichment interface | `actual_fresh_coordinate_entropy` | Exactly `Entry002.signedFreshCoordinate`, uniform true displacement law |

For nonempty finite displacement set Δ, actual endpoints `X−Y=ω`, and
`Δ−Δ` contained in the actual oriented rectangle, the strongest theorem proves

`(1−r(log 2)²/δ²−exp(−d³r/5120))*log|Δ|−2m log(2T)
 ≤ (r−m)*signedFreshCoordinate(data,S,uniform Δ,X,Y,m)`.

Assumptions: `m<r≤|S|`, actual selected primes satisfy `5≤T` and
`T≤p≤2T`, `1≤W≤R`, `0<d<1/4`, `δ>0`, `1000≤d³r`, and
`log(D*R*W)≤(1−d)*(r*batchMeanLog S−δ)`.
Here `D=max(2/actualCellArea,sqrt(2)*sqrt(A4Constant))`, independent of
orientation. The actual rectangle estimate and its A4 constant are proved in
GenericSignSeparation. The remaining overall synthesis must choose finite batches
and scalar parameters satisfying these geometric/logarithmic inequalities, then
combine this theorem with actual walk displacement extraction, time-law transfer,
and coverage accounting. This module does not claim that final synthesis.

Validation: Lean 4.34.1, pinned mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
Logs: `logs/GenericFreshEntropy-build.log` and
`logs/GenericFreshEntropy-axioms.log`.
