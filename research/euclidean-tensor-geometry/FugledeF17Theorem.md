# Fuglede's conjecture holds in F_17³

**Theorem.** A nonempty subset of the three-dimensional vector space over the field of order 17 has an orthogonal basis of additive characters if and only if it tiles the space by translations.

This is an exact computer-assisted proof for the single finite space F_17³. It does not imply the Euclidean conjecture or the conjecture over a general prime field.

## Reduction and proof index

The reductions of Aten et al., recalled in [Ferguson and Iosevich, §8](https://arxiv.org/html/2610.30712v1#S8), show that tiles are spectral, spectral sets of sizes 1, p, p² and p³ tile, and the only remaining candidate spectral cardinalities are mp with 2 ≤ m ≤ p−1. [Malikiosis, Theorem 1.4](https://doi.org/10.1007/s43670-023-00078-2) excludes sizes strictly between p²−(p−1)√p and p². For p=17 this excludes 238, 255 and 272. The [classical cyclotomic determinant obstruction](FugledeCyclotomicDeterminantObstruction.md), due to de Launey, excludes 51, 85, 119, 187 and 221.

The seven remaining cardinalities are excluded by the following arguments and their linked exact verifiers:

| Size | Proof |
| ---: | --- |
| 34 | [Radon profile census, spatial lift obstruction, and incidence](FugledeF17Size34Final.md) |
| 68 | [Pencil and profile exclusion](FugledeF17Size68Final.md) |
| 102 | [Moments and weighted polarity](FugledeF17Size102Final.md) |
| 136 | [Profile and support exclusion](FugledeF17Size136Final.md) |
| 153 | [Moment and two-layer exclusion](FugledeF17Size153TwoLayersFinal.md) |
| 170 | [Support exclusion](FugledeF17Size170.md) |
| 204 | [High-cardinality exclusion](FugledeF17Sizes187204.md) (the 187 part is not needed) |

Thus all candidate cardinalities are covered. The finite verifiers use integer and finite-field arithmetic, not numerical tolerance or probabilistic search. The proof is offered for public checking; it is not a claim of formal verification or external peer review.
