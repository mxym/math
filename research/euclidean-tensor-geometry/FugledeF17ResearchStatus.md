# Fuglede over \(\mathbb F_{17}^3\): verified cardinality exclusions

[The completed theorem and proof map](FugledeF17Theorem.md) show that Fuglede's conjecture holds for the three-dimensional vector space over the field of order 17. The proofs combine existing exclusions with exact verification for the remaining cardinalities, continuing the finite-field direction of [Ferguson and Iosevich](https://arxiv.org/abs/2610.30712).

| Spectral cardinalities excluded | Proof and exact verifiers |
|---:|---|
| 221 | [Planar-cap bootstrap](FugledeF17Size221CapBootstrap.md) |
| 204, 187 | [Moment and quadratic-profile exclusions](FugledeF17Sizes187204.md) |
| 170 | [Tight-pencil weight obstruction](FugledeF17Size170.md) |
| 153 | [Moment rigidity](FugledeF17Size153MomentEleven.md) and [two-layer exclusion](FugledeF17Size153TwoLayersFinal.md) |
| 136 | [Degree-nine moments](FugledeF17Size136MomentNine.md) and [final geometric and weighted exclusion](FugledeF17Size136Final.md) |
| 119 | [Degree-nine moments](FugledeF17Size119MomentNine.md), [degree eleven](FugledeF17Size119MomentEleven.md), and [final degree and weight obstruction](FugledeF17Size119Final.md) |
| 102 | [Degree-nine moments](FugledeF17Size102MomentNine.md) and [weighted degree-and-support obstruction](FugledeF17Size102Final.md) |
| 85 | [Degree-nine moments](FugledeF17Size85MomentNine.md) and [weighted and unweighted incidence obstruction](FugledeF17Size85Final.md) |
| 68 | [Degree-eight moments and plane cap twelve](FugledeF17Size68MomentEight.md) and [final incidence obstruction](FugledeF17Size68Final.md) |
| 51 | [Classical cyclotomic determinant obstruction](FugledeCyclotomicDeterminantObstruction.md) |
| 34 | [Exact Radon census, spatial lift obstruction, and incidence](FugledeF17Size34Final.md) |

The general [Malikiosis bound](https://doi.org/10.1007/s43670-023-00078-2) already excludes \(238,255,272\). The theorem index accounts for every possible spectral cardinality.

## Prior-art clarification

[The classical determinant sieve](FugledeCyclotomicDeterminantObstruction.md) already excludes 51, 85, 119, 187, 221, and 255. The listed geometry at those sizes gives independent proofs or reductions, not new nonexistence results relative to the classical obstruction. The [size-51 degree-six](FugledeF17Size51MomentSix.md) and [degree-seven](FugledeF17Size51MomentSeven.md) computations are retained as auxiliary research notes.

## Final step at size 34

[The initial reduction](FugledeF17Size34InitialReduction.md) rules out full planes, gives affine plane cap eight and uniform-pencil cap eight, and proves the first four mixed moments must vanish. The [sharper pencil and plane bounds](FugledeF17Size34PencilCapSeven.md) improve the caps to seven and six, respectively, and [the degree-five argument](FugledeF17Size34MomentFive.md) adds fifth moment vanishing. [Every tight pencil has at least twelve positives](FugledeF17Size34TightCapTwelve.md). The exact [five- and six-plane mask calculation](FugledeF17Size34SixDirectionsLowDegree.md) then leaves only its genuine degree-ten case. The [final census and lift obstruction](FugledeF17Size34Final.md) reject the unique Boolean projection and finish the exclusion.
