# Fuglede over \(\mathbb F_{17}^3\): verified cardinality exclusions

These are partial results for the three-dimensional vector space over the field of order 17, continuing the finite-field direction of [Ferguson and Iosevich](https://arxiv.org/abs/2610.30712). They do not solve the full conjecture for this field.

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

The general [Malikiosis bound](https://doi.org/10.1007/s43670-023-00078-2) already excludes \(238,255,272\). Using the standard dimension-three spectral cardinality reduction, the remaining non-prime-power candidate sizes in \(\mathbb F_{17}^3\) are \(34,51,68\).

## Partial progress at size 68

[The degree-seven reduction](FugledeF17Size68MomentSeven.md) proves that a putative size-68 spectral pair has no full affine planes and its moments vanish through degree seven. A [projection-grid exclusion](FugledeF17Size68PencilCapEleven.md) further shows that each projective line contains at most eleven uniform normals. The [low-degree obstruction](FugledeF17Size68LowDegree.md) forces both members to have genuine degree at least six and at least one to have degree seven or eight. The [degree-eight geometric reduction](FugledeF17Size68DegreeEightGeometry.md) forces a putative degree-eight moment zero set of uniform normals to meet every projective line in at least four sites. The [moment-eight proof](FugledeF17Size68MomentEight.md) excludes every octic profile and sharpens the affine plane cap to 12. Therefore at least one member has a genuine septic. Size 68 has not been excluded.
