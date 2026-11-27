# Fuglede's conjecture holds in \(\mathbb F_{13}^3\)

**Theorem.** Every nonempty subset of the three-dimensional vector space over \(\mathbb F_{13}\) is spectral if and only if it tiles by translations. This is about this particular finite vector space, not Euclidean space or arbitrary primes or dimensions.

## Reductions and proof map

We use the standard cardinality reduction for prime fields in dimension three, stated in [Ferguson and Iosevich, §8](https://arxiv.org/html/2610.30712v1) and originating in [Aten et al.](https://doi.org/10.1016/j.jfa.2016.10.018). Any tile is spectral. Spectral sets of size \(1,13,169,2197\) tile, and the only other candidate sizes are \(13m\), \(2\le m\le12\). The [linear programming bound of Malikiosis](https://doi.org/10.1007/s43670-023-00078-2) excludes sizes \(130,143,156\), since \(169-12\sqrt{13}<130\). The remaining exact exclusions are:

| Cardinality | Exact argument |
|---:|---|
| 26 | [Plane and pencil bounds](FugledeF13Size26UniformPlaneCaps.md); [final projection and secant contradiction](FugledeF13Size26Final.md). |
| 39 | [No layers and degree-five moments](FugledeF13Size39MomentsFiveNoLayers.md); [degree six and plane cap nine](FugledeF13Size39MomentsSix.md); [arithmetic profile reduction](FugledeF13Size39ConditionalMomentSevenEndgame.md); [heavy planes and mixed incidence](FugledeF13Size39FinalHeavyPolarity.md). |
| 52 | [Degree-seven moments and no layers](FugledeF13Size52MomentsSevenNoLayers.md); [mixed weighted incidence](FugledeF13Size52FinalWeightedSupport.md). |
| 65 | [Degree-eight moments](FugledeF13Size65MomentsEight.md); [weighted polarity](FugledeF13Size65FinalWeightedPolarity.md). |
| 78 | [Grid moments](FugledeF13Size78GridMoments.md); [cross moments](FugledeF13Size78CrossMoments.md); [final divisibility](FugledeF13Size78FinalDivisibility.md). |
| 91 | [Geometric stage](FugledeF13Size91Geometric.md); [weighted profiles](FugledeF13Size91WeightedProfiles.md); [final incidence](FugledeF13Size91FinalIncidence.md). |
| 104, 117 | [Dense cardinalities](FugledeF13DenseCardinalities.md). |

All computations in the size-26 proof and the arithmetic proofs for the other sizes use finite exact arithmetic. The JavaScript verification programs require no third-party dependencies, and the respective proof notes state their coverage and link to their scripts. The argument builds on the geometric approach of [Fallon, Mayeli and Villano](https://arxiv.org/abs/1902.02936) and the moment/profile computations of [Ferguson and Iosevich for \(p=11\)](https://arxiv.org/abs/2610.30712); the field-13 projection catalogs and incidence contradictions are given here. The bound on planar Boolean sets of size 52 with four special directions is independently available from [Qihang Wang, Appendix A](https://arxiv.org/html/2609.20495v2#A1).
