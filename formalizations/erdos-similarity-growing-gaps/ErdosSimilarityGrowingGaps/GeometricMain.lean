import ErdosSimilarityGrowingGaps.GeometricSpec
import ErdosSimilarityGrowingGaps.RoutingMain
import ErdosSimilarityGrowingGaps.CountableExhaustion

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory

/-- The finite routing theorem supplies the compact blocker specification at
all dyadic coefficient scales and all finite tails. -/
theorem smallCompactBlockerSpec_proved : SmallCompactBlockerSpec := by
  intro K hK k N δ hδ hδ₁
  exact exists_compact_power_blocker hK hδ hδ₁

/-- The geometric affine-tail conclusion obtained after the signed dyadic
coefficient cover and countable open exhaustion. -/
theorem geometric_main_target : MainTarget :=
  mainTarget_of_smallCompactBlockerSpec smallCompactBlockerSpec_proved

end ErdosSimilarityGrowingGaps
