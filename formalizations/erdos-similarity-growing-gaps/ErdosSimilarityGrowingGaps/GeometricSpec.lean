import ErdosSimilarityGrowingGaps.RoutingMain

namespace ErdosSimilarityGrowingGaps

open Set MeasureTheory
open scoped ENNReal

def SmallCompactBlockerSpec : Prop :=
  ∀ K : ℕ, 2 ≤ K → ∀ (k : ℤ) (N : ℕ) (δ : ℝ),
    0 < δ → δ < 1 → ∃ H : Set ℝ,
      IsOpen H ∧ OnePeriodic H ∧ unitDensity H < ENNReal.ofReal δ ∧
        CompactPowerHits H K k N

def AvoidsGeometricTails (E : Set ℝ) : Prop :=
  ∀ (a b q : ℝ), a ≠ 0 → 0 < q → q < 1 →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a * q ^ n + b ∉ E

def MainTarget : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Icc 0 1 ∧
      ENNReal.ofReal (1 - ε) < volume E ∧ AvoidsGeometricTails E

end ErdosSimilarityGrowingGaps
