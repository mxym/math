import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic

namespace ErdosSimilarityGrowingGaps
open Filter

/-- A positive, strictly increasing logarithmic scale tending to infinity. -/
structure LogScale where
  z : ℕ → ℝ
  strictMono : StrictMono z
  tendsto_atTop : Tendsto z atTop atTop
  positive : ∀ n, 0 < z n

/-- The consecutive gaps are eventually smaller than every positive multiple of
    `log (log z n)`.  The threshold is stated with the positivity of the
    iterated logarithm made explicit, so all later expressions are defined in
    the ordinary real order. -/
def ConsecutiveLogGapLittleO (Z : LogScale) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    1 < Real.log (Z.z n) ∧
    Z.z (n + 1) - Z.z n ≤ ε * Real.log (Real.log (Z.z n))

/-- A finite annulus is filled at scale `D` if every closed interval of length
    `D` lying in the annulus contains one logarithmic sample. -/
def FillsAnnulus (Z : LogScale) (U R : ℝ) (D : ℝ) : Prop :=
  0 < U ∧ 2 ≤ R ∧ 1 ≤ D ∧
    ∀ v : ℝ, U / R ≤ v → v + D ≤ R * U →
      ∃ n : ℕ, v ≤ Z.z n ∧ Z.z n ≤ v + D

/-- Property W from the paper, expressed without an informal choice of a
    subsequence: each annulus ratio has arbitrarily late filled annuli whose
    filling scale is `o(log log U)`. -/
def AnnularFilling (Z : LogScale) : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    ∀ η : ℝ, 0 < η →
      ∀ U₀ : ℝ, 0 < U₀ →
        ∃ U D : ℝ, U₀ ≤ U ∧ 1 ≤ D ∧ D ≤ η * Real.log (Real.log U) ∧
          FillsAnnulus Z U R D

/-- The local interval consequence used in the routing proof. -/
theorem FillsAnnulus.sample_mem
    {Z : LogScale} {U R D v : ℝ}
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) :
    ∃ n : ℕ, v ≤ Z.z n ∧ Z.z n ≤ v + D := by
  exact h.2.2.2 v hv hvD

end ErdosSimilarityGrowingGaps
