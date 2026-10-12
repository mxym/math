import ErdosSimilarityGrowingGaps.VariableRateSchedule

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! The ceiling in `lateBranching` gives a uniform entropy margin.  This is
stronger than mere positivity of the decay coefficient and is useful when a
late annulus is allowed to vary with the origin. -/
theorem lateBranching_decay_ge_two (K : ℕ) (hK : 2 ≤ K)
    (p δ D : ℝ) (hp : 0 < p) (hδ : 0 < δ) (hD : 0 ≤ D) :
    2 ≤ p * lateActivationRate K δ D *
        ((lateBranching K p δ D : ℝ) - 1) / 2 - 4 * Real.log 2 := by
  have hKr : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hW : 0 < δ + D := by linarith
  have hη : 0 < lateActivationRate K δ D :=
    lateActivationRate_pos K hK δ D hδ hD
  have hceil : 24 * (δ + D) / (p / (K : ℝ)) ≤
      (Nat.ceil (24 * (δ + D) / (p / (K : ℝ))) : ℝ) := by
    exact Nat.le_ceil _
  have hbranch : 24 * (K : ℝ) * (δ + D) / p ≤
      ((lateBranching K p δ D : ℕ) - 1 : ℝ) := by
    unfold lateBranching variableBranching at *
    push_cast
    have hpk : (p / (K : ℝ)) ≠ 0 := by positivity
    field_simp [hpk] at hceil ⊢
    nlinarith
  have hcoef : 0 ≤ p * lateActivationRate K δ D :=
    (mul_pos hp hη).le
  have hmul := mul_le_mul_of_nonneg_left hbranch hcoef
  have hprod : (12 : ℝ) ≤
      p * lateActivationRate K δ D *
        ((lateBranching K p δ D : ℝ) - 1) := by
    have heq : p * lateActivationRate K δ D *
        (24 * (K : ℝ) * (δ + D) / p) = 12 := by
      unfold lateActivationRate
      field_simp
      ring
    rw [heq] at hmul
    exact hmul
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

end ErdosSimilarityGrowingGaps
