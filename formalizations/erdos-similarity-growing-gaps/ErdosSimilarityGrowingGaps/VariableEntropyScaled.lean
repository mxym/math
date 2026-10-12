import ErdosSimilarityGrowingGaps.RoutingEntropy

namespace ErdosSimilarityGrowingGaps

/-! The scaled candidate envelope has a corresponding entropy estimate.  It
is deliberately separate from `signature_entropy_position_bound`, whose
legacy candidate hypothesis carries only one factor of the branching. -/
theorem signature_entropy_position_bound_scaled
    (M P U T ell L : ℕ) (k lam : ℝ)
    (hM : 1 ≤ M) (hT : T ≤ U) (hk : |k| ≤ U)
    (hP : (P : ℝ) ≤ (M : ℝ) ^ 2 * ((U : ℝ) + T + |k| + 2))
    (hL : L ≤ ell) (hκ : 0 < lam - 4 * Real.log 2) :
    (20 * ((P : ℝ) * (3 + (2 : ℝ) ^ (2 * ell + 3)) + 5) ^ 2) *
      Real.exp (-lam * (ell : ℝ)) ≤
    46080 * (M : ℝ) ^ 4 * ((U : ℝ) + 1) ^ 2 *
      Real.exp (-(lam - 4 * Real.log 2) * (L : ℝ)) := by
  have hM' : 1 ≤ M ^ 2 := Nat.one_le_pow 2 M (by omega)
  have hP' : (P : ℝ) ≤ ((M ^ 2 : ℕ) : ℝ) *
      ((U : ℝ) + T + |k| + 2) := by
    simpa only [Nat.cast_pow] using hP
  have h := signature_entropy_position_bound (M ^ 2) P U T ell L k lam
    hM' hT hk hP' hL hκ
  have hpow : (M : ℝ) ^ 4 = ((M : ℝ) ^ 2) ^ 2 := by ring
  rw [hpow]
  simpa only [Nat.cast_pow] using h

end ErdosSimilarityGrowingGaps
