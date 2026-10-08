import GaussianParallelBoundary

/-! The normal-offset sets are exactly the closed-ball erosions of the
original open cell. Thus the boundary-mass derivative concerns actual
geometric distance, not just an auxiliary family of prices. -/
open MeasureTheory ProbabilityTheory Set Module
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem simplicialInset_eq_closedBall_erosion
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hn : ∀ i : Fin (d+1), v 0 - v i.succ ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    simplicialInset v b t =
      {x | ∀ y : Space (d+1), dist y x ≤ t → y ∈ winningCell v b 0} := by
  ext x
  constructor
  · intro hx y hy j hj
    cases j using Fin.cases with
    | zero => exact (hj rfl).elim
    | succ i =>
      have hi := hx i
      have hy' : ‖x-y‖ ≤ t := by simpa [dist_eq_norm,norm_sub_rev] using hy
      have hb := (real_inner_le_norm (v 0 - v i.succ) (x-y)).trans
        (mul_le_mul_of_nonneg_left hy' (norm_nonneg _))
      simp only [inner_sub_left,inner_sub_right] at hi hb
      linarith
  · intro hx i
    let a := v 0 - v i.succ
    let y := x - (t / ‖a‖) • a
    have ha : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr (hn i)
    have hpos : 0 < ‖a‖ := norm_pos_iff.mpr (hn i)
    have hdist : dist y x ≤ t := by
      rw [dist_eq_norm]
      have he : y-x = -((t/‖a‖) • a) := by dsimp [y]; abel
      rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg ht hpos.le)]
      exact le_of_eq (div_mul_cancel₀ t ha)
    have hwin := hx y hdist i.succ (Fin.succ_ne_zero i)
    have he : ⟪a,y⟫ = ⟪a,x⟫ - t * ‖a‖ := by
      dsimp [y]
      rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
      field_simp
    have hi : 0 < ⟪a,y⟫ - (b 0 - b i.succ) := by
      dsimp [a]
      rw [inner_sub_left]
      linarith
    rw [he] at hi
    exact (by dsimp [a] at hi; linarith : t * ‖v 0 - v i.succ‖ <
      ⟪v 0 - v i.succ,x⟫ - (b 0 - b i.succ))

end GaussianMeasureBridge
