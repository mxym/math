import Entry005.AnchorCoordinates
import Mathlib.Analysis.InnerProductSpace.Orientation

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

theorem euclidean_matrix_hadamard {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ j, ‖WithLp.toLp 2 (fun i => A i j)‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le v
  rw [b.toBasis.orientation.volumeForm_robust b rfl, Module.Basis.det_apply] at h
  have hm : b.toBasis.toMatrix v = A := by
    ext i j
    simp [Module.Basis.toMatrix_apply, b, v]
  simpa only [hm] using h

theorem lifted_unit_column_norm {d : ℕ} (x : Fin d → ℝ)
    (hx : ‖WithLp.toLp 2 x‖ ≤ 1) :
    ‖WithLp.toLp 2 (liftedCoordinates id x)‖ ≤ Real.sqrt 2 := by
  have hs : ‖WithLp.toLp 2 (liftedCoordinates id x)‖ ^ 2 =
      1 + ‖WithLp.toLp 2 x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, liftedCoordinates,
      Fin.cases_zero, Fin.cases_succ, id_eq, one_pow]
  apply (Real.le_sqrt (norm_nonneg _) (by norm_num)).2
  nlinarith [norm_nonneg (WithLp.toLp 2 x)]

theorem unit_ball_anchor_determinant {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Fin d → ℝ) (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1) :
    |(anchorMatrix w).det| ≤ (2 : ℝ) ^ d := by
  have hcol (j : Fin (d + 1)) :
      ‖WithLp.toLp 2 (fun i => anchorMatrix w i j)‖ ≤ Real.sqrt 2 := by
    have heq : (fun i => anchorMatrix w i j) = liftedCoordinates id (w j) := by
      ext i
      rw [anchor_matrix_entry]
      rfl
    rw [heq]
    exact lifted_unit_column_norm (w j) (hw j)
  calc
    |(anchorMatrix w).det| ≤ ∏ j, ‖WithLp.toLp 2 (fun i => anchorMatrix w i j)‖ :=
      euclidean_matrix_hadamard _
    _ ≤ ∏ _ : Fin (d + 1), Real.sqrt 2 := Finset.prod_le_prod₀
      (fun _ _ => norm_nonneg _) (fun j _ => hcol j)
    _ = (Real.sqrt 2) ^ (d + 1) := by simp
    _ ≤ (Real.sqrt 2) ^ (2 * d) := by
      apply pow_le_pow_right₀ (by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2])
      omega
    _ = (2 : ℝ) ^ d := by rw [pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem unit_ball_replacement_determinant {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Fin d → ℝ) (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (x : Fin d → ℝ) (hx : ‖WithLp.toLp 2 x‖ ≤ 1) (i : Fin (d + 1)) :
    |replacementDeterminant w x i| ≤ (2 : ℝ) ^ d := by
  have hm : anchorMatrix (Function.update w i x) =
      (anchorMatrix w).updateCol i (liftedCoordinates id x) := by
    ext k j
    by_cases h : j = i
    · subst j
      simp [anchor_matrix_entry, Matrix.updateCol, Function.update, liftedCoordinates]
    · simp [anchor_matrix_entry, Matrix.updateCol, Function.update, liftedCoordinates, h]
  have hu : ∀ j, ‖WithLp.toLp 2 (Function.update w i x j)‖ ≤ 1 := by
    intro j
    by_cases h : j = i
    · simpa [h] using hx
    · simpa [Function.update_of_ne h] using hw j
  have hbound := unit_ball_anchor_determinant hd (Function.update w i x) hu
  simpa only [hm, replacementDeterminant] using hbound

theorem unit_ball_anchor_coordinate_bound {d : ℕ} (hd : 1 ≤ d)
    (w : Fin (d + 1) → Fin d → ℝ) (hw : ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1)
    (hdet : (anchorMatrix w).det ≠ 0)
    (x : Fin d → ℝ) (hx : ‖WithLp.toLp 2 x‖ ≤ 1) (i : Fin (d + 1)) :
    |anchorCoordinates w x i| ≤ (2 : ℝ) ^ d / |(anchorMatrix w).det| := by
  have hbound := unit_ball_replacement_determinant hd w hw x hx i
  rw [replacement_determinant_coordinates w hdet, abs_mul] at hbound
  exact (le_div_iff₀ (abs_pos.mpr hdet)).2 (by simpa [mul_comm] using hbound)

end Entry005
