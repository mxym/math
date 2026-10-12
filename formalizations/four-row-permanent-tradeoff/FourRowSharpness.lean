import FourRowInequality
open scoped BigOperators
namespace FourRowTradeoff
noncomputable section

def flatMatrix : Mat := fun _ _ => 1
def oddMatrix : Mat := !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1]

theorem flat_permanent : flatMatrix.permanent = 24 := by
  rw [permanent_laplace]
  norm_num [flatMatrix, symPair, Fin.sum_univ_succ, Fin.rev]
theorem flat_det : flatMatrix.det = 0 := by
  rw [det_laplace]
  norm_num [flatMatrix, altPair, shuffleSign, Fin.sum_univ_succ, Fin.rev]
theorem flat_rowProduct : rowProduct flatMatrix = 16 := by
  have hs : Real.sqrt (4 : ℝ) = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num), Real.sqrt_nonneg (4 : ℝ)]
  norm_num [rowProduct, rowNorm, rowSq, flatMatrix, Fin.sum_univ_succ, Fin.prod_univ_succ, hs]

theorem one_rowProduct : rowProduct (1 : Mat) = 1 := by
  have h : ∀ i : Fin 4, rowNorm ((1 : Mat) i) = 1 := by
    intro i
    fin_cases i <;> norm_num [rowNorm, rowSq, Matrix.one_apply, Fin.sum_univ_succ]
  simp [rowProduct, h]

theorem odd_permanent : oddMatrix.permanent = 1 := by
  rw [permanent_laplace]
  norm_num [oddMatrix, symPair, Fin.sum_univ_succ, Fin.rev]
theorem odd_det : oddMatrix.det = -1 := by
  rw [det_laplace]
  norm_num [oddMatrix, altPair, shuffleSign, Fin.sum_univ_succ, Fin.rev]
theorem odd_rowProduct : rowProduct oddMatrix = 1 := by
  norm_num [rowProduct, rowNorm, rowSq, oddMatrix, Fin.sum_univ_succ, Fin.prod_univ_succ]

/-- The universal real constant is admissible exactly when it is at least the sharp formula. -/
theorem matrix_bound_iff (c B : ℝ) (hc : 0 ≤ c) :
    (∀ A : Mat, ‖A.permanent‖+c*‖A.det‖ ≤ B*rowProduct A) ↔
      sharpConstant c ≤ B := by
  constructor
  · intro h
    have hf := h flatMatrix
    rw [flat_permanent, flat_det, flat_rowProduct] at hf
    norm_num at hf
    have hi := h (1 : Mat)
    simp only [Matrix.permanent_one, Matrix.det_one, norm_one, one_rowProduct,
      mul_one] at hi
    exact max_le (by linarith) hi
  · intro h A
    exact (matrix_tradeoff A c hc).trans (mul_le_mul_of_nonneg_right h (rowProduct_nonneg A))

theorem matrix_attainment (c : ℝ) :
    ∃ A : Mat, 0 < rowProduct A ∧
      ‖A.permanent‖+c*‖A.det‖ = sharpConstant c*rowProduct A := by
  by_cases h : 1+c ≤ 3/2
  · refine ⟨flatMatrix, ?_, ?_⟩
    · rw [flat_rowProduct]; norm_num
    · rw [flat_permanent, flat_det, flat_rowProduct, sharpConstant, max_eq_left h]
      norm_num
  · refine ⟨1, ?_, ?_⟩
    · rw [one_rowProduct]; norm_num
    · rw [Matrix.permanent_one, Matrix.det_one, one_rowProduct, sharpConstant,
        max_eq_right (by linarith : (3/2 : ℝ) ≤ 1+c)]
      simp

/-- The full real-parameter permanent/determinant pencil upper bound. -/
theorem pencil_bound (A : Mat) (t : ℝ) :
    ‖A.permanent+(t : ℂ)*A.det‖ ≤ sharpConstant |t| *rowProduct A := by
  calc
    _ ≤ ‖A.permanent‖+‖(t : ℂ)*A.det‖ := norm_add_le _ _
    _ = ‖A.permanent‖+|t| *‖A.det‖ := by simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := matrix_tradeoff A |t| (abs_nonneg t)

theorem flat_pencil (t : ℝ) : ‖flatMatrix.permanent+(t : ℂ)*flatMatrix.det‖ = 24 := by
  rw [flat_permanent, flat_det]
  norm_num

theorem one_pencil (t : ℝ) : ‖(1 : Mat).permanent+(t : ℂ)*(1 : Mat).det‖ = |1+t| := by
  rw [Matrix.permanent_one, Matrix.det_one, mul_one]
  have h : (1 : ℂ)+(t : ℂ) = ((1+t : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_real, Real.norm_eq_abs]

theorem odd_pencil (t : ℝ) : ‖oddMatrix.permanent+(t : ℂ)*oddMatrix.det‖ = |1-t| := by
  rw [odd_permanent, odd_det]
  have h : (1 : ℂ)+(t : ℂ)*(-1) = ((1-t : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- Corollary 2 as an exact universal norm, including both signs of the real parameter. -/
theorem pencil_bound_iff (t B : ℝ) :
    (∀ A : Mat, ‖A.permanent+(t : ℂ)*A.det‖ ≤ B*rowProduct A) ↔
      max (3/2) (1+|t|) ≤ B := by
  constructor
  · intro h
    have hf := h flatMatrix
    rw [flat_pencil, flat_rowProduct] at hf
    have hl : (3/2 : ℝ) ≤ B := by linarith
    apply max_le hl
    by_cases ht : 0 ≤ t
    · have hi := h (1 : Mat)
      rw [one_pencil, one_rowProduct, mul_one, abs_of_nonneg (by linarith : 0 ≤ 1+t)] at hi
      simpa only [abs_of_nonneg ht] using hi
    · have hi := h oddMatrix
      rw [odd_pencil, odd_rowProduct, mul_one, abs_of_nonneg (by linarith : 0 ≤ 1-t)] at hi
      simpa only [abs_of_nonpos (by linarith : t ≤ 0), sub_eq_add_neg] using hi
  · intro h A
    exact (pencil_bound A t).trans (mul_le_mul_of_nonneg_right h (rowProduct_nonneg A))

#print axioms matrix_bound_iff
#print axioms matrix_attainment
#print axioms pencil_bound_iff
end
end FourRowTradeoff
