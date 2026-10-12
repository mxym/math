import QPermanentDefs

namespace QPermanentHalfline
open Matrix

theorem counterexampleMatrix_isHermitian : counterexampleMatrix.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [counterexampleMatrix, rationalMatrix, Matrix.conjTranspose_apply]

/-- Exact completed-square identity for the real quadratic form. -/
theorem counterexampleMatrix_quadratic_form (x : Fin 4 → ℝ) :
    star x ⬝ᵥ (counterexampleMatrix *ᵥ x) =
      (x 0 - (99/100) * x 1 + (1/500) * x 3)^2 +
      (199/10000) * (x 1 + (6349/995) * x 3)^2 +
      (x 2)^2 + (944/4975) * (x 3)^2 := by
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    counterexampleMatrix, rationalMatrix]
  ring

theorem counterexampleMatrix_posDef : counterexampleMatrix.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos counterexampleMatrix_isHermitian
  intro x hx
  rw [counterexampleMatrix_quadratic_form]
  by_contra! h
  have h0 := sq_nonneg (x 0 - (99/100) * x 1 + (1/500) * x 3)
  have h1 := sq_nonneg (x 1 + (6349/995) * x 3)
  have h2 := sq_nonneg (x 2)
  have h3 := sq_nonneg (x 3)
  have hx3sq : (x 3)^2 = 0 := by nlinarith only [h, h0, h1, h2, h3]
  have hx3 : x 3 = 0 := sq_eq_zero_iff.mp hx3sq
  have hx2sq : (x 2)^2 = 0 := by nlinarith only [h, h0, h1, h2, h3]
  have hx2 : x 2 = 0 := sq_eq_zero_iff.mp hx2sq
  have hx1sq : (x 1 + (6349/995) * x 3)^2 = 0 := by
    nlinarith only [h, h0, h1, h2, h3]
  have hx1 : x 1 = 0 := by simpa [hx3] using sq_eq_zero_iff.mp hx1sq
  have hx0sq : (x 0 - (99/100) * x 1 + (1/500) * x 3)^2 = 0 := by
    nlinarith only [h, h0, h1, h2, h3]
  have hx0 : x 0 = 0 := by simpa [hx3, hx1] using sq_eq_zero_iff.mp hx0sq
  apply hx
  funext i
  fin_cases i <;> assumption

theorem counterexampleMatrix_not_diagonal :
    ¬ ∃ d : Fin 4 → ℝ, counterexampleMatrix = Matrix.diagonal d := by
  rintro ⟨d, hd⟩
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) hd
  norm_num [counterexampleMatrix, rationalMatrix, Matrix.diagonal] at h

end QPermanentHalfline
