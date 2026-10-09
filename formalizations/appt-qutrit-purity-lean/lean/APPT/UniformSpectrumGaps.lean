import APPT.UniformDefs

open scoped BigOperators
namespace APPT

noncomputable def gaps9 (y : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![y 0-y 1, y 1-y 2, y 2-y 3, y 3-y 4, y 4-y 5,
    y 5-y 6, y 6-y 7, y 7-y 8, y 8]

theorem gaps9_nonneg (y : Fin 9 → ℝ) (hy : Antitone y)
    (hn : ∀ i, 0 ≤ y i) : ∀ i, 0 ≤ gaps9 y i := by
  intro i
  fin_cases i <;> simp only [gaps9, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals first | exact hn _ | exact sub_nonneg.mpr (hy (by decide))

theorem spectrum_gaps9 (y : Fin 9 → ℝ) : Uniform.spectrum (gaps9 y) = y := by
  funext i
  fin_cases i <;> simp [Uniform.spectrum, gaps9] <;> ring

theorem outer_gaps9 (y : Fin 9 → ℝ) : Uniform.outer (gaps9 y) = y := by
  funext i
  fin_cases i <;> simp [Uniform.outer, spectrum_gaps9]

end APPT
