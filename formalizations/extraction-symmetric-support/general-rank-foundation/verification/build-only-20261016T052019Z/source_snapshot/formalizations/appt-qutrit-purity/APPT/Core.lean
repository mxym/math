import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open scoped BigOperators
namespace APPT

noncomputable def matA (y : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*y 8, y 7-y 0, y 5-y 1;
     y 7-y 0, 2*y 6, y 4-y 2;
     y 5-y 1, y 4-y 2, 2*y 3]
noncomputable def matB (y : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*y 8, y 7-y 0, y 6-y 1;
     y 7-y 0, 2*y 5, y 4-y 2;
     y 6-y 1, y 4-y 2, 2*y 3]
noncomputable def detA (y : Fin 9 → ℝ) : ℝ := (matA y).det
noncomputable def detB (y : Fin 9 → ℝ) : ℝ := (matB y).det
noncomputable def minorA (y : Fin 9 → ℝ) (i j : Fin 3) : ℝ :=
  matA y i i * matA y j j - matA y i j * matA y j i
noncomputable def minorB (y : Fin 9 → ℝ) (i j : Fin 3) : ℝ :=
  matB y i i * matB y j j - matB y i j * matB y j i
noncomputable def quadA (y : Fin 9 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  dotProduct v (Matrix.mulVec (matA y) v)
noncomputable def quadB (y : Fin 9 → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  dotProduct v (Matrix.mulVec (matB y) v)
noncomputable def ratio (y : Fin 9 → ℝ) : ℝ := 2*y 3-y 2

theorem detA_nonneg (y : Fin 9 → ℝ) (h : (matA y).PosSemidef) :
    0 ≤ detA y := h.det_nonneg
theorem detB_nonneg (y : Fin 9 → ℝ) (h : (matB y).PosSemidef) :
    0 ≤ detB y := h.det_nonneg

theorem minorA_nonneg (y : Fin 9 → ℝ) (h : (matA y).PosSemidef)
    (i j : Fin 3) : 0 ≤ minorA y i j := by
  have hsub := (h.submatrix (![i,j] : Fin 2 → Fin 3)).det_nonneg
  simpa [minorA, Matrix.det_fin_two, Matrix.submatrix] using hsub

theorem minorB_nonneg (y : Fin 9 → ℝ) (h : (matB y).PosSemidef)
    (i j : Fin 3) : 0 ≤ minorB y i j := by
  have hsub := (h.submatrix (![i,j] : Fin 2 → Fin 3)).det_nonneg
  simpa [minorB, Matrix.det_fin_two, Matrix.submatrix] using hsub

theorem quadA_nonneg (y : Fin 9 → ℝ) (h : (matA y).PosSemidef)
    (v : Fin 3 → ℝ) : 0 ≤ quadA y v := by
  simpa [quadA] using h.dotProduct_mulVec_nonneg v

theorem quadB_nonneg (y : Fin 9 → ℝ) (h : (matB y).PosSemidef)
    (v : Fin 3 → ℝ) : 0 ≤ quadB y v := by
  simpa [quadB] using h.dotProduct_mulVec_nonneg v

end APPT
