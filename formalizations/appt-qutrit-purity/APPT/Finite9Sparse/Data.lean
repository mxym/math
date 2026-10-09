import APPT.SparsePolynomialCubic
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

noncomputable def spectrum (g : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![(((g 0 + g 1) + (g 2 + g 3)) + ((g 4 + g 5) + (g 6 + (g 7 + g 8)))), (((g 1 + g 2) + (g 3 + g 4)) + ((g 5 + g 6) + (g 7 + g 8))), ((g 2 + (g 3 + g 4)) + ((g 5 + g 6) + (g 7 + g 8))), ((g 3 + (g 4 + g 5)) + (g 6 + (g 7 + g 8))), ((g 4 + g 5) + (g 6 + (g 7 + g 8))), ((g 5 + g 6) + (g 7 + g 8)), (g 6 + (g 7 + g 8)), (g 7 + g 8), g 8]
noncomputable def outer (g : Fin 9 → ℝ) : Fin 9 → ℝ :=
  ![spectrum g 0, spectrum g 1, spectrum g 2, spectrum g 3, spectrum g 4, spectrum g 5, spectrum g 6, spectrum g 7, spectrum g 8]
noncomputable def total (g : Fin 9 → ℝ) : ℝ := (∑ i, spectrum g i)
noncomputable def squareTotal (g : Fin 9 → ℝ) : ℝ := (∑ i, (spectrum g i)^2)

noncomputable def gapValues (g : Fin 9 → ℝ) (i : Nat) : ℝ :=
  if h : i < 9 then g ⟨i,h⟩ else 0

def polyY0 : SparsePolynomial.Poly := [([0], 1), ([1], 1), ([2], 1), ([3], 1), ([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1)]
theorem eval_polyY0 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyY0 = spectrum g 0 := by
  norm_num [polyY0, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY1 : SparsePolynomial.Poly := [([1], 1), ([2], 1), ([3], 1), ([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1)]
theorem eval_polyY1 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyY1 = spectrum g 1 := by
  norm_num [polyY1, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY2 : SparsePolynomial.Poly := [([2], 1), ([3], 1), ([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1)]
theorem eval_polyY2 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyY2 = spectrum g 2 := by
  norm_num [polyY2, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY3 : SparsePolynomial.Poly := [([3], 1), ([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1)]
theorem eval_polyY3 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyY3 = spectrum g 3 := by
  norm_num [polyY3, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY4 : SparsePolynomial.Poly := [([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1)]
theorem eval_polyY4 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyY4 = spectrum g 4 := by
  norm_num [polyY4, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY5 : SparsePolynomial.Poly := [([5], 1), ([6], 1), ([7], 1), ([8], 1)]
theorem eval_polyY5 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyY5 = spectrum g 5 := by
  norm_num [polyY5, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY6 : SparsePolynomial.Poly := [([6], 1), ([7], 1), ([8], 1)]
theorem eval_polyY6 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyY6 = spectrum g 6 := by
  norm_num [polyY6, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY7 : SparsePolynomial.Poly := [([7], 1), ([8], 1)]
theorem eval_polyY7 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyY7 = spectrum g 7 := by
  norm_num [polyY7, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY8 : SparsePolynomial.Poly := [([8], 1)]
theorem eval_polyY8 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyY8 = spectrum g 8 := by
  norm_num [polyY8, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyTotal : SparsePolynomial.Poly := [([0], 1), ([1], 2), ([2], 3), ([3], 4), ([4], 5), ([5], 6), ([6], 7), ([7], 8), ([8], 9)]
theorem eval_polyTotal (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) polyTotal = total g := by
  norm_num [polyTotal, total, Fin.sum_univ_succ, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def entryA00 : SparsePolynomial.Poly := [([8], 2)]
theorem eval_entryA00 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryA00 = matA (outer g) 0 0 := by
  norm_num [entryA00, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA01 : SparsePolynomial.Poly := [([0], -1), ([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1)]
theorem eval_entryA01 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryA01 = matA (outer g) 0 1 := by
  norm_num [entryA01, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA02 : SparsePolynomial.Poly := [([1], -1), ([2], -1), ([3], -1), ([4], -1)]
theorem eval_entryA02 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryA02 = matA (outer g) 0 2 := by
  norm_num [entryA02, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA10 : SparsePolynomial.Poly := [([0], -1), ([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1)]
theorem eval_entryA10 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryA10 = matA (outer g) 1 0 := by
  norm_num [entryA10, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA11 : SparsePolynomial.Poly := [([6], 2), ([7], 2), ([8], 2)]
theorem eval_entryA11 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryA11 = matA (outer g) 1 1 := by
  norm_num [entryA11, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA12 : SparsePolynomial.Poly := [([2], -1), ([3], -1)]
theorem eval_entryA12 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryA12 = matA (outer g) 1 2 := by
  norm_num [entryA12, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA20 : SparsePolynomial.Poly := [([1], -1), ([2], -1), ([3], -1), ([4], -1)]
theorem eval_entryA20 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryA20 = matA (outer g) 2 0 := by
  norm_num [entryA20, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA21 : SparsePolynomial.Poly := [([2], -1), ([3], -1)]
theorem eval_entryA21 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryA21 = matA (outer g) 2 1 := by
  norm_num [entryA21, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA22 : SparsePolynomial.Poly := [([3], 2), ([4], 2), ([5], 2), ([6], 2), ([7], 2), ([8], 2)]
theorem eval_entryA22 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryA22 = matA (outer g) 2 2 := by
  norm_num [entryA22, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryB00 : SparsePolynomial.Poly := [([8], 2)]
theorem eval_entryB00 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryB00 = matB (outer g) 0 0 := by
  norm_num [entryB00, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB01 : SparsePolynomial.Poly := [([0], -1), ([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1)]
theorem eval_entryB01 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryB01 = matB (outer g) 0 1 := by
  norm_num [entryB01, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB02 : SparsePolynomial.Poly := [([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1)]
theorem eval_entryB02 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryB02 = matB (outer g) 0 2 := by
  norm_num [entryB02, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB10 : SparsePolynomial.Poly := [([0], -1), ([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1)]
theorem eval_entryB10 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryB10 = matB (outer g) 1 0 := by
  norm_num [entryB10, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB11 : SparsePolynomial.Poly := [([5], 2), ([6], 2), ([7], 2), ([8], 2)]
theorem eval_entryB11 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryB11 = matB (outer g) 1 1 := by
  norm_num [entryB11, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB12 : SparsePolynomial.Poly := [([2], -1), ([3], -1)]
theorem eval_entryB12 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryB12 = matB (outer g) 1 2 := by
  norm_num [entryB12, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB20 : SparsePolynomial.Poly := [([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1)]
theorem eval_entryB20 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryB20 = matB (outer g) 2 0 := by
  norm_num [entryB20, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB21 : SparsePolynomial.Poly := [([2], -1), ([3], -1)]
theorem eval_entryB21 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryB21 = matB (outer g) 2 1 := by
  norm_num [entryB21, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB22 : SparsePolynomial.Poly := [([3], 2), ([4], 2), ([5], 2), ([6], 2), ([7], 2), ([8], 2)]
theorem eval_entryB22 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) entryB22 = matB (outer g) 2 2 := by
  norm_num [entryB22, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring

end APPT.Finite9
