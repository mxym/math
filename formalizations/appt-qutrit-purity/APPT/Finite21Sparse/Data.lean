import APPT.SparsePolynomialCubic
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

noncomputable def spectrum (g : Fin 21 → ℝ) : Fin 21 → ℝ :=
  ![((((g 0 + g 1) + (g 2 + (g 3 + g 4))) + ((g 5 + g 6) + (g 7 + (g 8 + g 9)))) + (((g 10 + g 11) + (g 12 + (g 13 + g 14))) + ((g 15 + (g 16 + g 17)) + (g 18 + (g 19 + g 20))))), ((((g 1 + g 2) + (g 3 + (g 4 + g 5))) + ((g 6 + g 7) + (g 8 + (g 9 + g 10)))) + (((g 11 + g 12) + (g 13 + (g 14 + g 15))) + ((g 16 + g 17) + (g 18 + (g 19 + g 20))))), ((((g 2 + g 3) + (g 4 + g 5)) + ((g 6 + g 7) + (g 8 + (g 9 + g 10)))) + (((g 11 + g 12) + (g 13 + (g 14 + g 15))) + ((g 16 + g 17) + (g 18 + (g 19 + g 20))))), ((((g 3 + g 4) + (g 5 + g 6)) + ((g 7 + g 8) + (g 9 + (g 10 + g 11)))) + (((g 12 + g 13) + (g 14 + g 15)) + ((g 16 + g 17) + (g 18 + (g 19 + g 20))))), ((((g 4 + g 5) + (g 6 + g 7)) + ((g 8 + g 9) + (g 10 + g 11))) + (((g 12 + g 13) + (g 14 + g 15)) + ((g 16 + g 17) + (g 18 + (g 19 + g 20))))), ((((g 5 + g 6) + (g 7 + g 8)) + ((g 9 + g 10) + (g 11 + g 12))) + (((g 13 + g 14) + (g 15 + g 16)) + ((g 17 + g 18) + (g 19 + g 20)))), (((g 6 + (g 7 + g 8)) + ((g 9 + g 10) + (g 11 + g 12))) + (((g 13 + g 14) + (g 15 + g 16)) + ((g 17 + g 18) + (g 19 + g 20)))), (((g 7 + (g 8 + g 9)) + ((g 10 + g 11) + (g 12 + g 13))) + ((g 14 + (g 15 + g 16)) + ((g 17 + g 18) + (g 19 + g 20)))), (((g 8 + (g 9 + g 10)) + (g 11 + (g 12 + g 13))) + ((g 14 + (g 15 + g 16)) + ((g 17 + g 18) + (g 19 + g 20)))), (((g 9 + (g 10 + g 11)) + (g 12 + (g 13 + g 14))) + ((g 15 + (g 16 + g 17)) + (g 18 + (g 19 + g 20)))), (((g 10 + g 11) + (g 12 + (g 13 + g 14))) + ((g 15 + (g 16 + g 17)) + (g 18 + (g 19 + g 20)))), (((g 11 + g 12) + (g 13 + (g 14 + g 15))) + ((g 16 + g 17) + (g 18 + (g 19 + g 20)))), (((g 12 + g 13) + (g 14 + g 15)) + ((g 16 + g 17) + (g 18 + (g 19 + g 20)))), (((g 13 + g 14) + (g 15 + g 16)) + ((g 17 + g 18) + (g 19 + g 20))), ((g 14 + (g 15 + g 16)) + ((g 17 + g 18) + (g 19 + g 20))), ((g 15 + (g 16 + g 17)) + (g 18 + (g 19 + g 20))), ((g 16 + g 17) + (g 18 + (g 19 + g 20))), ((g 17 + g 18) + (g 19 + g 20)), (g 18 + (g 19 + g 20)), (g 19 + g 20), g 20]
noncomputable def outer (g : Fin 21 → ℝ) : Fin 9 → ℝ :=
  ![spectrum g 0, spectrum g 1, spectrum g 2, spectrum g 15, spectrum g 16, spectrum g 17, spectrum g 18, spectrum g 19, spectrum g 20]
noncomputable def total (g : Fin 21 → ℝ) : ℝ := (∑ i, spectrum g i)
noncomputable def squareTotal (g : Fin 21 → ℝ) : ℝ := (∑ i, (spectrum g i)^2)

noncomputable def gapValues (g : Fin 21 → ℝ) (i : Nat) : ℝ :=
  if h : i < 21 then g ⟨i,h⟩ else 0

def polyY0 : SparsePolynomial.Poly := [([0], 1), ([1], 1), ([2], 1), ([3], 1), ([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1), ([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY0 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY0 = spectrum g 0 := by
  norm_num [polyY0, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY1 : SparsePolynomial.Poly := [([1], 1), ([2], 1), ([3], 1), ([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1), ([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY1 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY1 = spectrum g 1 := by
  norm_num [polyY1, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY2 : SparsePolynomial.Poly := [([2], 1), ([3], 1), ([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1), ([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY2 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY2 = spectrum g 2 := by
  norm_num [polyY2, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY3 : SparsePolynomial.Poly := [([3], 1), ([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1), ([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY3 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY3 = spectrum g 3 := by
  norm_num [polyY3, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY4 : SparsePolynomial.Poly := [([4], 1), ([5], 1), ([6], 1), ([7], 1), ([8], 1), ([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY4 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY4 = spectrum g 4 := by
  norm_num [polyY4, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY5 : SparsePolynomial.Poly := [([5], 1), ([6], 1), ([7], 1), ([8], 1), ([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY5 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY5 = spectrum g 5 := by
  norm_num [polyY5, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY6 : SparsePolynomial.Poly := [([6], 1), ([7], 1), ([8], 1), ([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY6 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY6 = spectrum g 6 := by
  norm_num [polyY6, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY7 : SparsePolynomial.Poly := [([7], 1), ([8], 1), ([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY7 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY7 = spectrum g 7 := by
  norm_num [polyY7, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY8 : SparsePolynomial.Poly := [([8], 1), ([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY8 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY8 = spectrum g 8 := by
  norm_num [polyY8, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY9 : SparsePolynomial.Poly := [([9], 1), ([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY9 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY9 = spectrum g 9 := by
  norm_num [polyY9, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY10 : SparsePolynomial.Poly := [([10], 1), ([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY10 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY10 = spectrum g 10 := by
  norm_num [polyY10, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY11 : SparsePolynomial.Poly := [([11], 1), ([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY11 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY11 = spectrum g 11 := by
  norm_num [polyY11, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY12 : SparsePolynomial.Poly := [([12], 1), ([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY12 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY12 = spectrum g 12 := by
  norm_num [polyY12, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY13 : SparsePolynomial.Poly := [([13], 1), ([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY13 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY13 = spectrum g 13 := by
  norm_num [polyY13, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY14 : SparsePolynomial.Poly := [([14], 1), ([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY14 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY14 = spectrum g 14 := by
  norm_num [polyY14, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY15 : SparsePolynomial.Poly := [([15], 1), ([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY15 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY15 = spectrum g 15 := by
  norm_num [polyY15, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY16 : SparsePolynomial.Poly := [([16], 1), ([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY16 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY16 = spectrum g 16 := by
  norm_num [polyY16, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY17 : SparsePolynomial.Poly := [([17], 1), ([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY17 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY17 = spectrum g 17 := by
  norm_num [polyY17, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY18 : SparsePolynomial.Poly := [([18], 1), ([19], 1), ([20], 1)]
theorem eval_polyY18 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY18 = spectrum g 18 := by
  norm_num [polyY18, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY19 : SparsePolynomial.Poly := [([19], 1), ([20], 1)]
theorem eval_polyY19 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY19 = spectrum g 19 := by
  norm_num [polyY19, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyY20 : SparsePolynomial.Poly := [([20], 1)]
theorem eval_polyY20 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyY20 = spectrum g 20 := by
  norm_num [polyY20, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def polyTotal : SparsePolynomial.Poly := [([0], 1), ([1], 2), ([2], 3), ([3], 4), ([4], 5), ([5], 6), ([6], 7), ([7], 8), ([8], 9), ([9], 10), ([10], 11), ([11], 12), ([12], 13), ([13], 14), ([14], 15), ([15], 16), ([16], 17), ([17], 18), ([18], 19), ([19], 20), ([20], 21)]
theorem eval_polyTotal (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) polyTotal = total g := by
  norm_num [polyTotal, total, Fin.sum_univ_succ, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum]
  <;> ring
def entryA00 : SparsePolynomial.Poly := [([20], 2)]
theorem eval_entryA00 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryA00 = matA (outer g) 0 0 := by
  norm_num [entryA00, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA01 : SparsePolynomial.Poly := [([0], -1), ([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1), ([16], -1), ([17], -1), ([18], -1)]
theorem eval_entryA01 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryA01 = matA (outer g) 0 1 := by
  norm_num [entryA01, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA02 : SparsePolynomial.Poly := [([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1), ([16], -1)]
theorem eval_entryA02 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryA02 = matA (outer g) 0 2 := by
  norm_num [entryA02, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA10 : SparsePolynomial.Poly := [([0], -1), ([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1), ([16], -1), ([17], -1), ([18], -1)]
theorem eval_entryA10 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryA10 = matA (outer g) 1 0 := by
  norm_num [entryA10, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA11 : SparsePolynomial.Poly := [([18], 2), ([19], 2), ([20], 2)]
theorem eval_entryA11 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryA11 = matA (outer g) 1 1 := by
  norm_num [entryA11, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA12 : SparsePolynomial.Poly := [([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1)]
theorem eval_entryA12 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryA12 = matA (outer g) 1 2 := by
  norm_num [entryA12, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA20 : SparsePolynomial.Poly := [([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1), ([16], -1)]
theorem eval_entryA20 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryA20 = matA (outer g) 2 0 := by
  norm_num [entryA20, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA21 : SparsePolynomial.Poly := [([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1)]
theorem eval_entryA21 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryA21 = matA (outer g) 2 1 := by
  norm_num [entryA21, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryA22 : SparsePolynomial.Poly := [([15], 2), ([16], 2), ([17], 2), ([18], 2), ([19], 2), ([20], 2)]
theorem eval_entryA22 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryA22 = matA (outer g) 2 2 := by
  norm_num [entryA22, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matA]
  <;> ring
def entryB00 : SparsePolynomial.Poly := [([20], 2)]
theorem eval_entryB00 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryB00 = matB (outer g) 0 0 := by
  norm_num [entryB00, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB01 : SparsePolynomial.Poly := [([0], -1), ([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1), ([16], -1), ([17], -1), ([18], -1)]
theorem eval_entryB01 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryB01 = matB (outer g) 0 1 := by
  norm_num [entryB01, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB02 : SparsePolynomial.Poly := [([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1), ([16], -1), ([17], -1)]
theorem eval_entryB02 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryB02 = matB (outer g) 0 2 := by
  norm_num [entryB02, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB10 : SparsePolynomial.Poly := [([0], -1), ([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1), ([16], -1), ([17], -1), ([18], -1)]
theorem eval_entryB10 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryB10 = matB (outer g) 1 0 := by
  norm_num [entryB10, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB11 : SparsePolynomial.Poly := [([17], 2), ([18], 2), ([19], 2), ([20], 2)]
theorem eval_entryB11 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryB11 = matB (outer g) 1 1 := by
  norm_num [entryB11, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB12 : SparsePolynomial.Poly := [([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1)]
theorem eval_entryB12 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryB12 = matB (outer g) 1 2 := by
  norm_num [entryB12, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB20 : SparsePolynomial.Poly := [([1], -1), ([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1), ([16], -1), ([17], -1)]
theorem eval_entryB20 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryB20 = matB (outer g) 2 0 := by
  norm_num [entryB20, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB21 : SparsePolynomial.Poly := [([2], -1), ([3], -1), ([4], -1), ([5], -1), ([6], -1), ([7], -1), ([8], -1), ([9], -1), ([10], -1), ([11], -1), ([12], -1), ([13], -1), ([14], -1), ([15], -1)]
theorem eval_entryB21 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryB21 = matB (outer g) 2 1 := by
  norm_num [entryB21, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring
def entryB22 : SparsePolynomial.Poly := [([15], 2), ([16], 2), ([17], 2), ([18], 2), ([19], 2), ([20], 2)]
theorem eval_entryB22 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) entryB22 = matB (outer g) 2 2 := by
  norm_num [entryB22, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, outer, matB]
  <;> ring

end APPT.Finite21
