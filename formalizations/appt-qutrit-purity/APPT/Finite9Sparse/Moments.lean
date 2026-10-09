import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def square0 : SparsePolynomial.Poly := [([0,0], 1), ([0,1], 2), ([0,2], 2), ([0,3], 2), ([0,4], 2), ([0,5], 2), ([0,6], 2), ([0,7], 2), ([0,8], 2), ([1,1], 1), ([1,2], 2), ([1,3], 2), ([1,4], 2), ([1,5], 2), ([1,6], 2), ([1,7], 2), ([1,8], 2), ([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 2), ([2,8], 2), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([7,7], 1), ([7,8], 2), ([8,8], 1)]
theorem square0_data : square0 = SparsePolynomial.trim (SparsePolynomial.mul polyY0 polyY0) := by decide +kernel
theorem eval_square0 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) square0 = (spectrum g 0)^2 := by
  rw [square0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY0]
  ring
def square1 : SparsePolynomial.Poly := [([1,1], 1), ([1,2], 2), ([1,3], 2), ([1,4], 2), ([1,5], 2), ([1,6], 2), ([1,7], 2), ([1,8], 2), ([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 2), ([2,8], 2), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([7,7], 1), ([7,8], 2), ([8,8], 1)]
theorem square1_data : square1 = SparsePolynomial.trim (SparsePolynomial.mul polyY1 polyY1) := by decide +kernel
theorem eval_square1 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) square1 = (spectrum g 1)^2 := by
  rw [square1_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY1]
  ring
def square2 : SparsePolynomial.Poly := [([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 2), ([2,8], 2), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([7,7], 1), ([7,8], 2), ([8,8], 1)]
theorem square2_data : square2 = SparsePolynomial.trim (SparsePolynomial.mul polyY2 polyY2) := by decide +kernel
theorem eval_square2 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) square2 = (spectrum g 2)^2 := by
  rw [square2_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY2]
  ring
def square3 : SparsePolynomial.Poly := [([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([7,7], 1), ([7,8], 2), ([8,8], 1)]
theorem square3_data : square3 = SparsePolynomial.trim (SparsePolynomial.mul polyY3 polyY3) := by decide +kernel
theorem eval_square3 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) square3 = (spectrum g 3)^2 := by
  rw [square3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY3]
  ring
def square4 : SparsePolynomial.Poly := [([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([7,7], 1), ([7,8], 2), ([8,8], 1)]
theorem square4_data : square4 = SparsePolynomial.trim (SparsePolynomial.mul polyY4 polyY4) := by decide +kernel
theorem eval_square4 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) square4 = (spectrum g 4)^2 := by
  rw [square4_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY4]
  ring
def square5 : SparsePolynomial.Poly := [([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([7,7], 1), ([7,8], 2), ([8,8], 1)]
theorem square5_data : square5 = SparsePolynomial.trim (SparsePolynomial.mul polyY5 polyY5) := by decide +kernel
theorem eval_square5 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) square5 = (spectrum g 5)^2 := by
  rw [square5_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY5]
  ring
def square6 : SparsePolynomial.Poly := [([6,6], 1), ([6,7], 2), ([6,8], 2), ([7,7], 1), ([7,8], 2), ([8,8], 1)]
theorem square6_data : square6 = SparsePolynomial.trim (SparsePolynomial.mul polyY6 polyY6) := by decide +kernel
theorem eval_square6 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) square6 = (spectrum g 6)^2 := by
  rw [square6_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY6]
  ring
def square7 : SparsePolynomial.Poly := [([7,7], 1), ([7,8], 2), ([8,8], 1)]
theorem square7_data : square7 = SparsePolynomial.trim (SparsePolynomial.mul polyY7 polyY7) := by decide +kernel
theorem eval_square7 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) square7 = (spectrum g 7)^2 := by
  rw [square7_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY7]
  ring
def square8 : SparsePolynomial.Poly := [([8,8], 1)]
theorem square8_data : square8 = SparsePolynomial.trim (SparsePolynomial.mul polyY8 polyY8) := by decide +kernel
theorem eval_square8 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) square8 = (spectrum g 8)^2 := by
  rw [square8_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY8]
  ring
def polySquares : SparsePolynomial.Poly := [([0,0], 1), ([0,1], 2), ([0,2], 2), ([0,3], 2), ([0,4], 2), ([0,5], 2), ([0,6], 2), ([0,7], 2), ([0,8], 2), ([1,1], 2), ([1,2], 4), ([1,3], 4), ([1,4], 4), ([1,5], 4), ([1,6], 4), ([1,7], 4), ([1,8], 4), ([2,2], 3), ([2,3], 6), ([2,4], 6), ([2,5], 6), ([2,6], 6), ([2,7], 6), ([2,8], 6), ([3,3], 4), ([3,4], 8), ([3,5], 8), ([3,6], 8), ([3,7], 8), ([3,8], 8), ([4,4], 5), ([4,5], 10), ([4,6], 10), ([4,7], 10), ([4,8], 10), ([5,5], 6), ([5,6], 12), ([5,7], 12), ([5,8], 12), ([6,6], 7), ([6,7], 14), ([6,8], 14), ([7,7], 8), ([7,8], 16), ([8,8], 9)]
theorem polySquares_data : polySquares = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge square0 square1) (SparsePolynomial.merge square2 square3)) (SparsePolynomial.merge (SparsePolynomial.merge square4 square5) (SparsePolynomial.merge square6 (SparsePolynomial.merge square7 square8)))) := by decide +kernel
theorem eval_polySquares (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) polySquares = squareTotal g := by
  rw [polySquares_data, SparsePolynomial.eval_trim]
  simp only [SparsePolynomial.eval_merge, eval_square0, eval_square1, eval_square2, eval_square3, eval_square4, eval_square5, eval_square6, eval_square7, eval_square8]
  simp [squareTotal, Fin.sum_univ_succ]
  <;> ring

end APPT.Finite9
