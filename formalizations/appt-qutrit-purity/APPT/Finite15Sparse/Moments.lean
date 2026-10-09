import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def square0 : SparsePolynomial.Poly := [([0,0], 1), ([0,1], 2), ([0,2], 2), ([0,3], 2), ([0,4], 2), ([0,5], 2), ([0,6], 2), ([0,7], 2), ([0,8], 2), ([0,9], 2), ([0,10], 2), ([0,11], 2), ([0,12], 2), ([0,13], 2), ([0,14], 2), ([1,1], 1), ([1,2], 2), ([1,3], 2), ([1,4], 2), ([1,5], 2), ([1,6], 2), ([1,7], 2), ([1,8], 2), ([1,9], 2), ([1,10], 2), ([1,11], 2), ([1,12], 2), ([1,13], 2), ([1,14], 2), ([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 2), ([2,8], 2), ([2,9], 2), ([2,10], 2), ([2,11], 2), ([2,12], 2), ([2,13], 2), ([2,14], 2), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([3,9], 2), ([3,10], 2), ([3,11], 2), ([3,12], 2), ([3,13], 2), ([3,14], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([4,9], 2), ([4,10], 2), ([4,11], 2), ([4,12], 2), ([4,13], 2), ([4,14], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([5,9], 2), ([5,10], 2), ([5,11], 2), ([5,12], 2), ([5,13], 2), ([5,14], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([6,10], 2), ([6,11], 2), ([6,12], 2), ([6,13], 2), ([6,14], 2), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 2), ([7,11], 2), ([7,12], 2), ([7,13], 2), ([7,14], 2), ([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([8,13], 2), ([8,14], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square0_data : square0 = SparsePolynomial.trim (SparsePolynomial.mul polyY0 polyY0) := by decide +kernel
theorem eval_square0 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square0 = (spectrum g 0)^2 := by
  rw [square0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY0]
  ring
def square1 : SparsePolynomial.Poly := [([1,1], 1), ([1,2], 2), ([1,3], 2), ([1,4], 2), ([1,5], 2), ([1,6], 2), ([1,7], 2), ([1,8], 2), ([1,9], 2), ([1,10], 2), ([1,11], 2), ([1,12], 2), ([1,13], 2), ([1,14], 2), ([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 2), ([2,8], 2), ([2,9], 2), ([2,10], 2), ([2,11], 2), ([2,12], 2), ([2,13], 2), ([2,14], 2), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([3,9], 2), ([3,10], 2), ([3,11], 2), ([3,12], 2), ([3,13], 2), ([3,14], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([4,9], 2), ([4,10], 2), ([4,11], 2), ([4,12], 2), ([4,13], 2), ([4,14], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([5,9], 2), ([5,10], 2), ([5,11], 2), ([5,12], 2), ([5,13], 2), ([5,14], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([6,10], 2), ([6,11], 2), ([6,12], 2), ([6,13], 2), ([6,14], 2), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 2), ([7,11], 2), ([7,12], 2), ([7,13], 2), ([7,14], 2), ([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([8,13], 2), ([8,14], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square1_data : square1 = SparsePolynomial.trim (SparsePolynomial.mul polyY1 polyY1) := by decide +kernel
theorem eval_square1 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square1 = (spectrum g 1)^2 := by
  rw [square1_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY1]
  ring
def square2 : SparsePolynomial.Poly := [([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 2), ([2,8], 2), ([2,9], 2), ([2,10], 2), ([2,11], 2), ([2,12], 2), ([2,13], 2), ([2,14], 2), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([3,9], 2), ([3,10], 2), ([3,11], 2), ([3,12], 2), ([3,13], 2), ([3,14], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([4,9], 2), ([4,10], 2), ([4,11], 2), ([4,12], 2), ([4,13], 2), ([4,14], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([5,9], 2), ([5,10], 2), ([5,11], 2), ([5,12], 2), ([5,13], 2), ([5,14], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([6,10], 2), ([6,11], 2), ([6,12], 2), ([6,13], 2), ([6,14], 2), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 2), ([7,11], 2), ([7,12], 2), ([7,13], 2), ([7,14], 2), ([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([8,13], 2), ([8,14], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square2_data : square2 = SparsePolynomial.trim (SparsePolynomial.mul polyY2 polyY2) := by decide +kernel
theorem eval_square2 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square2 = (spectrum g 2)^2 := by
  rw [square2_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY2]
  ring
def square3 : SparsePolynomial.Poly := [([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([3,9], 2), ([3,10], 2), ([3,11], 2), ([3,12], 2), ([3,13], 2), ([3,14], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([4,9], 2), ([4,10], 2), ([4,11], 2), ([4,12], 2), ([4,13], 2), ([4,14], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([5,9], 2), ([5,10], 2), ([5,11], 2), ([5,12], 2), ([5,13], 2), ([5,14], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([6,10], 2), ([6,11], 2), ([6,12], 2), ([6,13], 2), ([6,14], 2), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 2), ([7,11], 2), ([7,12], 2), ([7,13], 2), ([7,14], 2), ([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([8,13], 2), ([8,14], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square3_data : square3 = SparsePolynomial.trim (SparsePolynomial.mul polyY3 polyY3) := by decide +kernel
theorem eval_square3 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square3 = (spectrum g 3)^2 := by
  rw [square3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY3]
  ring
def square4 : SparsePolynomial.Poly := [([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([4,9], 2), ([4,10], 2), ([4,11], 2), ([4,12], 2), ([4,13], 2), ([4,14], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([5,9], 2), ([5,10], 2), ([5,11], 2), ([5,12], 2), ([5,13], 2), ([5,14], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([6,10], 2), ([6,11], 2), ([6,12], 2), ([6,13], 2), ([6,14], 2), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 2), ([7,11], 2), ([7,12], 2), ([7,13], 2), ([7,14], 2), ([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([8,13], 2), ([8,14], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square4_data : square4 = SparsePolynomial.trim (SparsePolynomial.mul polyY4 polyY4) := by decide +kernel
theorem eval_square4 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square4 = (spectrum g 4)^2 := by
  rw [square4_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY4]
  ring
def square5 : SparsePolynomial.Poly := [([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([5,9], 2), ([5,10], 2), ([5,11], 2), ([5,12], 2), ([5,13], 2), ([5,14], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([6,10], 2), ([6,11], 2), ([6,12], 2), ([6,13], 2), ([6,14], 2), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 2), ([7,11], 2), ([7,12], 2), ([7,13], 2), ([7,14], 2), ([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([8,13], 2), ([8,14], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square5_data : square5 = SparsePolynomial.trim (SparsePolynomial.mul polyY5 polyY5) := by decide +kernel
theorem eval_square5 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square5 = (spectrum g 5)^2 := by
  rw [square5_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY5]
  ring
def square6 : SparsePolynomial.Poly := [([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([6,10], 2), ([6,11], 2), ([6,12], 2), ([6,13], 2), ([6,14], 2), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 2), ([7,11], 2), ([7,12], 2), ([7,13], 2), ([7,14], 2), ([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([8,13], 2), ([8,14], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square6_data : square6 = SparsePolynomial.trim (SparsePolynomial.mul polyY6 polyY6) := by decide +kernel
theorem eval_square6 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square6 = (spectrum g 6)^2 := by
  rw [square6_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY6]
  ring
def square7 : SparsePolynomial.Poly := [([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 2), ([7,11], 2), ([7,12], 2), ([7,13], 2), ([7,14], 2), ([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([8,13], 2), ([8,14], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square7_data : square7 = SparsePolynomial.trim (SparsePolynomial.mul polyY7 polyY7) := by decide +kernel
theorem eval_square7 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square7 = (spectrum g 7)^2 := by
  rw [square7_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY7]
  ring
def square8 : SparsePolynomial.Poly := [([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([8,13], 2), ([8,14], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square8_data : square8 = SparsePolynomial.trim (SparsePolynomial.mul polyY8 polyY8) := by decide +kernel
theorem eval_square8 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square8 = (spectrum g 8)^2 := by
  rw [square8_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY8]
  ring
def square9 : SparsePolynomial.Poly := [([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([9,13], 2), ([9,14], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square9_data : square9 = SparsePolynomial.trim (SparsePolynomial.mul polyY9 polyY9) := by decide +kernel
theorem eval_square9 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square9 = (spectrum g 9)^2 := by
  rw [square9_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY9]
  ring
def square10 : SparsePolynomial.Poly := [([10,10], 1), ([10,11], 2), ([10,12], 2), ([10,13], 2), ([10,14], 2), ([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square10_data : square10 = SparsePolynomial.trim (SparsePolynomial.mul polyY10 polyY10) := by decide +kernel
theorem eval_square10 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square10 = (spectrum g 10)^2 := by
  rw [square10_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY10]
  ring
def square11 : SparsePolynomial.Poly := [([11,11], 1), ([11,12], 2), ([11,13], 2), ([11,14], 2), ([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square11_data : square11 = SparsePolynomial.trim (SparsePolynomial.mul polyY11 polyY11) := by decide +kernel
theorem eval_square11 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square11 = (spectrum g 11)^2 := by
  rw [square11_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY11]
  ring
def square12 : SparsePolynomial.Poly := [([12,12], 1), ([12,13], 2), ([12,14], 2), ([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square12_data : square12 = SparsePolynomial.trim (SparsePolynomial.mul polyY12 polyY12) := by decide +kernel
theorem eval_square12 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square12 = (spectrum g 12)^2 := by
  rw [square12_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY12]
  ring
def square13 : SparsePolynomial.Poly := [([13,13], 1), ([13,14], 2), ([14,14], 1)]
theorem square13_data : square13 = SparsePolynomial.trim (SparsePolynomial.mul polyY13 polyY13) := by decide +kernel
theorem eval_square13 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square13 = (spectrum g 13)^2 := by
  rw [square13_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY13]
  ring
def square14 : SparsePolynomial.Poly := [([14,14], 1)]
theorem square14_data : square14 = SparsePolynomial.trim (SparsePolynomial.mul polyY14 polyY14) := by decide +kernel
theorem eval_square14 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) square14 = (spectrum g 14)^2 := by
  rw [square14_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_polyY14]
  ring
def polySquares : SparsePolynomial.Poly := [([0,0], 1), ([0,1], 2), ([0,2], 2), ([0,3], 2), ([0,4], 2), ([0,5], 2), ([0,6], 2), ([0,7], 2), ([0,8], 2), ([0,9], 2), ([0,10], 2), ([0,11], 2), ([0,12], 2), ([0,13], 2), ([0,14], 2), ([1,1], 2), ([1,2], 4), ([1,3], 4), ([1,4], 4), ([1,5], 4), ([1,6], 4), ([1,7], 4), ([1,8], 4), ([1,9], 4), ([1,10], 4), ([1,11], 4), ([1,12], 4), ([1,13], 4), ([1,14], 4), ([2,2], 3), ([2,3], 6), ([2,4], 6), ([2,5], 6), ([2,6], 6), ([2,7], 6), ([2,8], 6), ([2,9], 6), ([2,10], 6), ([2,11], 6), ([2,12], 6), ([2,13], 6), ([2,14], 6), ([3,3], 4), ([3,4], 8), ([3,5], 8), ([3,6], 8), ([3,7], 8), ([3,8], 8), ([3,9], 8), ([3,10], 8), ([3,11], 8), ([3,12], 8), ([3,13], 8), ([3,14], 8), ([4,4], 5), ([4,5], 10), ([4,6], 10), ([4,7], 10), ([4,8], 10), ([4,9], 10), ([4,10], 10), ([4,11], 10), ([4,12], 10), ([4,13], 10), ([4,14], 10), ([5,5], 6), ([5,6], 12), ([5,7], 12), ([5,8], 12), ([5,9], 12), ([5,10], 12), ([5,11], 12), ([5,12], 12), ([5,13], 12), ([5,14], 12), ([6,6], 7), ([6,7], 14), ([6,8], 14), ([6,9], 14), ([6,10], 14), ([6,11], 14), ([6,12], 14), ([6,13], 14), ([6,14], 14), ([7,7], 8), ([7,8], 16), ([7,9], 16), ([7,10], 16), ([7,11], 16), ([7,12], 16), ([7,13], 16), ([7,14], 16), ([8,8], 9), ([8,9], 18), ([8,10], 18), ([8,11], 18), ([8,12], 18), ([8,13], 18), ([8,14], 18), ([9,9], 10), ([9,10], 20), ([9,11], 20), ([9,12], 20), ([9,13], 20), ([9,14], 20), ([10,10], 11), ([10,11], 22), ([10,12], 22), ([10,13], 22), ([10,14], 22), ([11,11], 12), ([11,12], 24), ([11,13], 24), ([11,14], 24), ([12,12], 13), ([12,13], 26), ([12,14], 26), ([13,13], 14), ([13,14], 28), ([14,14], 15)]
theorem polySquares_data : polySquares = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge square0 (SparsePolynomial.merge square1 square2)) (SparsePolynomial.merge (SparsePolynomial.merge square3 square4) (SparsePolynomial.merge square5 square6))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge square7 square8) (SparsePolynomial.merge square9 square10)) (SparsePolynomial.merge (SparsePolynomial.merge square11 square12) (SparsePolynomial.merge square13 square14)))) := by decide +kernel
theorem eval_polySquares (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) polySquares = squareTotal g := by
  rw [polySquares_data, SparsePolynomial.eval_trim]
  simp only [SparsePolynomial.eval_merge, eval_square0, eval_square1, eval_square2, eval_square3, eval_square4, eval_square5, eval_square6, eval_square7, eval_square8, eval_square9, eval_square10, eval_square11, eval_square12, eval_square13, eval_square14]
  simp [squareTotal, Fin.sum_univ_succ]
  <;> ring

end APPT.Finite15
