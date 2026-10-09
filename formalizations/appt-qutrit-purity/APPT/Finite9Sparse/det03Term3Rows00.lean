import APPT.Finite9Sparse.Det03Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term3Row00 : CoefficientMerge.Poly := [(nat_lit 95, Int.ofNat (nat_lit 2)), (nat_lit 96, Int.ofNat (nat_lit 2)), (nat_lit 97, Int.ofNat (nat_lit 2)), (nat_lit 98, Int.ofNat (nat_lit 2)), (nat_lit 104, Int.ofNat (nat_lit 2)), (nat_lit 105, Int.ofNat (nat_lit 2)), (nat_lit 106, Int.ofNat (nat_lit 2)), (nat_lit 107, Int.ofNat (nat_lit 2)), (nat_lit 113, Int.ofNat (nat_lit 2)), (nat_lit 114, Int.ofNat (nat_lit 2)), (nat_lit 115, Int.ofNat (nat_lit 2)), (nat_lit 116, Int.ofNat (nat_lit 2)), (nat_lit 122, Int.ofNat (nat_lit 2)), (nat_lit 123, Int.ofNat (nat_lit 2)), (nat_lit 124, Int.ofNat (nat_lit 2)), (nat_lit 125, Int.ofNat (nat_lit 2)), (nat_lit 131, Int.ofNat (nat_lit 2)), (nat_lit 132, Int.ofNat (nat_lit 2)), (nat_lit 133, Int.ofNat (nat_lit 2)), (nat_lit 134, Int.ofNat (nat_lit 2))]
theorem det03Term3Row00_decode : SparsePolynomial.decodeCubic 9 det03Term3Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term3Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row01 : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 2)), (nat_lit 105, Int.ofNat (nat_lit 2)), (nat_lit 106, Int.ofNat (nat_lit 2)), (nat_lit 107, Int.ofNat (nat_lit 2)), (nat_lit 185, Int.ofNat (nat_lit 2)), (nat_lit 186, Int.ofNat (nat_lit 2)), (nat_lit 187, Int.ofNat (nat_lit 2)), (nat_lit 188, Int.ofNat (nat_lit 2)), (nat_lit 194, Int.ofNat (nat_lit 2)), (nat_lit 195, Int.ofNat (nat_lit 2)), (nat_lit 196, Int.ofNat (nat_lit 2)), (nat_lit 197, Int.ofNat (nat_lit 2)), (nat_lit 203, Int.ofNat (nat_lit 2)), (nat_lit 204, Int.ofNat (nat_lit 2)), (nat_lit 205, Int.ofNat (nat_lit 2)), (nat_lit 206, Int.ofNat (nat_lit 2)), (nat_lit 212, Int.ofNat (nat_lit 2)), (nat_lit 213, Int.ofNat (nat_lit 2)), (nat_lit 214, Int.ofNat (nat_lit 2)), (nat_lit 215, Int.ofNat (nat_lit 2))]
theorem det03Term3Row01_decode : SparsePolynomial.decodeCubic 9 det03Term3Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row01 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term3Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row02 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 2)), (nat_lit 114, Int.ofNat (nat_lit 2)), (nat_lit 115, Int.ofNat (nat_lit 2)), (nat_lit 116, Int.ofNat (nat_lit 2)), (nat_lit 194, Int.ofNat (nat_lit 2)), (nat_lit 195, Int.ofNat (nat_lit 2)), (nat_lit 196, Int.ofNat (nat_lit 2)), (nat_lit 197, Int.ofNat (nat_lit 2)), (nat_lit 275, Int.ofNat (nat_lit 2)), (nat_lit 276, Int.ofNat (nat_lit 2)), (nat_lit 277, Int.ofNat (nat_lit 2)), (nat_lit 278, Int.ofNat (nat_lit 2)), (nat_lit 284, Int.ofNat (nat_lit 2)), (nat_lit 285, Int.ofNat (nat_lit 2)), (nat_lit 286, Int.ofNat (nat_lit 2)), (nat_lit 287, Int.ofNat (nat_lit 2)), (nat_lit 293, Int.ofNat (nat_lit 2)), (nat_lit 294, Int.ofNat (nat_lit 2)), (nat_lit 295, Int.ofNat (nat_lit 2)), (nat_lit 296, Int.ofNat (nat_lit 2))]
theorem det03Term3Row02_decode : SparsePolynomial.decodeCubic 9 det03Term3Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row02 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term3Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row03 : CoefficientMerge.Poly := [(nat_lit 122, Int.ofNat (nat_lit 2)), (nat_lit 123, Int.ofNat (nat_lit 2)), (nat_lit 124, Int.ofNat (nat_lit 2)), (nat_lit 125, Int.ofNat (nat_lit 2)), (nat_lit 203, Int.ofNat (nat_lit 2)), (nat_lit 204, Int.ofNat (nat_lit 2)), (nat_lit 205, Int.ofNat (nat_lit 2)), (nat_lit 206, Int.ofNat (nat_lit 2)), (nat_lit 284, Int.ofNat (nat_lit 2)), (nat_lit 285, Int.ofNat (nat_lit 2)), (nat_lit 286, Int.ofNat (nat_lit 2)), (nat_lit 287, Int.ofNat (nat_lit 2)), (nat_lit 365, Int.ofNat (nat_lit 2)), (nat_lit 366, Int.ofNat (nat_lit 2)), (nat_lit 367, Int.ofNat (nat_lit 2)), (nat_lit 368, Int.ofNat (nat_lit 2)), (nat_lit 374, Int.ofNat (nat_lit 2)), (nat_lit 375, Int.ofNat (nat_lit 2)), (nat_lit 376, Int.ofNat (nat_lit 2)), (nat_lit 377, Int.ofNat (nat_lit 2))]
theorem det03Term3Row03_decode : SparsePolynomial.decodeCubic 9 det03Term3Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row03 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term3Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
