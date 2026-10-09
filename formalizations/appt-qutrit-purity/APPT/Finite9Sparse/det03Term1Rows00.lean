import APPT.Finite9Sparse.Det03Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term1Row00 : CoefficientMerge.Poly := [(nat_lit 11, Int.negSucc (nat_lit 0)), (nat_lit 12, Int.negSucc (nat_lit 0)), (nat_lit 20, Int.negSucc (nat_lit 0)), (nat_lit 21, Int.negSucc (nat_lit 1)), (nat_lit 22, Int.negSucc (nat_lit 0)), (nat_lit 23, Int.negSucc (nat_lit 0)), (nat_lit 30, Int.negSucc (nat_lit 0)), (nat_lit 31, Int.negSucc (nat_lit 0)), (nat_lit 32, Int.negSucc (nat_lit 0))]
theorem det03Term1Row00_decode : SparsePolynomial.decodeCubic 9 det03Term1Row00 = SparsePolynomial.monoTimes [0] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [0]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term1Row01 : CoefficientMerge.Poly := [(nat_lit 92, Int.negSucc (nat_lit 0)), (nat_lit 93, Int.negSucc (nat_lit 0)), (nat_lit 101, Int.negSucc (nat_lit 0)), (nat_lit 102, Int.negSucc (nat_lit 1)), (nat_lit 103, Int.negSucc (nat_lit 0)), (nat_lit 104, Int.negSucc (nat_lit 0)), (nat_lit 111, Int.negSucc (nat_lit 0)), (nat_lit 112, Int.negSucc (nat_lit 0)), (nat_lit 113, Int.negSucc (nat_lit 0))]
theorem det03Term1Row01_decode : SparsePolynomial.decodeCubic 9 det03Term1Row01 = SparsePolynomial.monoTimes [1] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row01 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term1Row02 : CoefficientMerge.Poly := [(nat_lit 101, Int.negSucc (nat_lit 0)), (nat_lit 102, Int.negSucc (nat_lit 0)), (nat_lit 182, Int.negSucc (nat_lit 0)), (nat_lit 183, Int.negSucc (nat_lit 1)), (nat_lit 184, Int.negSucc (nat_lit 0)), (nat_lit 185, Int.negSucc (nat_lit 0)), (nat_lit 192, Int.negSucc (nat_lit 0)), (nat_lit 193, Int.negSucc (nat_lit 0)), (nat_lit 194, Int.negSucc (nat_lit 0))]
theorem det03Term1Row02_decode : SparsePolynomial.decodeCubic 9 det03Term1Row02 = SparsePolynomial.monoTimes [2] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row02 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term1Row03 : CoefficientMerge.Poly := [(nat_lit 102, Int.negSucc (nat_lit 0)), (nat_lit 111, Int.negSucc (nat_lit 0)), (nat_lit 183, Int.negSucc (nat_lit 0)), (nat_lit 192, Int.negSucc (nat_lit 1)), (nat_lit 193, Int.negSucc (nat_lit 0)), (nat_lit 194, Int.negSucc (nat_lit 0)), (nat_lit 273, Int.negSucc (nat_lit 0)), (nat_lit 274, Int.negSucc (nat_lit 0)), (nat_lit 275, Int.negSucc (nat_lit 0))]
theorem det03Term1Row03_decode : SparsePolynomial.decodeCubic 9 det03Term1Row03 = SparsePolynomial.monoTimes [3] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row03 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
