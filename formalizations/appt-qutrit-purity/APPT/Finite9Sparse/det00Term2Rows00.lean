import APPT.Finite9Sparse.Det00Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term2Row00 : CoefficientMerge.Poly := [(nat_lit 11, Int.negSucc (nat_lit 0)), (nat_lit 12, Int.negSucc (nat_lit 0)), (nat_lit 92, Int.negSucc (nat_lit 0)), (nat_lit 93, Int.negSucc (nat_lit 0)), (nat_lit 101, Int.negSucc (nat_lit 0)), (nat_lit 102, Int.negSucc (nat_lit 1)), (nat_lit 103, Int.negSucc (nat_lit 0)), (nat_lit 104, Int.negSucc (nat_lit 0)), (nat_lit 105, Int.negSucc (nat_lit 0)), (nat_lit 111, Int.negSucc (nat_lit 0)), (nat_lit 112, Int.negSucc (nat_lit 0)), (nat_lit 113, Int.negSucc (nat_lit 0)), (nat_lit 114, Int.negSucc (nat_lit 0))]
theorem det00Term2Row00_decode : SparsePolynomial.decodeCubic 9 det00Term2Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term2Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row01 : CoefficientMerge.Poly := [(nat_lit 20, Int.negSucc (nat_lit 0)), (nat_lit 21, Int.negSucc (nat_lit 0)), (nat_lit 101, Int.negSucc (nat_lit 0)), (nat_lit 102, Int.negSucc (nat_lit 0)), (nat_lit 182, Int.negSucc (nat_lit 0)), (nat_lit 183, Int.negSucc (nat_lit 1)), (nat_lit 184, Int.negSucc (nat_lit 0)), (nat_lit 185, Int.negSucc (nat_lit 0)), (nat_lit 186, Int.negSucc (nat_lit 0)), (nat_lit 192, Int.negSucc (nat_lit 0)), (nat_lit 193, Int.negSucc (nat_lit 0)), (nat_lit 194, Int.negSucc (nat_lit 0)), (nat_lit 195, Int.negSucc (nat_lit 0))]
theorem det00Term2Row01_decode : SparsePolynomial.decodeCubic 9 det00Term2Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row01 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term2Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row02 : CoefficientMerge.Poly := [(nat_lit 21, Int.negSucc (nat_lit 0)), (nat_lit 30, Int.negSucc (nat_lit 0)), (nat_lit 102, Int.negSucc (nat_lit 0)), (nat_lit 111, Int.negSucc (nat_lit 0)), (nat_lit 183, Int.negSucc (nat_lit 0)), (nat_lit 192, Int.negSucc (nat_lit 1)), (nat_lit 193, Int.negSucc (nat_lit 0)), (nat_lit 194, Int.negSucc (nat_lit 0)), (nat_lit 195, Int.negSucc (nat_lit 0)), (nat_lit 273, Int.negSucc (nat_lit 0)), (nat_lit 274, Int.negSucc (nat_lit 0)), (nat_lit 275, Int.negSucc (nat_lit 0)), (nat_lit 276, Int.negSucc (nat_lit 0))]
theorem det00Term2Row02_decode : SparsePolynomial.decodeCubic 9 det00Term2Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row02 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term2Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row03 : CoefficientMerge.Poly := [(nat_lit 22, Int.negSucc (nat_lit 0)), (nat_lit 31, Int.negSucc (nat_lit 0)), (nat_lit 103, Int.negSucc (nat_lit 0)), (nat_lit 112, Int.negSucc (nat_lit 0)), (nat_lit 184, Int.negSucc (nat_lit 0)), (nat_lit 193, Int.negSucc (nat_lit 1)), (nat_lit 202, Int.negSucc (nat_lit 0)), (nat_lit 203, Int.negSucc (nat_lit 0)), (nat_lit 204, Int.negSucc (nat_lit 0)), (nat_lit 274, Int.negSucc (nat_lit 0)), (nat_lit 283, Int.negSucc (nat_lit 0)), (nat_lit 284, Int.negSucc (nat_lit 0)), (nat_lit 285, Int.negSucc (nat_lit 0))]
theorem det00Term2Row03_decode : SparsePolynomial.decodeCubic 9 det00Term2Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row03 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term2Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
