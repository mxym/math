import APPT.Finite9Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term3Row00 : CoefficientMerge.Poly := [(96, 2), (97, 2), (98, 2), (105, 2), (106, 2), (107, 2), (114, 2), (115, 2), (116, 2), (123, 2), (124, 2), (125, 2)]
theorem det00Term3Row00_decode : SparsePolynomial.decodeCubic 9 det00Term3Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term3Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row01 : CoefficientMerge.Poly := [(105, 2), (106, 2), (107, 2), (186, 2), (187, 2), (188, 2), (195, 2), (196, 2), (197, 2), (204, 2), (205, 2), (206, 2)]
theorem det00Term3Row01_decode : SparsePolynomial.decodeCubic 9 det00Term3Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row01 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term3Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row02 : CoefficientMerge.Poly := [(114, 2), (115, 2), (116, 2), (195, 2), (196, 2), (197, 2), (276, 2), (277, 2), (278, 2), (285, 2), (286, 2), (287, 2)]
theorem det00Term3Row02_decode : SparsePolynomial.decodeCubic 9 det00Term3Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row02 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term3Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row03 : CoefficientMerge.Poly := [(123, 2), (124, 2), (125, 2), (204, 2), (205, 2), (206, 2), (285, 2), (286, 2), (287, 2), (366, 2), (367, 2), (368, 2)]
theorem det00Term3Row03_decode : SparsePolynomial.decodeCubic 9 det00Term3Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row03 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term3Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
