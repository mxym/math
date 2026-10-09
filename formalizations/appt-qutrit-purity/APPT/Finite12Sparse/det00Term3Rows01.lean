import APPT.Finite12Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term3Row04 : CoefficientMerge.Poly := [(213, 2), (214, 2), (215, 2), (357, 2), (358, 2), (359, 2), (501, 2), (502, 2), (503, 2), (645, 2), (646, 2), (647, 2), (789, 2), (790, 2), (791, 2), (801, 2), (802, 2), (803, 2), (813, 2), (814, 2), (815, 2)]
theorem det00Term3Row04_decode : SparsePolynomial.decodeCubic 12 det00Term3Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row04 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row05 : CoefficientMerge.Poly := [(225, 2), (226, 2), (227, 2), (369, 2), (370, 2), (371, 2), (513, 2), (514, 2), (515, 2), (657, 2), (658, 2), (659, 2), (801, 2), (802, 2), (803, 2), (945, 2), (946, 2), (947, 2), (957, 2), (958, 2), (959, 2)]
theorem det00Term3Row05_decode : SparsePolynomial.decodeCubic 12 det00Term3Row05 = SparsePolynomial.monoTimes [6] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row05 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row06 : CoefficientMerge.Poly := [(237, 2), (238, 2), (239, 2), (381, 2), (382, 2), (383, 2), (525, 2), (526, 2), (527, 2), (669, 2), (670, 2), (671, 2), (813, 2), (814, 2), (815, 2), (957, 2), (958, 2), (959, 2), (1101, 2), (1102, 2), (1103, 2)]
theorem det00Term3Row06_decode : SparsePolynomial.decodeCubic 12 det00Term3Row06 = SparsePolynomial.monoTimes [7] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row06 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
