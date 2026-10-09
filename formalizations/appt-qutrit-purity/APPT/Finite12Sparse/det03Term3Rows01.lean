import APPT.Finite12Sparse.Det03Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term3Row04 : CoefficientMerge.Poly := [(212, 2), (213, 2), (214, 2), (215, 2), (356, 2), (357, 2), (358, 2), (359, 2), (500, 2), (501, 2), (502, 2), (503, 2), (644, 2), (645, 2), (646, 2), (647, 2), (788, 2), (789, 2), (790, 2), (791, 2), (800, 2), (801, 2), (802, 2), (803, 2), (812, 2), (813, 2), (814, 2), (815, 2), (824, 2), (825, 2), (826, 2), (827, 2)]
theorem det03Term3Row04_decode : SparsePolynomial.decodeCubic 12 det03Term3Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row04 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term3Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row05 : CoefficientMerge.Poly := [(224, 2), (225, 2), (226, 2), (227, 2), (368, 2), (369, 2), (370, 2), (371, 2), (512, 2), (513, 2), (514, 2), (515, 2), (656, 2), (657, 2), (658, 2), (659, 2), (800, 2), (801, 2), (802, 2), (803, 2), (944, 2), (945, 2), (946, 2), (947, 2), (956, 2), (957, 2), (958, 2), (959, 2), (968, 2), (969, 2), (970, 2), (971, 2)]
theorem det03Term3Row05_decode : SparsePolynomial.decodeCubic 12 det03Term3Row05 = SparsePolynomial.monoTimes [6] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row05 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term3Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row06 : CoefficientMerge.Poly := [(236, 2), (237, 2), (238, 2), (239, 2), (380, 2), (381, 2), (382, 2), (383, 2), (524, 2), (525, 2), (526, 2), (527, 2), (668, 2), (669, 2), (670, 2), (671, 2), (812, 2), (813, 2), (814, 2), (815, 2), (956, 2), (957, 2), (958, 2), (959, 2), (1100, 2), (1101, 2), (1102, 2), (1103, 2), (1112, 2), (1113, 2), (1114, 2), (1115, 2)]
theorem det03Term3Row06_decode : SparsePolynomial.decodeCubic 12 det03Term3Row06 = SparsePolynomial.monoTimes [7] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row06 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term3Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row07 : CoefficientMerge.Poly := [(248, 2), (249, 2), (250, 2), (251, 2), (392, 2), (393, 2), (394, 2), (395, 2), (536, 2), (537, 2), (538, 2), (539, 2), (680, 2), (681, 2), (682, 2), (683, 2), (824, 2), (825, 2), (826, 2), (827, 2), (968, 2), (969, 2), (970, 2), (971, 2), (1112, 2), (1113, 2), (1114, 2), (1115, 2), (1256, 2), (1257, 2), (1258, 2), (1259, 2)]
theorem det03Term3Row07_decode : SparsePolynomial.decodeCubic 12 det03Term3Row07 = SparsePolynomial.monoTimes [8] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row07 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term3Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
