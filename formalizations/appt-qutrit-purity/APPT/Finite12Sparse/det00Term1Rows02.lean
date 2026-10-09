import APPT.Finite12Sparse.Det00Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term1Row08 : CoefficientMerge.Poly := [(176, -1), (188, -1), (200, -1), (212, -1), (224, -1), (320, -1), (332, -2), (344, -2), (356, -2), (368, -2), (380, -1), (476, -1), (488, -2), (500, -2), (512, -2), (524, -1), (632, -1), (644, -2), (656, -2), (668, -1), (788, -1), (800, -2), (812, -1), (944, -1), (956, -1)]
theorem det00Term1Row08_decode : SparsePolynomial.decodeCubic 12 det00Term1Row08 = SparsePolynomial.monoTimes [8] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row08 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row09 : CoefficientMerge.Poly := [(177, -1), (189, -1), (201, -1), (213, -1), (225, -1), (321, -1), (333, -2), (345, -2), (357, -2), (369, -2), (381, -1), (477, -1), (489, -2), (501, -2), (513, -2), (525, -1), (633, -1), (645, -2), (657, -2), (669, -1), (789, -1), (801, -2), (813, -1), (945, -1), (957, -1)]
theorem det00Term1Row09_decode : SparsePolynomial.decodeCubic 12 det00Term1Row09 = SparsePolynomial.monoTimes [9] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row09 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
