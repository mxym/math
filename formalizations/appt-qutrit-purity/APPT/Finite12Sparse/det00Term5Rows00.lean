import APPT.Finite12Sparse.Det00Pair5
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term5Row00 : CoefficientMerge.Poly := [(323, 2), (335, 4), (347, 4), (359, 4), (371, 4), (479, 2), (491, 4), (503, 4), (515, 4), (635, 2), (647, 4), (659, 4), (791, 2), (803, 4), (947, 2)]
theorem det00Term5Row00_decode : SparsePolynomial.decodeCubic 12 det00Term5Row00 = SparsePolynomial.monoTimes [11] (2 : Int) det00Pair5 := by decide +kernel
theorem eval_det00Term5Row00 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term5Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det00Pair5 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term5Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
