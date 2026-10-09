import APPT.Finite12Sparse.Det00Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term0Row00 : CoefficientMerge.Poly := [(983, 8), (995, 8), (1007, 8), (1127, 8), (1139, 8), (1151, 8), (1271, 8), (1283, 8), (1295, 8), (1415, 8), (1427, 16), (1439, 16), (1571, 8), (1583, 16), (1727, 8)]
theorem det00Term0Row00_decode : SparsePolynomial.decodeCubic 12 det00Term0Row00 = SparsePolynomial.monoTimes [11] (2 : Int) det00Pair0 := by decide +kernel
theorem eval_det00Term0Row00 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det00Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
