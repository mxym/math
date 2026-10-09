import APPT.Finite24Sparse.Det04Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Term0Row00 : CoefficientMerge.Poly := [(10871, 8), (10895, 8), (10919, 8), (10943, 8), (11447, 8), (11471, 8), (11495, 8), (11519, 8), (12023, 8), (12047, 16), (12071, 16), (12095, 16), (12623, 8), (12647, 16), (12671, 16), (13223, 8), (13247, 16), (13823, 8)]
theorem det04Term0Row00_decode : SparsePolynomial.decodeCubic 24 det04Term0Row00 = SparsePolynomial.monoTimes [23] (2 : Int) det04Pair0 := by decide +kernel
theorem eval_det04Term0Row00 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [23]*SparsePolynomial.eval (gapValues g) det04Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite24
