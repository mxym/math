import APPT.Finite18Sparse.Det00Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det00Term0Row00 : CoefficientMerge.Poly := [(4175, 8), (4193, 8), (4211, 8), (4499, 8), (4517, 8), (4535, 8), (4823, 8), (4841, 8), (4859, 8), (5147, 8), (5165, 16), (5183, 16), (5489, 8), (5507, 16), (5831, 8)]
theorem det00Term0Row00_decode : SparsePolynomial.decodeCubic 18 det00Term0Row00 = SparsePolynomial.monoTimes [17] (2 : Int) det00Pair0 := by decide +kernel
theorem eval_det00Term0Row00 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [17]*SparsePolynomial.eval (gapValues g) det00Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite18
