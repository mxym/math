import APPT.Finite9Sparse.Det00Pair5
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term5Row00 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 2)), (nat_lit 197, Int.ofNat (nat_lit 4)), (nat_lit 278, Int.ofNat (nat_lit 2))]
theorem det00Term5Row00_decode : SparsePolynomial.decodeCubic 9 det00Term5Row00 = SparsePolynomial.monoTimes [8] (2 : Int) det00Pair5 := by decide +kernel
theorem eval_det00Term5Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term5Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det00Pair5 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term5Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
