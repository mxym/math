import APPT.Finite21Sparse.Det03Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det03Term0Row00 : CoefficientMerge.Poly := [(nat_lit 6992, Int.ofNat (nat_lit 8)), (nat_lit 7013, Int.ofNat (nat_lit 8)), (nat_lit 7034, Int.ofNat (nat_lit 8)), (nat_lit 7055, Int.ofNat (nat_lit 8)), (nat_lit 7433, Int.ofNat (nat_lit 8)), (nat_lit 7454, Int.ofNat (nat_lit 8)), (nat_lit 7475, Int.ofNat (nat_lit 8)), (nat_lit 7496, Int.ofNat (nat_lit 8)), (nat_lit 7874, Int.ofNat (nat_lit 8)), (nat_lit 7895, Int.ofNat (nat_lit 16)), (nat_lit 7916, Int.ofNat (nat_lit 16)), (nat_lit 7937, Int.ofNat (nat_lit 16)), (nat_lit 8336, Int.ofNat (nat_lit 8)), (nat_lit 8357, Int.ofNat (nat_lit 16)), (nat_lit 8378, Int.ofNat (nat_lit 16)), (nat_lit 8798, Int.ofNat (nat_lit 8)), (nat_lit 8819, Int.ofNat (nat_lit 16)), (nat_lit 9260, Int.ofNat (nat_lit 8))]
theorem det03Term0Row00_decode : SparsePolynomial.decodeCubic 21 det03Term0Row00 = SparsePolynomial.monoTimes [20] (2 : Int) det03Pair0 := by decide +kernel
theorem eval_det03Term0Row00 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [20]*SparsePolynomial.eval (gapValues g) det03Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite21
