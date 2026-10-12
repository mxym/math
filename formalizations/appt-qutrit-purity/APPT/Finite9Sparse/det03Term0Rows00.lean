import APPT.Finite9Sparse.Det03Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term0Row00 : CoefficientMerge.Poly := [(nat_lit 296, Int.ofNat (nat_lit 8)), (nat_lit 305, Int.ofNat (nat_lit 8)), (nat_lit 314, Int.ofNat (nat_lit 8)), (nat_lit 323, Int.ofNat (nat_lit 8)), (nat_lit 377, Int.ofNat (nat_lit 8)), (nat_lit 386, Int.ofNat (nat_lit 8)), (nat_lit 395, Int.ofNat (nat_lit 8)), (nat_lit 404, Int.ofNat (nat_lit 8)), (nat_lit 458, Int.ofNat (nat_lit 8)), (nat_lit 467, Int.ofNat (nat_lit 16)), (nat_lit 476, Int.ofNat (nat_lit 16)), (nat_lit 485, Int.ofNat (nat_lit 16)), (nat_lit 548, Int.ofNat (nat_lit 8)), (nat_lit 557, Int.ofNat (nat_lit 16)), (nat_lit 566, Int.ofNat (nat_lit 16)), (nat_lit 638, Int.ofNat (nat_lit 8)), (nat_lit 647, Int.ofNat (nat_lit 16)), (nat_lit 728, Int.ofNat (nat_lit 8))]
theorem det03Term0Row00_decode : SparsePolynomial.decodeCubic 9 det03Term0Row00 = SparsePolynomial.monoTimes [8] (2 : Int) det03Pair0 := by decide +kernel
theorem eval_det03Term0Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det03Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
