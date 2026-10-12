import APPT.Finite15Sparse.Det00Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term0Row00 : CoefficientMerge.Poly := [(nat_lit 2219, Int.ofNat (nat_lit 8)), (nat_lit 2234, Int.ofNat (nat_lit 8)), (nat_lit 2249, Int.ofNat (nat_lit 8)), (nat_lit 2444, Int.ofNat (nat_lit 8)), (nat_lit 2459, Int.ofNat (nat_lit 8)), (nat_lit 2474, Int.ofNat (nat_lit 8)), (nat_lit 2669, Int.ofNat (nat_lit 8)), (nat_lit 2684, Int.ofNat (nat_lit 8)), (nat_lit 2699, Int.ofNat (nat_lit 8)), (nat_lit 2894, Int.ofNat (nat_lit 8)), (nat_lit 2909, Int.ofNat (nat_lit 16)), (nat_lit 2924, Int.ofNat (nat_lit 16)), (nat_lit 3134, Int.ofNat (nat_lit 8)), (nat_lit 3149, Int.ofNat (nat_lit 16)), (nat_lit 3374, Int.ofNat (nat_lit 8))]
theorem det00Term0Row00_decode : SparsePolynomial.decodeCubic 15 det00Term0Row00 = SparsePolynomial.monoTimes [14] (2 : Int) det00Pair0 := by decide +kernel
theorem eval_det00Term0Row00 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [14]*SparsePolynomial.eval (gapValues g) det00Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
