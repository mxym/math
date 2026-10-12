import APPT.Finite12Sparse.Det03Pair5
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term5Row00 : CoefficientMerge.Poly := [(nat_lit 323, Int.ofNat (nat_lit 2)), (nat_lit 335, Int.ofNat (nat_lit 4)), (nat_lit 347, Int.ofNat (nat_lit 4)), (nat_lit 359, Int.ofNat (nat_lit 4)), (nat_lit 371, Int.ofNat (nat_lit 4)), (nat_lit 479, Int.ofNat (nat_lit 2)), (nat_lit 491, Int.ofNat (nat_lit 4)), (nat_lit 503, Int.ofNat (nat_lit 4)), (nat_lit 515, Int.ofNat (nat_lit 4)), (nat_lit 635, Int.ofNat (nat_lit 2)), (nat_lit 647, Int.ofNat (nat_lit 4)), (nat_lit 659, Int.ofNat (nat_lit 4)), (nat_lit 791, Int.ofNat (nat_lit 2)), (nat_lit 803, Int.ofNat (nat_lit 4)), (nat_lit 947, Int.ofNat (nat_lit 2))]
theorem det03Term5Row00_decode : SparsePolynomial.decodeCubic 12 det03Term5Row00 = SparsePolynomial.monoTimes [11] (2 : Int) det03Pair5 := by decide +kernel
theorem eval_det03Term5Row00 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term5Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det03Pair5 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term5Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
