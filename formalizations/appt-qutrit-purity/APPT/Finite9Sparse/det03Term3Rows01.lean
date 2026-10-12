import APPT.Finite9Sparse.Det03Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term3Row04 : CoefficientMerge.Poly := [(nat_lit 131, Int.ofNat (nat_lit 2)), (nat_lit 132, Int.ofNat (nat_lit 2)), (nat_lit 133, Int.ofNat (nat_lit 2)), (nat_lit 134, Int.ofNat (nat_lit 2)), (nat_lit 212, Int.ofNat (nat_lit 2)), (nat_lit 213, Int.ofNat (nat_lit 2)), (nat_lit 214, Int.ofNat (nat_lit 2)), (nat_lit 215, Int.ofNat (nat_lit 2)), (nat_lit 293, Int.ofNat (nat_lit 2)), (nat_lit 294, Int.ofNat (nat_lit 2)), (nat_lit 295, Int.ofNat (nat_lit 2)), (nat_lit 296, Int.ofNat (nat_lit 2)), (nat_lit 374, Int.ofNat (nat_lit 2)), (nat_lit 375, Int.ofNat (nat_lit 2)), (nat_lit 376, Int.ofNat (nat_lit 2)), (nat_lit 377, Int.ofNat (nat_lit 2)), (nat_lit 455, Int.ofNat (nat_lit 2)), (nat_lit 456, Int.ofNat (nat_lit 2)), (nat_lit 457, Int.ofNat (nat_lit 2)), (nat_lit 458, Int.ofNat (nat_lit 2))]
theorem det03Term3Row04_decode : SparsePolynomial.decodeCubic 9 det03Term3Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row04 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term3Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
