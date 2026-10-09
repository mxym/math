import APPT.Finite18Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det00Term3Row12 : CoefficientMerge.Poly := [(nat_lit 573, Int.ofNat (nat_lit 2)), (nat_lit 574, Int.ofNat (nat_lit 2)), (nat_lit 575, Int.ofNat (nat_lit 2)), (nat_lit 897, Int.ofNat (nat_lit 2)), (nat_lit 898, Int.ofNat (nat_lit 2)), (nat_lit 899, Int.ofNat (nat_lit 2)), (nat_lit 1221, Int.ofNat (nat_lit 2)), (nat_lit 1222, Int.ofNat (nat_lit 2)), (nat_lit 1223, Int.ofNat (nat_lit 2)), (nat_lit 1545, Int.ofNat (nat_lit 2)), (nat_lit 1546, Int.ofNat (nat_lit 2)), (nat_lit 1547, Int.ofNat (nat_lit 2)), (nat_lit 1869, Int.ofNat (nat_lit 2)), (nat_lit 1870, Int.ofNat (nat_lit 2)), (nat_lit 1871, Int.ofNat (nat_lit 2)), (nat_lit 2193, Int.ofNat (nat_lit 2)), (nat_lit 2194, Int.ofNat (nat_lit 2)), (nat_lit 2195, Int.ofNat (nat_lit 2)), (nat_lit 2517, Int.ofNat (nat_lit 2)), (nat_lit 2518, Int.ofNat (nat_lit 2)), (nat_lit 2519, Int.ofNat (nat_lit 2)), (nat_lit 2841, Int.ofNat (nat_lit 2)), (nat_lit 2842, Int.ofNat (nat_lit 2)), (nat_lit 2843, Int.ofNat (nat_lit 2)), (nat_lit 3165, Int.ofNat (nat_lit 2)), (nat_lit 3166, Int.ofNat (nat_lit 2)), (nat_lit 3167, Int.ofNat (nat_lit 2)), (nat_lit 3489, Int.ofNat (nat_lit 2)), (nat_lit 3490, Int.ofNat (nat_lit 2)), (nat_lit 3491, Int.ofNat (nat_lit 2)), (nat_lit 3813, Int.ofNat (nat_lit 2)), (nat_lit 3814, Int.ofNat (nat_lit 2)), (nat_lit 3815, Int.ofNat (nat_lit 2)), (nat_lit 4137, Int.ofNat (nat_lit 2)), (nat_lit 4138, Int.ofNat (nat_lit 2)), (nat_lit 4139, Int.ofNat (nat_lit 2)), (nat_lit 4461, Int.ofNat (nat_lit 2)), (nat_lit 4462, Int.ofNat (nat_lit 2)), (nat_lit 4463, Int.ofNat (nat_lit 2))]
theorem det00Term3Row12_decode : SparsePolynomial.decodeCubic 18 det00Term3Row12 = SparsePolynomial.monoTimes [13] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row12 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term3Row12 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [13]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row12_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite18
