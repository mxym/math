import APPT.Finite15Sparse.Det00Pair5
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term5Row00 : CoefficientMerge.Poly := [(nat_lit 494, Int.ofNat (nat_lit 2)), (nat_lit 509, Int.ofNat (nat_lit 4)), (nat_lit 524, Int.ofNat (nat_lit 4)), (nat_lit 539, Int.ofNat (nat_lit 4)), (nat_lit 554, Int.ofNat (nat_lit 4)), (nat_lit 569, Int.ofNat (nat_lit 4)), (nat_lit 584, Int.ofNat (nat_lit 4)), (nat_lit 599, Int.ofNat (nat_lit 4)), (nat_lit 734, Int.ofNat (nat_lit 2)), (nat_lit 749, Int.ofNat (nat_lit 4)), (nat_lit 764, Int.ofNat (nat_lit 4)), (nat_lit 779, Int.ofNat (nat_lit 4)), (nat_lit 794, Int.ofNat (nat_lit 4)), (nat_lit 809, Int.ofNat (nat_lit 4)), (nat_lit 824, Int.ofNat (nat_lit 4)), (nat_lit 974, Int.ofNat (nat_lit 2)), (nat_lit 989, Int.ofNat (nat_lit 4)), (nat_lit 1004, Int.ofNat (nat_lit 4)), (nat_lit 1019, Int.ofNat (nat_lit 4)), (nat_lit 1034, Int.ofNat (nat_lit 4)), (nat_lit 1049, Int.ofNat (nat_lit 4)), (nat_lit 1214, Int.ofNat (nat_lit 2)), (nat_lit 1229, Int.ofNat (nat_lit 4)), (nat_lit 1244, Int.ofNat (nat_lit 4)), (nat_lit 1259, Int.ofNat (nat_lit 4)), (nat_lit 1274, Int.ofNat (nat_lit 4)), (nat_lit 1454, Int.ofNat (nat_lit 2)), (nat_lit 1469, Int.ofNat (nat_lit 4)), (nat_lit 1484, Int.ofNat (nat_lit 4)), (nat_lit 1499, Int.ofNat (nat_lit 4)), (nat_lit 1694, Int.ofNat (nat_lit 2)), (nat_lit 1709, Int.ofNat (nat_lit 4)), (nat_lit 1724, Int.ofNat (nat_lit 4)), (nat_lit 1934, Int.ofNat (nat_lit 2)), (nat_lit 1949, Int.ofNat (nat_lit 4)), (nat_lit 2174, Int.ofNat (nat_lit 2))]
theorem det00Term5Row00_decode : SparsePolynomial.decodeCubic 15 det00Term5Row00 = SparsePolynomial.monoTimes [14] (2 : Int) det00Pair5 := by decide +kernel
theorem eval_det00Term5Row00 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term5Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [14]*SparsePolynomial.eval (gapValues g) det00Pair5 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term5Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
