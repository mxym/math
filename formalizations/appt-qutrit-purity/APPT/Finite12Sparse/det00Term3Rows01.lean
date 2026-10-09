import APPT.Finite12Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term3Row04 : CoefficientMerge.Poly := [(nat_lit 213, Int.ofNat (nat_lit 2)), (nat_lit 214, Int.ofNat (nat_lit 2)), (nat_lit 215, Int.ofNat (nat_lit 2)), (nat_lit 357, Int.ofNat (nat_lit 2)), (nat_lit 358, Int.ofNat (nat_lit 2)), (nat_lit 359, Int.ofNat (nat_lit 2)), (nat_lit 501, Int.ofNat (nat_lit 2)), (nat_lit 502, Int.ofNat (nat_lit 2)), (nat_lit 503, Int.ofNat (nat_lit 2)), (nat_lit 645, Int.ofNat (nat_lit 2)), (nat_lit 646, Int.ofNat (nat_lit 2)), (nat_lit 647, Int.ofNat (nat_lit 2)), (nat_lit 789, Int.ofNat (nat_lit 2)), (nat_lit 790, Int.ofNat (nat_lit 2)), (nat_lit 791, Int.ofNat (nat_lit 2)), (nat_lit 801, Int.ofNat (nat_lit 2)), (nat_lit 802, Int.ofNat (nat_lit 2)), (nat_lit 803, Int.ofNat (nat_lit 2)), (nat_lit 813, Int.ofNat (nat_lit 2)), (nat_lit 814, Int.ofNat (nat_lit 2)), (nat_lit 815, Int.ofNat (nat_lit 2))]
theorem det00Term3Row04_decode : SparsePolynomial.decodeCubic 12 det00Term3Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row04 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row05 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 2)), (nat_lit 226, Int.ofNat (nat_lit 2)), (nat_lit 227, Int.ofNat (nat_lit 2)), (nat_lit 369, Int.ofNat (nat_lit 2)), (nat_lit 370, Int.ofNat (nat_lit 2)), (nat_lit 371, Int.ofNat (nat_lit 2)), (nat_lit 513, Int.ofNat (nat_lit 2)), (nat_lit 514, Int.ofNat (nat_lit 2)), (nat_lit 515, Int.ofNat (nat_lit 2)), (nat_lit 657, Int.ofNat (nat_lit 2)), (nat_lit 658, Int.ofNat (nat_lit 2)), (nat_lit 659, Int.ofNat (nat_lit 2)), (nat_lit 801, Int.ofNat (nat_lit 2)), (nat_lit 802, Int.ofNat (nat_lit 2)), (nat_lit 803, Int.ofNat (nat_lit 2)), (nat_lit 945, Int.ofNat (nat_lit 2)), (nat_lit 946, Int.ofNat (nat_lit 2)), (nat_lit 947, Int.ofNat (nat_lit 2)), (nat_lit 957, Int.ofNat (nat_lit 2)), (nat_lit 958, Int.ofNat (nat_lit 2)), (nat_lit 959, Int.ofNat (nat_lit 2))]
theorem det00Term3Row05_decode : SparsePolynomial.decodeCubic 12 det00Term3Row05 = SparsePolynomial.monoTimes [6] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row05 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row06 : CoefficientMerge.Poly := [(nat_lit 237, Int.ofNat (nat_lit 2)), (nat_lit 238, Int.ofNat (nat_lit 2)), (nat_lit 239, Int.ofNat (nat_lit 2)), (nat_lit 381, Int.ofNat (nat_lit 2)), (nat_lit 382, Int.ofNat (nat_lit 2)), (nat_lit 383, Int.ofNat (nat_lit 2)), (nat_lit 525, Int.ofNat (nat_lit 2)), (nat_lit 526, Int.ofNat (nat_lit 2)), (nat_lit 527, Int.ofNat (nat_lit 2)), (nat_lit 669, Int.ofNat (nat_lit 2)), (nat_lit 670, Int.ofNat (nat_lit 2)), (nat_lit 671, Int.ofNat (nat_lit 2)), (nat_lit 813, Int.ofNat (nat_lit 2)), (nat_lit 814, Int.ofNat (nat_lit 2)), (nat_lit 815, Int.ofNat (nat_lit 2)), (nat_lit 957, Int.ofNat (nat_lit 2)), (nat_lit 958, Int.ofNat (nat_lit 2)), (nat_lit 959, Int.ofNat (nat_lit 2)), (nat_lit 1101, Int.ofNat (nat_lit 2)), (nat_lit 1102, Int.ofNat (nat_lit 2)), (nat_lit 1103, Int.ofNat (nat_lit 2))]
theorem det00Term3Row06_decode : SparsePolynomial.decodeCubic 12 det00Term3Row06 = SparsePolynomial.monoTimes [7] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row06 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
