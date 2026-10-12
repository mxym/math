import APPT.Finite12Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term3Row00 : CoefficientMerge.Poly := [(nat_lit 165, Int.ofNat (nat_lit 2)), (nat_lit 166, Int.ofNat (nat_lit 2)), (nat_lit 167, Int.ofNat (nat_lit 2)), (nat_lit 177, Int.ofNat (nat_lit 2)), (nat_lit 178, Int.ofNat (nat_lit 2)), (nat_lit 179, Int.ofNat (nat_lit 2)), (nat_lit 189, Int.ofNat (nat_lit 2)), (nat_lit 190, Int.ofNat (nat_lit 2)), (nat_lit 191, Int.ofNat (nat_lit 2)), (nat_lit 201, Int.ofNat (nat_lit 2)), (nat_lit 202, Int.ofNat (nat_lit 2)), (nat_lit 203, Int.ofNat (nat_lit 2)), (nat_lit 213, Int.ofNat (nat_lit 2)), (nat_lit 214, Int.ofNat (nat_lit 2)), (nat_lit 215, Int.ofNat (nat_lit 2)), (nat_lit 225, Int.ofNat (nat_lit 2)), (nat_lit 226, Int.ofNat (nat_lit 2)), (nat_lit 227, Int.ofNat (nat_lit 2)), (nat_lit 237, Int.ofNat (nat_lit 2)), (nat_lit 238, Int.ofNat (nat_lit 2)), (nat_lit 239, Int.ofNat (nat_lit 2))]
theorem det00Term3Row00_decode : SparsePolynomial.decodeCubic 12 det00Term3Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row00 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row01 : CoefficientMerge.Poly := [(nat_lit 177, Int.ofNat (nat_lit 2)), (nat_lit 178, Int.ofNat (nat_lit 2)), (nat_lit 179, Int.ofNat (nat_lit 2)), (nat_lit 321, Int.ofNat (nat_lit 2)), (nat_lit 322, Int.ofNat (nat_lit 2)), (nat_lit 323, Int.ofNat (nat_lit 2)), (nat_lit 333, Int.ofNat (nat_lit 2)), (nat_lit 334, Int.ofNat (nat_lit 2)), (nat_lit 335, Int.ofNat (nat_lit 2)), (nat_lit 345, Int.ofNat (nat_lit 2)), (nat_lit 346, Int.ofNat (nat_lit 2)), (nat_lit 347, Int.ofNat (nat_lit 2)), (nat_lit 357, Int.ofNat (nat_lit 2)), (nat_lit 358, Int.ofNat (nat_lit 2)), (nat_lit 359, Int.ofNat (nat_lit 2)), (nat_lit 369, Int.ofNat (nat_lit 2)), (nat_lit 370, Int.ofNat (nat_lit 2)), (nat_lit 371, Int.ofNat (nat_lit 2)), (nat_lit 381, Int.ofNat (nat_lit 2)), (nat_lit 382, Int.ofNat (nat_lit 2)), (nat_lit 383, Int.ofNat (nat_lit 2))]
theorem det00Term3Row01_decode : SparsePolynomial.decodeCubic 12 det00Term3Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row01 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row02 : CoefficientMerge.Poly := [(nat_lit 189, Int.ofNat (nat_lit 2)), (nat_lit 190, Int.ofNat (nat_lit 2)), (nat_lit 191, Int.ofNat (nat_lit 2)), (nat_lit 333, Int.ofNat (nat_lit 2)), (nat_lit 334, Int.ofNat (nat_lit 2)), (nat_lit 335, Int.ofNat (nat_lit 2)), (nat_lit 477, Int.ofNat (nat_lit 2)), (nat_lit 478, Int.ofNat (nat_lit 2)), (nat_lit 479, Int.ofNat (nat_lit 2)), (nat_lit 489, Int.ofNat (nat_lit 2)), (nat_lit 490, Int.ofNat (nat_lit 2)), (nat_lit 491, Int.ofNat (nat_lit 2)), (nat_lit 501, Int.ofNat (nat_lit 2)), (nat_lit 502, Int.ofNat (nat_lit 2)), (nat_lit 503, Int.ofNat (nat_lit 2)), (nat_lit 513, Int.ofNat (nat_lit 2)), (nat_lit 514, Int.ofNat (nat_lit 2)), (nat_lit 515, Int.ofNat (nat_lit 2)), (nat_lit 525, Int.ofNat (nat_lit 2)), (nat_lit 526, Int.ofNat (nat_lit 2)), (nat_lit 527, Int.ofNat (nat_lit 2))]
theorem det00Term3Row02_decode : SparsePolynomial.decodeCubic 12 det00Term3Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row02 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row03 : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 2)), (nat_lit 202, Int.ofNat (nat_lit 2)), (nat_lit 203, Int.ofNat (nat_lit 2)), (nat_lit 345, Int.ofNat (nat_lit 2)), (nat_lit 346, Int.ofNat (nat_lit 2)), (nat_lit 347, Int.ofNat (nat_lit 2)), (nat_lit 489, Int.ofNat (nat_lit 2)), (nat_lit 490, Int.ofNat (nat_lit 2)), (nat_lit 491, Int.ofNat (nat_lit 2)), (nat_lit 633, Int.ofNat (nat_lit 2)), (nat_lit 634, Int.ofNat (nat_lit 2)), (nat_lit 635, Int.ofNat (nat_lit 2)), (nat_lit 645, Int.ofNat (nat_lit 2)), (nat_lit 646, Int.ofNat (nat_lit 2)), (nat_lit 647, Int.ofNat (nat_lit 2)), (nat_lit 657, Int.ofNat (nat_lit 2)), (nat_lit 658, Int.ofNat (nat_lit 2)), (nat_lit 659, Int.ofNat (nat_lit 2)), (nat_lit 669, Int.ofNat (nat_lit 2)), (nat_lit 670, Int.ofNat (nat_lit 2)), (nat_lit 671, Int.ofNat (nat_lit 2))]
theorem det00Term3Row03_decode : SparsePolynomial.decodeCubic 12 det00Term3Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row03 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
