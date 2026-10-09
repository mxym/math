import APPT.Finite9Sparse.Det03Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term2Row00 : CoefficientMerge.Poly := [(11, -1), (12, -1), (92, -1), (93, -1), (101, -1), (102, -2), (103, -1), (104, -1), (105, -1), (111, -1), (112, -1), (113, -1), (114, -1)]
theorem det03Term2Row00_decode : SparsePolynomial.decodeCubic 9 det03Term2Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term2Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term2Row01 : CoefficientMerge.Poly := [(20, -1), (21, -1), (101, -1), (102, -1), (182, -1), (183, -2), (184, -1), (185, -1), (186, -1), (192, -1), (193, -1), (194, -1), (195, -1)]
theorem det03Term2Row01_decode : SparsePolynomial.decodeCubic 9 det03Term2Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row01 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term2Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term2Row02 : CoefficientMerge.Poly := [(21, -1), (30, -1), (102, -1), (111, -1), (183, -1), (192, -2), (193, -1), (194, -1), (195, -1), (273, -1), (274, -1), (275, -1), (276, -1)]
theorem det03Term2Row02_decode : SparsePolynomial.decodeCubic 9 det03Term2Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row02 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term2Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term2Row03 : CoefficientMerge.Poly := [(22, -1), (31, -1), (103, -1), (112, -1), (184, -1), (193, -2), (202, -1), (203, -1), (204, -1), (274, -1), (283, -1), (284, -1), (285, -1)]
theorem det03Term2Row03_decode : SparsePolynomial.decodeCubic 9 det03Term2Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row03 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term2Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
