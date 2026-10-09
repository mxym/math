import APPT.Finite9Sparse.Det00Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term1Row00 : CoefficientMerge.Poly := [(11, -1), (12, -1), (20, -1), (21, -2), (22, -1), (30, -1), (31, -1)]
theorem det00Term1Row00_decode : SparsePolynomial.decodeCubic 9 det00Term1Row00 = SparsePolynomial.monoTimes [0] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term1Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [0]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row01 : CoefficientMerge.Poly := [(92, -1), (93, -1), (101, -1), (102, -2), (103, -1), (111, -1), (112, -1)]
theorem det00Term1Row01_decode : SparsePolynomial.decodeCubic 9 det00Term1Row01 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row01 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term1Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row02 : CoefficientMerge.Poly := [(101, -1), (102, -1), (182, -1), (183, -2), (184, -1), (192, -1), (193, -1)]
theorem det00Term1Row02_decode : SparsePolynomial.decodeCubic 9 det00Term1Row02 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row02 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term1Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row03 : CoefficientMerge.Poly := [(102, -1), (111, -1), (183, -1), (192, -2), (193, -1), (273, -1), (274, -1)]
theorem det00Term1Row03_decode : SparsePolynomial.decodeCubic 9 det00Term1Row03 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row03 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term1Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
