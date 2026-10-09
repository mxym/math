import APPT.Finite9Sparse.Det03Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term1Row04 : CoefficientMerge.Poly := [(103, -1), (112, -1), (184, -1), (193, -2), (202, -1), (203, -1), (274, -1), (283, -1), (284, -1)]
theorem det03Term1Row04_decode : SparsePolynomial.decodeCubic 9 det03Term1Row04 = SparsePolynomial.monoTimes [4] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row04 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term1Row05 : CoefficientMerge.Poly := [(104, -1), (113, -1), (185, -1), (194, -2), (203, -1), (212, -1), (275, -1), (284, -1), (293, -1)]
theorem det03Term1Row05_decode : SparsePolynomial.decodeCubic 9 det03Term1Row05 = SparsePolynomial.monoTimes [5] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row05 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term1Row06 : CoefficientMerge.Poly := [(105, -1), (114, -1), (186, -1), (195, -2), (204, -1), (213, -1), (276, -1), (285, -1), (294, -1)]
theorem det03Term1Row06_decode : SparsePolynomial.decodeCubic 9 det03Term1Row06 = SparsePolynomial.monoTimes [6] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row06 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
