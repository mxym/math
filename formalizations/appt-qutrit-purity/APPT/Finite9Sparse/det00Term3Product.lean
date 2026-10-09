import APPT.Finite9Sparse.det00Term3Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term3Coeffs : CoefficientMerge.Poly := [(96, 2), (97, 2), (98, 2), (105, 4), (106, 4), (107, 4), (114, 4), (115, 4), (116, 4), (123, 4), (124, 4), (125, 4), (186, 2), (187, 2), (188, 2), (195, 4), (196, 4), (197, 4), (204, 4), (205, 4), (206, 4), (276, 2), (277, 2), (278, 2), (285, 4), (286, 4), (287, 4), (366, 2), (367, 2), (368, 2)]
theorem det00Term3Coeffs_data : det00Term3Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det00Term3Row00 det00Term3Row01) (CoefficientMerge.fastMerge det00Term3Row02 det00Term3Row03)) := by decide +kernel
theorem eval_det00Term3Coeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term3Coeffs = SparsePolynomial.eval (gapValues g) entryA02 * SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [det00Term3Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det00Term3Row00, eval_det00Term3Row01, eval_det00Term3Row02, eval_det00Term3Row03]
  generalize hq : SparsePolynomial.eval (gapValues g) det00Pair3 = v
  simp only [entryA02, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
