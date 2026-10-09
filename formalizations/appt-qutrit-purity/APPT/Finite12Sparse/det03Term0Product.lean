import APPT.Finite12Sparse.det03Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term0Coeffs : CoefficientMerge.Poly := [(971, 8), (983, 8), (995, 8), (1007, 8), (1115, 8), (1127, 8), (1139, 8), (1151, 8), (1259, 8), (1271, 16), (1283, 16), (1295, 16), (1415, 8), (1427, 16), (1439, 16), (1571, 8), (1583, 16), (1727, 8)]
theorem det03Term0Coeffs_data : det03Term0Coeffs = CoefficientMerge.trim det03Term0Row00 := by decide +kernel
theorem eval_det03Term0Coeffs (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term0Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det03Pair0 := by
  rw [det03Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair0 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite12
