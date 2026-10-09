import APPT.Finite15Sparse.det04Term5Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term5Coeffs : CoefficientMerge.Poly := [(494, 2), (509, 4), (524, 4), (539, 4), (554, 4), (569, 4), (584, 4), (599, 4), (734, 2), (749, 4), (764, 4), (779, 4), (794, 4), (809, 4), (824, 4), (974, 2), (989, 4), (1004, 4), (1019, 4), (1034, 4), (1049, 4), (1214, 2), (1229, 4), (1244, 4), (1259, 4), (1274, 4), (1454, 2), (1469, 4), (1484, 4), (1499, 4), (1694, 2), (1709, 4), (1724, 4), (1934, 2), (1949, 4), (2174, 2)]
theorem det04Term5Coeffs_data : det04Term5Coeffs = CoefficientMerge.trim det04Term5Row00 := by decide +kernel
theorem eval_det04Term5Coeffs (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term5Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det04Pair5 := by
  rw [det04Term5Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det04Term5Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det04Pair5 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite15
