import APPT.Finite18Sparse.det04Term5Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det04Term5Coeffs : CoefficientMerge.Poly := [(701, 2), (719, 4), (737, 4), (755, 4), (773, 4), (791, 4), (809, 4), (827, 4), (845, 4), (863, 4), (881, 4), (1043, 2), (1061, 4), (1079, 4), (1097, 4), (1115, 4), (1133, 4), (1151, 4), (1169, 4), (1187, 4), (1205, 4), (1385, 2), (1403, 4), (1421, 4), (1439, 4), (1457, 4), (1475, 4), (1493, 4), (1511, 4), (1529, 4), (1727, 2), (1745, 4), (1763, 4), (1781, 4), (1799, 4), (1817, 4), (1835, 4), (1853, 4), (2069, 2), (2087, 4), (2105, 4), (2123, 4), (2141, 4), (2159, 4), (2177, 4), (2411, 2), (2429, 4), (2447, 4), (2465, 4), (2483, 4), (2501, 4), (2753, 2), (2771, 4), (2789, 4), (2807, 4), (2825, 4), (3095, 2), (3113, 4), (3131, 4), (3149, 4), (3437, 2), (3455, 4), (3473, 4), (3779, 2), (3797, 4), (4121, 2)]
theorem det04Term5Coeffs_data : det04Term5Coeffs = CoefficientMerge.trim det04Term5Row00 := by decide +kernel
theorem eval_det04Term5Coeffs (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term5Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det04Pair5 := by
  rw [det04Term5Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det04Term5Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det04Pair5 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite18
