import APPT.Finite24Sparse.det04Term5Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Term5Coeffs : CoefficientMerge.Poly := [(1223, 2), (1247, 4), (1271, 4), (1295, 4), (1319, 4), (1343, 4), (1367, 4), (1391, 4), (1415, 4), (1439, 4), (1463, 4), (1487, 4), (1511, 4), (1535, 4), (1559, 4), (1583, 4), (1607, 4), (1823, 2), (1847, 4), (1871, 4), (1895, 4), (1919, 4), (1943, 4), (1967, 4), (1991, 4), (2015, 4), (2039, 4), (2063, 4), (2087, 4), (2111, 4), (2135, 4), (2159, 4), (2183, 4), (2423, 2), (2447, 4), (2471, 4), (2495, 4), (2519, 4), (2543, 4), (2567, 4), (2591, 4), (2615, 4), (2639, 4), (2663, 4), (2687, 4), (2711, 4), (2735, 4), (2759, 4), (3023, 2), (3047, 4), (3071, 4), (3095, 4), (3119, 4), (3143, 4), (3167, 4), (3191, 4), (3215, 4), (3239, 4), (3263, 4), (3287, 4), (3311, 4), (3335, 4), (3623, 2), (3647, 4), (3671, 4), (3695, 4), (3719, 4), (3743, 4), (3767, 4), (3791, 4), (3815, 4), (3839, 4), (3863, 4), (3887, 4), (3911, 4), (4223, 2), (4247, 4), (4271, 4), (4295, 4), (4319, 4), (4343, 4), (4367, 4), (4391, 4), (4415, 4), (4439, 4), (4463, 4), (4487, 4), (4823, 2), (4847, 4), (4871, 4), (4895, 4), (4919, 4), (4943, 4), (4967, 4), (4991, 4), (5015, 4), (5039, 4), (5063, 4), (5423, 2), (5447, 4), (5471, 4), (5495, 4), (5519, 4), (5543, 4), (5567, 4), (5591, 4), (5615, 4), (5639, 4), (6023, 2), (6047, 4), (6071, 4), (6095, 4), (6119, 4), (6143, 4), (6167, 4), (6191, 4), (6215, 4), (6623, 2), (6647, 4), (6671, 4), (6695, 4), (6719, 4), (6743, 4), (6767, 4), (6791, 4), (7223, 2), (7247, 4), (7271, 4), (7295, 4), (7319, 4), (7343, 4), (7367, 4), (7823, 2), (7847, 4), (7871, 4), (7895, 4), (7919, 4), (7943, 4), (8423, 2), (8447, 4), (8471, 4), (8495, 4), (8519, 4), (9023, 2), (9047, 4), (9071, 4), (9095, 4), (9623, 2), (9647, 4), (9671, 4), (10223, 2), (10247, 4), (10823, 2)]
theorem det04Term5Coeffs_data : det04Term5Coeffs = CoefficientMerge.trim det04Term5Row00 := by decide +kernel
theorem eval_det04Term5Coeffs (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term5Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det04Pair5 := by
  rw [det04Term5Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det04Term5Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det04Pair5 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite24
