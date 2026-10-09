import APPT.Finite15Sparse.det00Term3Rows00
import APPT.Finite15Sparse.det00Term3Rows01
import APPT.Finite15Sparse.det00Term3Rows02
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term3Coeffs : CoefficientMerge.Poly := [(252, 2), (253, 2), (254, 2), (267, 4), (268, 4), (269, 4), (282, 4), (283, 4), (284, 4), (297, 4), (298, 4), (299, 4), (312, 4), (313, 4), (314, 4), (327, 4), (328, 4), (329, 4), (342, 4), (343, 4), (344, 4), (357, 4), (358, 4), (359, 4), (372, 4), (373, 4), (374, 4), (387, 4), (388, 4), (389, 4), (492, 2), (493, 2), (494, 2), (507, 4), (508, 4), (509, 4), (522, 4), (523, 4), (524, 4), (537, 4), (538, 4), (539, 4), (552, 4), (553, 4), (554, 4), (567, 4), (568, 4), (569, 4), (582, 4), (583, 4), (584, 4), (597, 4), (598, 4), (599, 4), (612, 4), (613, 4), (614, 4), (732, 2), (733, 2), (734, 2), (747, 4), (748, 4), (749, 4), (762, 4), (763, 4), (764, 4), (777, 4), (778, 4), (779, 4), (792, 4), (793, 4), (794, 4), (807, 4), (808, 4), (809, 4), (822, 4), (823, 4), (824, 4), (837, 4), (838, 4), (839, 4), (972, 2), (973, 2), (974, 2), (987, 4), (988, 4), (989, 4), (1002, 4), (1003, 4), (1004, 4), (1017, 4), (1018, 4), (1019, 4), (1032, 4), (1033, 4), (1034, 4), (1047, 4), (1048, 4), (1049, 4), (1062, 4), (1063, 4), (1064, 4), (1212, 2), (1213, 2), (1214, 2), (1227, 4), (1228, 4), (1229, 4), (1242, 4), (1243, 4), (1244, 4), (1257, 4), (1258, 4), (1259, 4), (1272, 4), (1273, 4), (1274, 4), (1287, 4), (1288, 4), (1289, 4), (1452, 2), (1453, 2), (1454, 2), (1467, 4), (1468, 4), (1469, 4), (1482, 4), (1483, 4), (1484, 4), (1497, 4), (1498, 4), (1499, 4), (1512, 4), (1513, 4), (1514, 4), (1692, 2), (1693, 2), (1694, 2), (1707, 4), (1708, 4), (1709, 4), (1722, 4), (1723, 4), (1724, 4), (1737, 4), (1738, 4), (1739, 4), (1932, 2), (1933, 2), (1934, 2), (1947, 4), (1948, 4), (1949, 4), (1962, 4), (1963, 4), (1964, 4), (2172, 2), (2173, 2), (2174, 2), (2187, 4), (2188, 4), (2189, 4), (2412, 2), (2413, 2), (2414, 2)]
theorem det00Term3Coeffs_data : det00Term3Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det00Term3Row00 det00Term3Row01) (CoefficientMerge.fastMerge det00Term3Row02 (CoefficientMerge.fastMerge det00Term3Row03 det00Term3Row04))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det00Term3Row05 det00Term3Row06) (CoefficientMerge.fastMerge det00Term3Row07 (CoefficientMerge.fastMerge det00Term3Row08 det00Term3Row09)))) := by decide +kernel
theorem eval_det00Term3Coeffs (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term3Coeffs = SparsePolynomial.eval (gapValues g) entryA02 * SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [det00Term3Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det00Term3Row00, eval_det00Term3Row01, eval_det00Term3Row02, eval_det00Term3Row03, eval_det00Term3Row04, eval_det00Term3Row05, eval_det00Term3Row06, eval_det00Term3Row07, eval_det00Term3Row08, eval_det00Term3Row09]
  generalize hq : SparsePolynomial.eval (gapValues g) det00Pair3 = v
  simp only [entryA02, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite15
