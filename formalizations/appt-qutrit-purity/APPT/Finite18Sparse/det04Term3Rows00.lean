import APPT.Finite18Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det04Term3Row00 : CoefficientMerge.Poly := [(356, 2), (357, 2), (358, 2), (359, 2), (374, 2), (375, 2), (376, 2), (377, 2), (392, 2), (393, 2), (394, 2), (395, 2), (410, 2), (411, 2), (412, 2), (413, 2), (428, 2), (429, 2), (430, 2), (431, 2), (446, 2), (447, 2), (448, 2), (449, 2), (464, 2), (465, 2), (466, 2), (467, 2), (482, 2), (483, 2), (484, 2), (485, 2), (500, 2), (501, 2), (502, 2), (503, 2), (518, 2), (519, 2), (520, 2), (521, 2), (536, 2), (537, 2), (538, 2), (539, 2), (554, 2), (555, 2), (556, 2), (557, 2), (572, 2), (573, 2), (574, 2), (575, 2), (590, 2), (591, 2), (592, 2), (593, 2)]
theorem det04Term3Row00_decode : SparsePolynomial.decodeCubic 18 det04Term3Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row00 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row01 : CoefficientMerge.Poly := [(374, 2), (375, 2), (376, 2), (377, 2), (698, 2), (699, 2), (700, 2), (701, 2), (716, 2), (717, 2), (718, 2), (719, 2), (734, 2), (735, 2), (736, 2), (737, 2), (752, 2), (753, 2), (754, 2), (755, 2), (770, 2), (771, 2), (772, 2), (773, 2), (788, 2), (789, 2), (790, 2), (791, 2), (806, 2), (807, 2), (808, 2), (809, 2), (824, 2), (825, 2), (826, 2), (827, 2), (842, 2), (843, 2), (844, 2), (845, 2), (860, 2), (861, 2), (862, 2), (863, 2), (878, 2), (879, 2), (880, 2), (881, 2), (896, 2), (897, 2), (898, 2), (899, 2), (914, 2), (915, 2), (916, 2), (917, 2)]
theorem det04Term3Row01_decode : SparsePolynomial.decodeCubic 18 det04Term3Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row01 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row02 : CoefficientMerge.Poly := [(392, 2), (393, 2), (394, 2), (395, 2), (716, 2), (717, 2), (718, 2), (719, 2), (1040, 2), (1041, 2), (1042, 2), (1043, 2), (1058, 2), (1059, 2), (1060, 2), (1061, 2), (1076, 2), (1077, 2), (1078, 2), (1079, 2), (1094, 2), (1095, 2), (1096, 2), (1097, 2), (1112, 2), (1113, 2), (1114, 2), (1115, 2), (1130, 2), (1131, 2), (1132, 2), (1133, 2), (1148, 2), (1149, 2), (1150, 2), (1151, 2), (1166, 2), (1167, 2), (1168, 2), (1169, 2), (1184, 2), (1185, 2), (1186, 2), (1187, 2), (1202, 2), (1203, 2), (1204, 2), (1205, 2), (1220, 2), (1221, 2), (1222, 2), (1223, 2), (1238, 2), (1239, 2), (1240, 2), (1241, 2)]
theorem det04Term3Row02_decode : SparsePolynomial.decodeCubic 18 det04Term3Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row02 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row03 : CoefficientMerge.Poly := [(410, 2), (411, 2), (412, 2), (413, 2), (734, 2), (735, 2), (736, 2), (737, 2), (1058, 2), (1059, 2), (1060, 2), (1061, 2), (1382, 2), (1383, 2), (1384, 2), (1385, 2), (1400, 2), (1401, 2), (1402, 2), (1403, 2), (1418, 2), (1419, 2), (1420, 2), (1421, 2), (1436, 2), (1437, 2), (1438, 2), (1439, 2), (1454, 2), (1455, 2), (1456, 2), (1457, 2), (1472, 2), (1473, 2), (1474, 2), (1475, 2), (1490, 2), (1491, 2), (1492, 2), (1493, 2), (1508, 2), (1509, 2), (1510, 2), (1511, 2), (1526, 2), (1527, 2), (1528, 2), (1529, 2), (1544, 2), (1545, 2), (1546, 2), (1547, 2), (1562, 2), (1563, 2), (1564, 2), (1565, 2)]
theorem det04Term3Row03_decode : SparsePolynomial.decodeCubic 18 det04Term3Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row03 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite18
