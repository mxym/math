import APPT.Finite18Sparse.Det00Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det00Term4Row00 : CoefficientMerge.Poly := [(12, 2), (13, 2), (14, 2), (15, 2), (16, 2), (17, 2), (30, 2), (31, 2), (32, 2), (33, 2), (34, 2), (35, 2), (48, 2), (49, 2), (50, 2), (51, 2), (52, 2), (53, 2), (66, 2), (67, 2), (68, 2), (69, 2), (70, 2), (71, 2), (84, 2), (85, 2), (86, 2), (87, 2), (88, 2), (89, 2), (102, 2), (103, 2), (104, 2), (105, 2), (106, 2), (107, 2), (120, 2), (121, 2), (122, 2), (123, 2), (124, 2), (125, 2), (138, 2), (139, 2), (140, 2), (141, 2), (142, 2), (143, 2), (156, 2), (157, 2), (158, 2), (159, 2), (160, 2), (161, 2), (174, 2), (175, 2), (176, 2), (177, 2), (178, 2), (179, 2), (192, 2), (193, 2), (194, 2), (195, 2), (196, 2), (197, 2), (210, 2), (211, 2), (212, 2), (213, 2), (214, 2), (215, 2), (228, 2), (229, 4), (230, 4), (231, 4), (232, 2), (233, 2), (247, 2), (248, 4), (249, 4), (250, 2), (251, 2), (266, 2), (267, 4), (268, 2), (269, 2), (285, 2), (286, 2), (287, 2)]
theorem det00Term4Row00_decode : SparsePolynomial.decodeCubic 18 det00Term4Row00 = SparsePolynomial.monoTimes [0] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row00 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term4Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [0]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term4Row01 : CoefficientMerge.Poly := [(30, 2), (31, 2), (32, 2), (33, 2), (34, 2), (35, 2), (354, 2), (355, 2), (356, 2), (357, 2), (358, 2), (359, 2), (372, 2), (373, 2), (374, 2), (375, 2), (376, 2), (377, 2), (390, 2), (391, 2), (392, 2), (393, 2), (394, 2), (395, 2), (408, 2), (409, 2), (410, 2), (411, 2), (412, 2), (413, 2), (426, 2), (427, 2), (428, 2), (429, 2), (430, 2), (431, 2), (444, 2), (445, 2), (446, 2), (447, 2), (448, 2), (449, 2), (462, 2), (463, 2), (464, 2), (465, 2), (466, 2), (467, 2), (480, 2), (481, 2), (482, 2), (483, 2), (484, 2), (485, 2), (498, 2), (499, 2), (500, 2), (501, 2), (502, 2), (503, 2), (516, 2), (517, 2), (518, 2), (519, 2), (520, 2), (521, 2), (534, 2), (535, 2), (536, 2), (537, 2), (538, 2), (539, 2), (552, 2), (553, 4), (554, 4), (555, 4), (556, 2), (557, 2), (571, 2), (572, 4), (573, 4), (574, 2), (575, 2), (590, 2), (591, 4), (592, 2), (593, 2), (609, 2), (610, 2), (611, 2)]
theorem det00Term4Row01_decode : SparsePolynomial.decodeCubic 18 det00Term4Row01 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row01 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term4Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term4Row02 : CoefficientMerge.Poly := [(48, 2), (49, 2), (50, 2), (51, 2), (52, 2), (53, 2), (372, 2), (373, 2), (374, 2), (375, 2), (376, 2), (377, 2), (696, 2), (697, 2), (698, 2), (699, 2), (700, 2), (701, 2), (714, 2), (715, 2), (716, 2), (717, 2), (718, 2), (719, 2), (732, 2), (733, 2), (734, 2), (735, 2), (736, 2), (737, 2), (750, 2), (751, 2), (752, 2), (753, 2), (754, 2), (755, 2), (768, 2), (769, 2), (770, 2), (771, 2), (772, 2), (773, 2), (786, 2), (787, 2), (788, 2), (789, 2), (790, 2), (791, 2), (804, 2), (805, 2), (806, 2), (807, 2), (808, 2), (809, 2), (822, 2), (823, 2), (824, 2), (825, 2), (826, 2), (827, 2), (840, 2), (841, 2), (842, 2), (843, 2), (844, 2), (845, 2), (858, 2), (859, 2), (860, 2), (861, 2), (862, 2), (863, 2), (876, 2), (877, 4), (878, 4), (879, 4), (880, 2), (881, 2), (895, 2), (896, 4), (897, 4), (898, 2), (899, 2), (914, 2), (915, 4), (916, 2), (917, 2), (933, 2), (934, 2), (935, 2)]
theorem det00Term4Row02_decode : SparsePolynomial.decodeCubic 18 det00Term4Row02 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row02 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term4Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term4Row03 : CoefficientMerge.Poly := [(66, 2), (67, 2), (68, 2), (69, 2), (70, 2), (71, 2), (390, 2), (391, 2), (392, 2), (393, 2), (394, 2), (395, 2), (714, 2), (715, 2), (716, 2), (717, 2), (718, 2), (719, 2), (1038, 2), (1039, 2), (1040, 2), (1041, 2), (1042, 2), (1043, 2), (1056, 2), (1057, 2), (1058, 2), (1059, 2), (1060, 2), (1061, 2), (1074, 2), (1075, 2), (1076, 2), (1077, 2), (1078, 2), (1079, 2), (1092, 2), (1093, 2), (1094, 2), (1095, 2), (1096, 2), (1097, 2), (1110, 2), (1111, 2), (1112, 2), (1113, 2), (1114, 2), (1115, 2), (1128, 2), (1129, 2), (1130, 2), (1131, 2), (1132, 2), (1133, 2), (1146, 2), (1147, 2), (1148, 2), (1149, 2), (1150, 2), (1151, 2), (1164, 2), (1165, 2), (1166, 2), (1167, 2), (1168, 2), (1169, 2), (1182, 2), (1183, 2), (1184, 2), (1185, 2), (1186, 2), (1187, 2), (1200, 2), (1201, 4), (1202, 4), (1203, 4), (1204, 2), (1205, 2), (1219, 2), (1220, 4), (1221, 4), (1222, 2), (1223, 2), (1238, 2), (1239, 4), (1240, 2), (1241, 2), (1257, 2), (1258, 2), (1259, 2)]
theorem det00Term4Row03_decode : SparsePolynomial.decodeCubic 18 det00Term4Row03 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row03 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term4Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite18
