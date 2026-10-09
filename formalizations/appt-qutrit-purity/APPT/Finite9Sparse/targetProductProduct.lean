import APPT.Finite9Sparse.targetProductRows00
import APPT.Finite9Sparse.targetProductRows01
import APPT.Finite9Sparse.targetProductRows02
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def targetProductCoeffs : CoefficientMerge.Poly := [(0, -104), (1, -382), (2, -452), (3, -522), (4, -592), (5, -662), (6, -732), (7, -802), (8, -872), (10, -522), (11, -1082), (12, -1120), (13, -1158), (14, -1196), (15, -1234), (16, -1272), (17, -1310), (20, -630), (21, -1196), (22, -1132), (23, -1068), (24, -1004), (25, -940), (26, -876), (30, -636), (31, -1106), (32, -940), (33, -774), (34, -608), (35, -442), (40, -540), (41, -812), (42, -544), (43, -276), (44, -8), (50, -342), (51, -314), (52, 56), (53, 426), (60, -42), (61, 388), (62, 860), (70, 360), (71, 1294), (80, 864), (91, -348), (92, -1082), (93, -1120), (94, -1158), (95, -1196), (96, -1234), (97, -1272), (98, -1310), (101, -1260), (102, -2392), (103, -2264), (104, -2136), (105, -2008), (106, -1880), (107, -1752), (111, -1272), (112, -2212), (113, -1880), (114, -1548), (115, -1216), (116, -884), (121, -1080), (122, -1624), (123, -1088), (124, -552), (125, -16), (131, -684), (132, -628), (133, 112), (134, 852), (141, -84), (142, 776), (143, 1720), (151, 720), (152, 2588), (161, 1728), (182, -630), (183, -1794), (184, -1698), (185, -1602), (186, -1506), (187, -1410), (188, -1314), (192, -1908), (193, -3318), (194, -2820), (195, -2322), (196, -1824), (197, -1326), (202, -1620), (203, -2436), (204, -1632), (205, -828), (206, -24), (212, -1026), (213, -942), (214, 168), (215, 1278), (222, -126), (223, 1164), (224, 2580), (232, 1080), (233, 3882), (242, 2592), (273, -848), (274, -2212), (275, -1880), (276, -1548), (277, -1216), (278, -884), (283, -2160), (284, -3248), (285, -2176), (286, -1104), (287, -32), (293, -1368), (294, -1256), (295, 224), (296, 1704), (303, -168), (304, 1552), (305, 3440), (313, 1440), (314, 5176), (323, 3456), (364, -900), (365, -2030), (366, -1360), (367, -690), (368, -20), (374, -1710), (375, -1570), (376, 280), (377, 2130), (384, -210), (385, 1940), (386, 4300), (394, 1800), (395, 6470), (404, 4320), (455, -684), (456, -942), (457, 168), (458, 1278), (465, -252), (466, 2328), (467, 5160), (475, 2160), (476, 7764), (485, 5184), (546, -98), (547, 1358), (548, 3010), (556, 2520), (557, 9058), (566, 6048), (637, 960), (638, 5176), (647, 6912), (728, 2592)]
theorem targetProductCoeffs_data : targetProductCoeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge targetProductRow00 targetProductRow01) (CoefficientMerge.fastMerge targetProductRow02 targetProductRow03)) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge targetProductRow04 targetProductRow05) (CoefficientMerge.fastMerge targetProductRow06 (CoefficientMerge.fastMerge targetProductRow07 targetProductRow08)))) := by decide +kernel
theorem eval_targetProductCoeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductCoeffs = SparsePolynomial.eval (gapValues g) polyTotal * SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [targetProductCoeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_targetProductRow00, eval_targetProductRow01, eval_targetProductRow02, eval_targetProductRow03, eval_targetProductRow04, eval_targetProductRow05, eval_targetProductRow06, eval_targetProductRow07, eval_targetProductRow08]
  generalize hq : SparsePolynomial.eval (gapValues g) targetQuadratic = v
  simp only [polyTotal, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
