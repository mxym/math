import APPT.Finite9Sparse.TargetQuadratic
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def targetProductRow04 : CoefficientMerge.Poly := [(4, -520), (13, -870), (22, -700), (31, -530), (40, -360), (41, -190), (42, -20), (43, 150), (44, 320), (94, -870), (103, -1400), (112, -1060), (121, -720), (122, -380), (123, -40), (124, 300), (125, 640), (184, -1050), (193, -1590), (202, -1080), (203, -570), (204, -60), (205, 450), (206, 960), (274, -1060), (283, -1440), (284, -760), (285, -80), (286, 600), (287, 1280), (364, -900), (365, -950), (366, -100), (367, 750), (368, 1600), (374, -570), (375, -120), (376, 900), (377, 1920), (384, -70), (385, 1050), (386, 2240), (394, 600), (395, 2560), (404, 1440)]
theorem targetProductRow04_decode : SparsePolynomial.decodeCubic 9 targetProductRow04 = SparsePolynomial.monoTimes [4] (5 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow04 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow04 = (5 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def targetProductRow05 : CoefficientMerge.Poly := [(5, -624), (14, -1044), (23, -840), (32, -636), (41, -432), (50, -228), (51, -24), (52, 180), (53, 384), (95, -1044), (104, -1680), (113, -1272), (122, -864), (131, -456), (132, -48), (133, 360), (134, 768), (185, -1260), (194, -1908), (203, -1296), (212, -684), (213, -72), (214, 540), (215, 1152), (275, -1272), (284, -1728), (293, -912), (294, -96), (295, 720), (296, 1536), (365, -1080), (374, -1140), (375, -120), (376, 900), (377, 1920), (455, -684), (456, -144), (457, 1080), (458, 2304), (465, -84), (466, 1260), (467, 2688), (475, 720), (476, 3072), (485, 1728)]
theorem targetProductRow05_decode : SparsePolynomial.decodeCubic 9 targetProductRow05 = SparsePolynomial.monoTimes [5] (6 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow05 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow05 = (6 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def targetProductRow06 : CoefficientMerge.Poly := [(6, -728), (15, -1218), (24, -980), (33, -742), (42, -504), (51, -266), (60, -28), (61, 210), (62, 448), (96, -1218), (105, -1960), (114, -1484), (123, -1008), (132, -532), (141, -56), (142, 420), (143, 896), (186, -1470), (195, -2226), (204, -1512), (213, -798), (222, -84), (223, 630), (224, 1344), (276, -1484), (285, -2016), (294, -1064), (303, -112), (304, 840), (305, 1792), (366, -1260), (375, -1330), (384, -140), (385, 1050), (386, 2240), (456, -798), (465, -168), (466, 1260), (467, 2688), (546, -98), (547, 1470), (548, 3136), (556, 840), (557, 3584), (566, 2016)]
theorem targetProductRow06_decode : SparsePolynomial.decodeCubic 9 targetProductRow06 = SparsePolynomial.monoTimes [6] (7 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow06 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow06 = (7 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def targetProductRow07 : CoefficientMerge.Poly := [(7, -832), (16, -1392), (25, -1120), (34, -848), (43, -576), (52, -304), (61, -32), (70, 240), (71, 512), (97, -1392), (106, -2240), (115, -1696), (124, -1152), (133, -608), (142, -64), (151, 480), (152, 1024), (187, -1680), (196, -2544), (205, -1728), (214, -912), (223, -96), (232, 720), (233, 1536), (277, -1696), (286, -2304), (295, -1216), (304, -128), (313, 960), (314, 2048), (367, -1440), (376, -1520), (385, -160), (394, 1200), (395, 2560), (457, -912), (466, -192), (475, 1440), (476, 3072), (547, -112), (556, 1680), (557, 3584), (637, 960), (638, 4096), (647, 2304)]
theorem targetProductRow07_decode : SparsePolynomial.decodeCubic 9 targetProductRow07 = SparsePolynomial.monoTimes [7] (8 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow07 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow07 = (8 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
