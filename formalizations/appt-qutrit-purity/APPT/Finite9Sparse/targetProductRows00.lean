import APPT.Finite9Sparse.TargetQuadratic
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def targetProductRow00 : CoefficientMerge.Poly := [(0, -104), (1, -174), (2, -140), (3, -106), (4, -72), (5, -38), (6, -4), (7, 30), (8, 64), (10, -174), (11, -280), (12, -212), (13, -144), (14, -76), (15, -8), (16, 60), (17, 128), (20, -210), (21, -318), (22, -216), (23, -114), (24, -12), (25, 90), (26, 192), (30, -212), (31, -288), (32, -152), (33, -16), (34, 120), (35, 256), (40, -180), (41, -190), (42, -20), (43, 150), (44, 320), (50, -114), (51, -24), (52, 180), (53, 384), (60, -14), (61, 210), (62, 448), (70, 120), (71, 512), (80, 288)]
theorem targetProductRow00_decode : SparsePolynomial.decodeCubic 9 targetProductRow00 = SparsePolynomial.monoTimes [0] (1 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow00 = (1 : ℝ)*SparsePolynomial.mon (gapValues g) [0]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def targetProductRow01 : CoefficientMerge.Poly := [(1, -208), (10, -348), (11, -280), (12, -212), (13, -144), (14, -76), (15, -8), (16, 60), (17, 128), (91, -348), (92, -560), (93, -424), (94, -288), (95, -152), (96, -16), (97, 120), (98, 256), (101, -420), (102, -636), (103, -432), (104, -228), (105, -24), (106, 180), (107, 384), (111, -424), (112, -576), (113, -304), (114, -32), (115, 240), (116, 512), (121, -360), (122, -380), (123, -40), (124, 300), (125, 640), (131, -228), (132, -48), (133, 360), (134, 768), (141, -28), (142, 420), (143, 896), (151, 240), (152, 1024), (161, 576)]
theorem targetProductRow01_decode : SparsePolynomial.decodeCubic 9 targetProductRow01 = SparsePolynomial.monoTimes [1] (2 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow01 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow01 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def targetProductRow02 : CoefficientMerge.Poly := [(2, -312), (11, -522), (20, -420), (21, -318), (22, -216), (23, -114), (24, -12), (25, 90), (26, 192), (92, -522), (101, -840), (102, -636), (103, -432), (104, -228), (105, -24), (106, 180), (107, 384), (182, -630), (183, -954), (184, -648), (185, -342), (186, -36), (187, 270), (188, 576), (192, -636), (193, -864), (194, -456), (195, -48), (196, 360), (197, 768), (202, -540), (203, -570), (204, -60), (205, 450), (206, 960), (212, -342), (213, -72), (214, 540), (215, 1152), (222, -42), (223, 630), (224, 1344), (232, 360), (233, 1536), (242, 864)]
theorem targetProductRow02_decode : SparsePolynomial.decodeCubic 9 targetProductRow02 = SparsePolynomial.monoTimes [2] (3 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow02 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow02 = (3 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def targetProductRow03 : CoefficientMerge.Poly := [(3, -416), (12, -696), (21, -560), (30, -424), (31, -288), (32, -152), (33, -16), (34, 120), (35, 256), (93, -696), (102, -1120), (111, -848), (112, -576), (113, -304), (114, -32), (115, 240), (116, 512), (183, -840), (192, -1272), (193, -864), (194, -456), (195, -48), (196, 360), (197, 768), (273, -848), (274, -1152), (275, -608), (276, -64), (277, 480), (278, 1024), (283, -720), (284, -760), (285, -80), (286, 600), (287, 1280), (293, -456), (294, -96), (295, 720), (296, 1536), (303, -56), (304, 840), (305, 1792), (313, 480), (314, 2048), (323, 1152)]
theorem targetProductRow03_decode : SparsePolynomial.decodeCubic 9 targetProductRow03 = SparsePolynomial.monoTimes [3] (4 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow03 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow03 = (4 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
