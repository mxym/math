import APPT.Finite9Sparse.Det03Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term4Row00 : CoefficientMerge.Poly := [(3, 2), (4, 2), (5, 2), (6, 2), (7, 2), (8, 2), (12, 2), (13, 2), (14, 2), (15, 2), (16, 2), (17, 2), (21, 2), (22, 2), (23, 2), (24, 2), (25, 2), (26, 2), (30, 2), (31, 4), (32, 4), (33, 4), (34, 2), (35, 2), (40, 2), (41, 4), (42, 4), (43, 2), (44, 2), (50, 2), (51, 4), (52, 2), (53, 2), (60, 2), (61, 2), (62, 2)]
theorem det03Term4Row00_decode : SparsePolynomial.decodeCubic 9 det03Term4Row00 = SparsePolynomial.monoTimes [0] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term4Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [0]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term4Row01 : CoefficientMerge.Poly := [(12, 2), (13, 2), (14, 2), (15, 2), (16, 2), (17, 2), (93, 2), (94, 2), (95, 2), (96, 2), (97, 2), (98, 2), (102, 2), (103, 2), (104, 2), (105, 2), (106, 2), (107, 2), (111, 2), (112, 4), (113, 4), (114, 4), (115, 2), (116, 2), (121, 2), (122, 4), (123, 4), (124, 2), (125, 2), (131, 2), (132, 4), (133, 2), (134, 2), (141, 2), (142, 2), (143, 2)]
theorem det03Term4Row01_decode : SparsePolynomial.decodeCubic 9 det03Term4Row01 = SparsePolynomial.monoTimes [1] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row01 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term4Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term4Row02 : CoefficientMerge.Poly := [(21, 2), (22, 2), (23, 2), (24, 2), (25, 2), (26, 2), (102, 2), (103, 2), (104, 2), (105, 2), (106, 2), (107, 2), (183, 2), (184, 2), (185, 2), (186, 2), (187, 2), (188, 2), (192, 2), (193, 4), (194, 4), (195, 4), (196, 2), (197, 2), (202, 2), (203, 4), (204, 4), (205, 2), (206, 2), (212, 2), (213, 4), (214, 2), (215, 2), (222, 2), (223, 2), (224, 2)]
theorem det03Term4Row02_decode : SparsePolynomial.decodeCubic 9 det03Term4Row02 = SparsePolynomial.monoTimes [2] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row02 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term4Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term4Row03 : CoefficientMerge.Poly := [(30, 2), (31, 2), (32, 2), (33, 2), (34, 2), (35, 2), (111, 2), (112, 2), (113, 2), (114, 2), (115, 2), (116, 2), (192, 2), (193, 2), (194, 2), (195, 2), (196, 2), (197, 2), (273, 2), (274, 4), (275, 4), (276, 4), (277, 2), (278, 2), (283, 2), (284, 4), (285, 4), (286, 2), (287, 2), (293, 2), (294, 4), (295, 2), (296, 2), (303, 2), (304, 2), (305, 2)]
theorem det03Term4Row03_decode : SparsePolynomial.decodeCubic 9 det03Term4Row03 = SparsePolynomial.monoTimes [3] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row03 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term4Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
