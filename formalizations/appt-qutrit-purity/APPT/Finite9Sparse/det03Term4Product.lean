import APPT.Finite9Sparse.det03Term4Rows00
import APPT.Finite9Sparse.det03Term4Rows01
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term4Coeffs : CoefficientMerge.Poly := [(3, 2), (4, 2), (5, 2), (6, 2), (7, 2), (8, 2), (12, 4), (13, 4), (14, 4), (15, 4), (16, 4), (17, 4), (21, 4), (22, 4), (23, 4), (24, 4), (25, 4), (26, 4), (30, 4), (31, 8), (32, 8), (33, 8), (34, 4), (35, 4), (40, 4), (41, 8), (42, 8), (43, 4), (44, 4), (50, 4), (51, 8), (52, 4), (53, 4), (60, 4), (61, 4), (62, 4), (93, 2), (94, 2), (95, 2), (96, 2), (97, 2), (98, 2), (102, 4), (103, 4), (104, 4), (105, 4), (106, 4), (107, 4), (111, 4), (112, 8), (113, 8), (114, 8), (115, 4), (116, 4), (121, 4), (122, 8), (123, 8), (124, 4), (125, 4), (131, 4), (132, 8), (133, 4), (134, 4), (141, 4), (142, 4), (143, 4), (183, 2), (184, 2), (185, 2), (186, 2), (187, 2), (188, 2), (192, 4), (193, 8), (194, 8), (195, 8), (196, 4), (197, 4), (202, 4), (203, 8), (204, 8), (205, 4), (206, 4), (212, 4), (213, 8), (214, 4), (215, 4), (222, 4), (223, 4), (224, 4), (273, 2), (274, 6), (275, 6), (276, 6), (277, 2), (278, 2), (283, 6), (284, 12), (285, 12), (286, 4), (287, 4), (293, 6), (294, 12), (295, 4), (296, 4), (303, 6), (304, 4), (305, 4), (364, 2), (365, 6), (366, 6), (367, 2), (368, 2), (374, 6), (375, 12), (376, 4), (377, 4), (384, 6), (385, 4), (386, 4), (455, 2), (456, 6), (457, 2), (458, 2), (465, 6), (466, 4), (467, 4), (546, 2), (547, 2), (548, 2)]
theorem det03Term4Coeffs_data : det03Term4Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term4Row00 (CoefficientMerge.fastMerge det03Term4Row01 det03Term4Row02)) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term4Row03 det03Term4Row04) (CoefficientMerge.fastMerge det03Term4Row05 det03Term4Row06))) := by decide +kernel
theorem eval_det03Term4Coeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term4Coeffs = SparsePolynomial.eval (gapValues g) entryB01 * SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [det03Term4Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term4Row00, eval_det03Term4Row01, eval_det03Term4Row02, eval_det03Term4Row03, eval_det03Term4Row04, eval_det03Term4Row05, eval_det03Term4Row06]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair4 = v
  simp only [entryB01, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
