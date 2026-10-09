import APPT.Finite9Sparse.Det00Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term4Row04 : CoefficientMerge.Poly := [(31, 2), (40, 2), (41, 2), (42, 2), (43, 2), (44, 2), (112, 2), (121, 2), (122, 2), (123, 2), (124, 2), (125, 2), (193, 2), (202, 2), (203, 2), (204, 2), (205, 2), (206, 2), (274, 2), (283, 4), (284, 4), (285, 4), (286, 2), (287, 2), (364, 2), (365, 4), (366, 4), (367, 2), (368, 2), (374, 2), (375, 4), (376, 2), (377, 2), (384, 2), (385, 2), (386, 2)]
theorem det00Term4Row04_decode : SparsePolynomial.decodeCubic 9 det00Term4Row04 = SparsePolynomial.monoTimes [4] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row04 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term4Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term4Row05 : CoefficientMerge.Poly := [(32, 2), (41, 2), (50, 2), (51, 2), (52, 2), (53, 2), (113, 2), (122, 2), (131, 2), (132, 2), (133, 2), (134, 2), (194, 2), (203, 2), (212, 2), (213, 2), (214, 2), (215, 2), (275, 2), (284, 4), (293, 4), (294, 4), (295, 2), (296, 2), (365, 2), (374, 4), (375, 4), (376, 2), (377, 2), (455, 2), (456, 4), (457, 2), (458, 2), (465, 2), (466, 2), (467, 2)]
theorem det00Term4Row05_decode : SparsePolynomial.decodeCubic 9 det00Term4Row05 = SparsePolynomial.monoTimes [5] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row05 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term4Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term4Row06 : CoefficientMerge.Poly := [(33, 2), (42, 2), (51, 2), (60, 2), (61, 2), (62, 2), (114, 2), (123, 2), (132, 2), (141, 2), (142, 2), (143, 2), (195, 2), (204, 2), (213, 2), (222, 2), (223, 2), (224, 2), (276, 2), (285, 4), (294, 4), (303, 4), (304, 2), (305, 2), (366, 2), (375, 4), (384, 4), (385, 2), (386, 2), (456, 2), (465, 4), (466, 2), (467, 2), (546, 2), (547, 2), (548, 2)]
theorem det00Term4Row06_decode : SparsePolynomial.decodeCubic 9 det00Term4Row06 = SparsePolynomial.monoTimes [6] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row06 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term4Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
