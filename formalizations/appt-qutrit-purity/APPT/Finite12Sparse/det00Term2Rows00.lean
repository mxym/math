import APPT.Finite12Sparse.Det00Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term2Row00 : CoefficientMerge.Poly := [(14, -1), (15, -1), (16, -1), (17, -1), (18, -1), (158, -1), (159, -1), (160, -1), (161, -1), (162, -1), (170, -1), (171, -2), (172, -2), (173, -2), (174, -2), (175, -1), (176, -1), (177, -1), (183, -1), (184, -2), (185, -2), (186, -2), (187, -1), (188, -1), (189, -1), (196, -1), (197, -2), (198, -2), (199, -1), (200, -1), (201, -1), (209, -1), (210, -2), (211, -1), (212, -1), (213, -1), (222, -1), (223, -1), (224, -1), (225, -1)]
theorem det00Term2Row00_decode : SparsePolynomial.decodeCubic 12 det00Term2Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row00 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term2Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row01 : CoefficientMerge.Poly := [(26, -1), (27, -1), (28, -1), (29, -1), (30, -1), (170, -1), (171, -1), (172, -1), (173, -1), (174, -1), (314, -1), (315, -2), (316, -2), (317, -2), (318, -2), (319, -1), (320, -1), (321, -1), (327, -1), (328, -2), (329, -2), (330, -2), (331, -1), (332, -1), (333, -1), (340, -1), (341, -2), (342, -2), (343, -1), (344, -1), (345, -1), (353, -1), (354, -2), (355, -1), (356, -1), (357, -1), (366, -1), (367, -1), (368, -1), (369, -1)]
theorem det00Term2Row01_decode : SparsePolynomial.decodeCubic 12 det00Term2Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row01 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term2Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row02 : CoefficientMerge.Poly := [(27, -1), (39, -1), (40, -1), (41, -1), (42, -1), (171, -1), (183, -1), (184, -1), (185, -1), (186, -1), (315, -1), (327, -2), (328, -2), (329, -2), (330, -2), (331, -1), (332, -1), (333, -1), (471, -1), (472, -2), (473, -2), (474, -2), (475, -1), (476, -1), (477, -1), (484, -1), (485, -2), (486, -2), (487, -1), (488, -1), (489, -1), (497, -1), (498, -2), (499, -1), (500, -1), (501, -1), (510, -1), (511, -1), (512, -1), (513, -1)]
theorem det00Term2Row02_decode : SparsePolynomial.decodeCubic 12 det00Term2Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row02 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term2Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row03 : CoefficientMerge.Poly := [(28, -1), (40, -1), (52, -1), (53, -1), (54, -1), (172, -1), (184, -1), (196, -1), (197, -1), (198, -1), (316, -1), (328, -2), (340, -2), (341, -2), (342, -2), (343, -1), (344, -1), (345, -1), (472, -1), (484, -2), (485, -2), (486, -2), (487, -1), (488, -1), (489, -1), (628, -1), (629, -2), (630, -2), (631, -1), (632, -1), (633, -1), (641, -1), (642, -2), (643, -1), (644, -1), (645, -1), (654, -1), (655, -1), (656, -1), (657, -1)]
theorem det00Term2Row03_decode : SparsePolynomial.decodeCubic 12 det00Term2Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row03 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term2Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
