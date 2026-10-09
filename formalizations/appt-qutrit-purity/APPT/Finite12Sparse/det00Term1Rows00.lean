import APPT.Finite12Sparse.Det00Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term1Row00 : CoefficientMerge.Poly := [(14, -1), (15, -1), (16, -1), (17, -1), (18, -1), (26, -1), (27, -2), (28, -2), (29, -2), (30, -2), (31, -1), (39, -1), (40, -2), (41, -2), (42, -2), (43, -1), (52, -1), (53, -2), (54, -2), (55, -1), (65, -1), (66, -2), (67, -1), (78, -1), (79, -1)]
theorem det00Term1Row00_decode : SparsePolynomial.decodeCubic 12 det00Term1Row00 = SparsePolynomial.monoTimes [0] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row00 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [0]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row01 : CoefficientMerge.Poly := [(158, -1), (159, -1), (160, -1), (161, -1), (162, -1), (170, -1), (171, -2), (172, -2), (173, -2), (174, -2), (175, -1), (183, -1), (184, -2), (185, -2), (186, -2), (187, -1), (196, -1), (197, -2), (198, -2), (199, -1), (209, -1), (210, -2), (211, -1), (222, -1), (223, -1)]
theorem det00Term1Row01_decode : SparsePolynomial.decodeCubic 12 det00Term1Row01 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row01 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row02 : CoefficientMerge.Poly := [(170, -1), (171, -1), (172, -1), (173, -1), (174, -1), (314, -1), (315, -2), (316, -2), (317, -2), (318, -2), (319, -1), (327, -1), (328, -2), (329, -2), (330, -2), (331, -1), (340, -1), (341, -2), (342, -2), (343, -1), (353, -1), (354, -2), (355, -1), (366, -1), (367, -1)]
theorem det00Term1Row02_decode : SparsePolynomial.decodeCubic 12 det00Term1Row02 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row02 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row03 : CoefficientMerge.Poly := [(171, -1), (183, -1), (184, -1), (185, -1), (186, -1), (315, -1), (327, -2), (328, -2), (329, -2), (330, -2), (331, -1), (471, -1), (472, -2), (473, -2), (474, -2), (475, -1), (484, -1), (485, -2), (486, -2), (487, -1), (497, -1), (498, -2), (499, -1), (510, -1), (511, -1)]
theorem det00Term1Row03_decode : SparsePolynomial.decodeCubic 12 det00Term1Row03 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row03 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
