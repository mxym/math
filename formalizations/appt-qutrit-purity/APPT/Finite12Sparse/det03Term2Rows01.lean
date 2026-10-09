import APPT.Finite12Sparse.Det03Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term2Row04 : CoefficientMerge.Poly := [(29, -1), (41, -1), (53, -1), (65, -1), (66, -1), (173, -1), (185, -1), (197, -1), (209, -1), (210, -1), (317, -1), (329, -2), (341, -2), (353, -2), (354, -2), (355, -1), (356, -1), (357, -1), (473, -1), (485, -2), (497, -2), (498, -2), (499, -1), (500, -1), (501, -1), (629, -1), (641, -2), (642, -2), (643, -1), (644, -1), (645, -1), (785, -1), (786, -2), (787, -1), (788, -1), (789, -1), (798, -1), (799, -1), (800, -1), (801, -1)]
theorem det03Term2Row04_decode : SparsePolynomial.decodeCubic 12 det03Term2Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row04 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term2Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term2Row05 : CoefficientMerge.Poly := [(30, -1), (42, -1), (54, -1), (66, -1), (78, -1), (174, -1), (186, -1), (198, -1), (210, -1), (222, -1), (318, -1), (330, -2), (342, -2), (354, -2), (366, -2), (367, -1), (368, -1), (369, -1), (474, -1), (486, -2), (498, -2), (510, -2), (511, -1), (512, -1), (513, -1), (630, -1), (642, -2), (654, -2), (655, -1), (656, -1), (657, -1), (786, -1), (798, -2), (799, -1), (800, -1), (801, -1), (942, -1), (943, -1), (944, -1), (945, -1)]
theorem det03Term2Row05_decode : SparsePolynomial.decodeCubic 12 det03Term2Row05 = SparsePolynomial.monoTimes [6] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row05 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term2Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term2Row06 : CoefficientMerge.Poly := [(31, -1), (43, -1), (55, -1), (67, -1), (79, -1), (175, -1), (187, -1), (199, -1), (211, -1), (223, -1), (319, -1), (331, -2), (343, -2), (355, -2), (367, -2), (379, -1), (380, -1), (381, -1), (475, -1), (487, -2), (499, -2), (511, -2), (523, -1), (524, -1), (525, -1), (631, -1), (643, -2), (655, -2), (667, -1), (668, -1), (669, -1), (787, -1), (799, -2), (811, -1), (812, -1), (813, -1), (943, -1), (955, -1), (956, -1), (957, -1)]
theorem det03Term2Row06_decode : SparsePolynomial.decodeCubic 12 det03Term2Row06 = SparsePolynomial.monoTimes [7] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row06 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term2Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term2Row07 : CoefficientMerge.Poly := [(32, -1), (44, -1), (56, -1), (68, -1), (80, -1), (176, -1), (188, -1), (200, -1), (212, -1), (224, -1), (320, -1), (332, -2), (344, -2), (356, -2), (368, -2), (380, -1), (392, -1), (393, -1), (476, -1), (488, -2), (500, -2), (512, -2), (524, -1), (536, -1), (537, -1), (632, -1), (644, -2), (656, -2), (668, -1), (680, -1), (681, -1), (788, -1), (800, -2), (812, -1), (824, -1), (825, -1), (944, -1), (956, -1), (968, -1), (969, -1)]
theorem det03Term2Row07_decode : SparsePolynomial.decodeCubic 12 det03Term2Row07 = SparsePolynomial.monoTimes [8] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row07 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term2Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
