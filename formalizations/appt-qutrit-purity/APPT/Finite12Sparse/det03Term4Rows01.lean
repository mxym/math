import APPT.Finite12Sparse.Det03Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term4Row04 : CoefficientMerge.Poly := [(54, 2), (55, 2), (56, 2), (57, 2), (58, 2), (59, 2), (198, 2), (199, 2), (200, 2), (201, 2), (202, 2), (203, 2), (342, 2), (343, 2), (344, 2), (345, 2), (346, 2), (347, 2), (486, 2), (487, 2), (488, 2), (489, 2), (490, 2), (491, 2), (630, 2), (631, 2), (632, 2), (633, 2), (634, 2), (635, 2), (642, 2), (643, 2), (644, 2), (645, 2), (646, 2), (647, 2), (654, 2), (655, 4), (656, 4), (657, 4), (658, 2), (659, 2), (667, 2), (668, 4), (669, 4), (670, 2), (671, 2), (680, 2), (681, 4), (682, 2), (683, 2), (693, 2), (694, 2), (695, 2)]
theorem det03Term4Row04_decode : SparsePolynomial.decodeCubic 12 det03Term4Row04 = SparsePolynomial.monoTimes [4] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row04 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term4Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term4Row05 : CoefficientMerge.Poly := [(66, 2), (67, 2), (68, 2), (69, 2), (70, 2), (71, 2), (210, 2), (211, 2), (212, 2), (213, 2), (214, 2), (215, 2), (354, 2), (355, 2), (356, 2), (357, 2), (358, 2), (359, 2), (498, 2), (499, 2), (500, 2), (501, 2), (502, 2), (503, 2), (642, 2), (643, 2), (644, 2), (645, 2), (646, 2), (647, 2), (786, 2), (787, 2), (788, 2), (789, 2), (790, 2), (791, 2), (798, 2), (799, 4), (800, 4), (801, 4), (802, 2), (803, 2), (811, 2), (812, 4), (813, 4), (814, 2), (815, 2), (824, 2), (825, 4), (826, 2), (827, 2), (837, 2), (838, 2), (839, 2)]
theorem det03Term4Row05_decode : SparsePolynomial.decodeCubic 12 det03Term4Row05 = SparsePolynomial.monoTimes [5] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row05 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term4Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term4Row06 : CoefficientMerge.Poly := [(78, 2), (79, 2), (80, 2), (81, 2), (82, 2), (83, 2), (222, 2), (223, 2), (224, 2), (225, 2), (226, 2), (227, 2), (366, 2), (367, 2), (368, 2), (369, 2), (370, 2), (371, 2), (510, 2), (511, 2), (512, 2), (513, 2), (514, 2), (515, 2), (654, 2), (655, 2), (656, 2), (657, 2), (658, 2), (659, 2), (798, 2), (799, 2), (800, 2), (801, 2), (802, 2), (803, 2), (942, 2), (943, 4), (944, 4), (945, 4), (946, 2), (947, 2), (955, 2), (956, 4), (957, 4), (958, 2), (959, 2), (968, 2), (969, 4), (970, 2), (971, 2), (981, 2), (982, 2), (983, 2)]
theorem det03Term4Row06_decode : SparsePolynomial.decodeCubic 12 det03Term4Row06 = SparsePolynomial.monoTimes [6] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row06 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term4Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term4Row07 : CoefficientMerge.Poly := [(79, 2), (91, 2), (92, 2), (93, 2), (94, 2), (95, 2), (223, 2), (235, 2), (236, 2), (237, 2), (238, 2), (239, 2), (367, 2), (379, 2), (380, 2), (381, 2), (382, 2), (383, 2), (511, 2), (523, 2), (524, 2), (525, 2), (526, 2), (527, 2), (655, 2), (667, 2), (668, 2), (669, 2), (670, 2), (671, 2), (799, 2), (811, 2), (812, 2), (813, 2), (814, 2), (815, 2), (943, 2), (955, 4), (956, 4), (957, 4), (958, 2), (959, 2), (1099, 2), (1100, 4), (1101, 4), (1102, 2), (1103, 2), (1112, 2), (1113, 4), (1114, 2), (1115, 2), (1125, 2), (1126, 2), (1127, 2)]
theorem det03Term4Row07_decode : SparsePolynomial.decodeCubic 12 det03Term4Row07 = SparsePolynomial.monoTimes [7] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row07 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term4Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
