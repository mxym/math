import APPT.Finite12Sparse.Det00Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term4Row08 : CoefficientMerge.Poly := [(80, 2), (92, 2), (104, 2), (105, 2), (106, 2), (107, 2), (224, 2), (236, 2), (248, 2), (249, 2), (250, 2), (251, 2), (368, 2), (380, 2), (392, 2), (393, 2), (394, 2), (395, 2), (512, 2), (524, 2), (536, 2), (537, 2), (538, 2), (539, 2), (656, 2), (668, 2), (680, 2), (681, 2), (682, 2), (683, 2), (800, 2), (812, 2), (824, 2), (825, 2), (826, 2), (827, 2), (944, 2), (956, 4), (968, 4), (969, 4), (970, 2), (971, 2), (1100, 2), (1112, 4), (1113, 4), (1114, 2), (1115, 2), (1256, 2), (1257, 4), (1258, 2), (1259, 2), (1269, 2), (1270, 2), (1271, 2)]
theorem det00Term4Row08_decode : SparsePolynomial.decodeCubic 12 det00Term4Row08 = SparsePolynomial.monoTimes [8] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row08 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term4Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term4Row09 : CoefficientMerge.Poly := [(81, 2), (93, 2), (105, 2), (117, 2), (118, 2), (119, 2), (225, 2), (237, 2), (249, 2), (261, 2), (262, 2), (263, 2), (369, 2), (381, 2), (393, 2), (405, 2), (406, 2), (407, 2), (513, 2), (525, 2), (537, 2), (549, 2), (550, 2), (551, 2), (657, 2), (669, 2), (681, 2), (693, 2), (694, 2), (695, 2), (801, 2), (813, 2), (825, 2), (837, 2), (838, 2), (839, 2), (945, 2), (957, 4), (969, 4), (981, 4), (982, 2), (983, 2), (1101, 2), (1113, 4), (1125, 4), (1126, 2), (1127, 2), (1257, 2), (1269, 4), (1270, 2), (1271, 2), (1413, 2), (1414, 2), (1415, 2)]
theorem det00Term4Row09_decode : SparsePolynomial.decodeCubic 12 det00Term4Row09 = SparsePolynomial.monoTimes [9] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row09 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term4Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
