import APPT.Finite24Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Term3Row12 : CoefficientMerge.Poly := [(908, 2), (909, 2), (910, 2), (911, 2), (1484, 2), (1485, 2), (1486, 2), (1487, 2), (2060, 2), (2061, 2), (2062, 2), (2063, 2), (2636, 2), (2637, 2), (2638, 2), (2639, 2), (3212, 2), (3213, 2), (3214, 2), (3215, 2), (3788, 2), (3789, 2), (3790, 2), (3791, 2), (4364, 2), (4365, 2), (4366, 2), (4367, 2), (4940, 2), (4941, 2), (4942, 2), (4943, 2), (5516, 2), (5517, 2), (5518, 2), (5519, 2), (6092, 2), (6093, 2), (6094, 2), (6095, 2), (6668, 2), (6669, 2), (6670, 2), (6671, 2), (7244, 2), (7245, 2), (7246, 2), (7247, 2), (7820, 2), (7821, 2), (7822, 2), (7823, 2), (7844, 2), (7845, 2), (7846, 2), (7847, 2), (7868, 2), (7869, 2), (7870, 2), (7871, 2), (7892, 2), (7893, 2), (7894, 2), (7895, 2), (7916, 2), (7917, 2), (7918, 2), (7919, 2), (7940, 2), (7941, 2), (7942, 2), (7943, 2), (7964, 2), (7965, 2), (7966, 2), (7967, 2), (7988, 2), (7989, 2), (7990, 2), (7991, 2)]
theorem det04Term3Row12_decode : SparsePolynomial.decodeCubic 24 det04Term3Row12 = SparsePolynomial.monoTimes [13] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row12 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row12 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [13]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row12_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row13 : CoefficientMerge.Poly := [(932, 2), (933, 2), (934, 2), (935, 2), (1508, 2), (1509, 2), (1510, 2), (1511, 2), (2084, 2), (2085, 2), (2086, 2), (2087, 2), (2660, 2), (2661, 2), (2662, 2), (2663, 2), (3236, 2), (3237, 2), (3238, 2), (3239, 2), (3812, 2), (3813, 2), (3814, 2), (3815, 2), (4388, 2), (4389, 2), (4390, 2), (4391, 2), (4964, 2), (4965, 2), (4966, 2), (4967, 2), (5540, 2), (5541, 2), (5542, 2), (5543, 2), (6116, 2), (6117, 2), (6118, 2), (6119, 2), (6692, 2), (6693, 2), (6694, 2), (6695, 2), (7268, 2), (7269, 2), (7270, 2), (7271, 2), (7844, 2), (7845, 2), (7846, 2), (7847, 2), (8420, 2), (8421, 2), (8422, 2), (8423, 2), (8444, 2), (8445, 2), (8446, 2), (8447, 2), (8468, 2), (8469, 2), (8470, 2), (8471, 2), (8492, 2), (8493, 2), (8494, 2), (8495, 2), (8516, 2), (8517, 2), (8518, 2), (8519, 2), (8540, 2), (8541, 2), (8542, 2), (8543, 2), (8564, 2), (8565, 2), (8566, 2), (8567, 2)]
theorem det04Term3Row13_decode : SparsePolynomial.decodeCubic 24 det04Term3Row13 = SparsePolynomial.monoTimes [14] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row13 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row13 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [14]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row13_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row14 : CoefficientMerge.Poly := [(956, 2), (957, 2), (958, 2), (959, 2), (1532, 2), (1533, 2), (1534, 2), (1535, 2), (2108, 2), (2109, 2), (2110, 2), (2111, 2), (2684, 2), (2685, 2), (2686, 2), (2687, 2), (3260, 2), (3261, 2), (3262, 2), (3263, 2), (3836, 2), (3837, 2), (3838, 2), (3839, 2), (4412, 2), (4413, 2), (4414, 2), (4415, 2), (4988, 2), (4989, 2), (4990, 2), (4991, 2), (5564, 2), (5565, 2), (5566, 2), (5567, 2), (6140, 2), (6141, 2), (6142, 2), (6143, 2), (6716, 2), (6717, 2), (6718, 2), (6719, 2), (7292, 2), (7293, 2), (7294, 2), (7295, 2), (7868, 2), (7869, 2), (7870, 2), (7871, 2), (8444, 2), (8445, 2), (8446, 2), (8447, 2), (9020, 2), (9021, 2), (9022, 2), (9023, 2), (9044, 2), (9045, 2), (9046, 2), (9047, 2), (9068, 2), (9069, 2), (9070, 2), (9071, 2), (9092, 2), (9093, 2), (9094, 2), (9095, 2), (9116, 2), (9117, 2), (9118, 2), (9119, 2), (9140, 2), (9141, 2), (9142, 2), (9143, 2)]
theorem det04Term3Row14_decode : SparsePolynomial.decodeCubic 24 det04Term3Row14 = SparsePolynomial.monoTimes [15] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row14 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row14 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [15]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row14_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row15 : CoefficientMerge.Poly := [(980, 2), (981, 2), (982, 2), (983, 2), (1556, 2), (1557, 2), (1558, 2), (1559, 2), (2132, 2), (2133, 2), (2134, 2), (2135, 2), (2708, 2), (2709, 2), (2710, 2), (2711, 2), (3284, 2), (3285, 2), (3286, 2), (3287, 2), (3860, 2), (3861, 2), (3862, 2), (3863, 2), (4436, 2), (4437, 2), (4438, 2), (4439, 2), (5012, 2), (5013, 2), (5014, 2), (5015, 2), (5588, 2), (5589, 2), (5590, 2), (5591, 2), (6164, 2), (6165, 2), (6166, 2), (6167, 2), (6740, 2), (6741, 2), (6742, 2), (6743, 2), (7316, 2), (7317, 2), (7318, 2), (7319, 2), (7892, 2), (7893, 2), (7894, 2), (7895, 2), (8468, 2), (8469, 2), (8470, 2), (8471, 2), (9044, 2), (9045, 2), (9046, 2), (9047, 2), (9620, 2), (9621, 2), (9622, 2), (9623, 2), (9644, 2), (9645, 2), (9646, 2), (9647, 2), (9668, 2), (9669, 2), (9670, 2), (9671, 2), (9692, 2), (9693, 2), (9694, 2), (9695, 2), (9716, 2), (9717, 2), (9718, 2), (9719, 2)]
theorem det04Term3Row15_decode : SparsePolynomial.decodeCubic 24 det04Term3Row15 = SparsePolynomial.monoTimes [16] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row15 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row15 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [16]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row15_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite24
