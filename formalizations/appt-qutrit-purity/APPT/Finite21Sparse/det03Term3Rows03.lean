import APPT.Finite21Sparse.Det03Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det03Term3Row12 : CoefficientMerge.Poly := [(731, 2), (732, 2), (733, 2), (734, 2), (1172, 2), (1173, 2), (1174, 2), (1175, 2), (1613, 2), (1614, 2), (1615, 2), (1616, 2), (2054, 2), (2055, 2), (2056, 2), (2057, 2), (2495, 2), (2496, 2), (2497, 2), (2498, 2), (2936, 2), (2937, 2), (2938, 2), (2939, 2), (3377, 2), (3378, 2), (3379, 2), (3380, 2), (3818, 2), (3819, 2), (3820, 2), (3821, 2), (4259, 2), (4260, 2), (4261, 2), (4262, 2), (4700, 2), (4701, 2), (4702, 2), (4703, 2), (5141, 2), (5142, 2), (5143, 2), (5144, 2), (5582, 2), (5583, 2), (5584, 2), (5585, 2), (6023, 2), (6024, 2), (6025, 2), (6026, 2), (6044, 2), (6045, 2), (6046, 2), (6047, 2), (6065, 2), (6066, 2), (6067, 2), (6068, 2), (6086, 2), (6087, 2), (6088, 2), (6089, 2), (6107, 2), (6108, 2), (6109, 2), (6110, 2)]
theorem det03Term3Row12_decode : SparsePolynomial.decodeCubic 21 det03Term3Row12 = SparsePolynomial.monoTimes [13] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row12 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row12 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [13]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row12_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row13 : CoefficientMerge.Poly := [(752, 2), (753, 2), (754, 2), (755, 2), (1193, 2), (1194, 2), (1195, 2), (1196, 2), (1634, 2), (1635, 2), (1636, 2), (1637, 2), (2075, 2), (2076, 2), (2077, 2), (2078, 2), (2516, 2), (2517, 2), (2518, 2), (2519, 2), (2957, 2), (2958, 2), (2959, 2), (2960, 2), (3398, 2), (3399, 2), (3400, 2), (3401, 2), (3839, 2), (3840, 2), (3841, 2), (3842, 2), (4280, 2), (4281, 2), (4282, 2), (4283, 2), (4721, 2), (4722, 2), (4723, 2), (4724, 2), (5162, 2), (5163, 2), (5164, 2), (5165, 2), (5603, 2), (5604, 2), (5605, 2), (5606, 2), (6044, 2), (6045, 2), (6046, 2), (6047, 2), (6485, 2), (6486, 2), (6487, 2), (6488, 2), (6506, 2), (6507, 2), (6508, 2), (6509, 2), (6527, 2), (6528, 2), (6529, 2), (6530, 2), (6548, 2), (6549, 2), (6550, 2), (6551, 2)]
theorem det03Term3Row13_decode : SparsePolynomial.decodeCubic 21 det03Term3Row13 = SparsePolynomial.monoTimes [14] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row13 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row13 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [14]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row13_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row14 : CoefficientMerge.Poly := [(773, 2), (774, 2), (775, 2), (776, 2), (1214, 2), (1215, 2), (1216, 2), (1217, 2), (1655, 2), (1656, 2), (1657, 2), (1658, 2), (2096, 2), (2097, 2), (2098, 2), (2099, 2), (2537, 2), (2538, 2), (2539, 2), (2540, 2), (2978, 2), (2979, 2), (2980, 2), (2981, 2), (3419, 2), (3420, 2), (3421, 2), (3422, 2), (3860, 2), (3861, 2), (3862, 2), (3863, 2), (4301, 2), (4302, 2), (4303, 2), (4304, 2), (4742, 2), (4743, 2), (4744, 2), (4745, 2), (5183, 2), (5184, 2), (5185, 2), (5186, 2), (5624, 2), (5625, 2), (5626, 2), (5627, 2), (6065, 2), (6066, 2), (6067, 2), (6068, 2), (6506, 2), (6507, 2), (6508, 2), (6509, 2), (6947, 2), (6948, 2), (6949, 2), (6950, 2), (6968, 2), (6969, 2), (6970, 2), (6971, 2), (6989, 2), (6990, 2), (6991, 2), (6992, 2)]
theorem det03Term3Row14_decode : SparsePolynomial.decodeCubic 21 det03Term3Row14 = SparsePolynomial.monoTimes [15] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row14 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row14 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [15]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row14_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row15 : CoefficientMerge.Poly := [(794, 2), (795, 2), (796, 2), (797, 2), (1235, 2), (1236, 2), (1237, 2), (1238, 2), (1676, 2), (1677, 2), (1678, 2), (1679, 2), (2117, 2), (2118, 2), (2119, 2), (2120, 2), (2558, 2), (2559, 2), (2560, 2), (2561, 2), (2999, 2), (3000, 2), (3001, 2), (3002, 2), (3440, 2), (3441, 2), (3442, 2), (3443, 2), (3881, 2), (3882, 2), (3883, 2), (3884, 2), (4322, 2), (4323, 2), (4324, 2), (4325, 2), (4763, 2), (4764, 2), (4765, 2), (4766, 2), (5204, 2), (5205, 2), (5206, 2), (5207, 2), (5645, 2), (5646, 2), (5647, 2), (5648, 2), (6086, 2), (6087, 2), (6088, 2), (6089, 2), (6527, 2), (6528, 2), (6529, 2), (6530, 2), (6968, 2), (6969, 2), (6970, 2), (6971, 2), (7409, 2), (7410, 2), (7411, 2), (7412, 2), (7430, 2), (7431, 2), (7432, 2), (7433, 2)]
theorem det03Term3Row15_decode : SparsePolynomial.decodeCubic 21 det03Term3Row15 = SparsePolynomial.monoTimes [16] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row15 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row15 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [16]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row15_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite21
