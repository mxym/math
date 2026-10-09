import APPT.Finite24Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Term3Row16 : CoefficientMerge.Poly := [(1004, 2), (1005, 2), (1006, 2), (1007, 2), (1580, 2), (1581, 2), (1582, 2), (1583, 2), (2156, 2), (2157, 2), (2158, 2), (2159, 2), (2732, 2), (2733, 2), (2734, 2), (2735, 2), (3308, 2), (3309, 2), (3310, 2), (3311, 2), (3884, 2), (3885, 2), (3886, 2), (3887, 2), (4460, 2), (4461, 2), (4462, 2), (4463, 2), (5036, 2), (5037, 2), (5038, 2), (5039, 2), (5612, 2), (5613, 2), (5614, 2), (5615, 2), (6188, 2), (6189, 2), (6190, 2), (6191, 2), (6764, 2), (6765, 2), (6766, 2), (6767, 2), (7340, 2), (7341, 2), (7342, 2), (7343, 2), (7916, 2), (7917, 2), (7918, 2), (7919, 2), (8492, 2), (8493, 2), (8494, 2), (8495, 2), (9068, 2), (9069, 2), (9070, 2), (9071, 2), (9644, 2), (9645, 2), (9646, 2), (9647, 2), (10220, 2), (10221, 2), (10222, 2), (10223, 2), (10244, 2), (10245, 2), (10246, 2), (10247, 2), (10268, 2), (10269, 2), (10270, 2), (10271, 2), (10292, 2), (10293, 2), (10294, 2), (10295, 2)]
theorem det04Term3Row16_decode : SparsePolynomial.decodeCubic 24 det04Term3Row16 = SparsePolynomial.monoTimes [17] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row16 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row16 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [17]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row16_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row17 : CoefficientMerge.Poly := [(1028, 2), (1029, 2), (1030, 2), (1031, 2), (1604, 2), (1605, 2), (1606, 2), (1607, 2), (2180, 2), (2181, 2), (2182, 2), (2183, 2), (2756, 2), (2757, 2), (2758, 2), (2759, 2), (3332, 2), (3333, 2), (3334, 2), (3335, 2), (3908, 2), (3909, 2), (3910, 2), (3911, 2), (4484, 2), (4485, 2), (4486, 2), (4487, 2), (5060, 2), (5061, 2), (5062, 2), (5063, 2), (5636, 2), (5637, 2), (5638, 2), (5639, 2), (6212, 2), (6213, 2), (6214, 2), (6215, 2), (6788, 2), (6789, 2), (6790, 2), (6791, 2), (7364, 2), (7365, 2), (7366, 2), (7367, 2), (7940, 2), (7941, 2), (7942, 2), (7943, 2), (8516, 2), (8517, 2), (8518, 2), (8519, 2), (9092, 2), (9093, 2), (9094, 2), (9095, 2), (9668, 2), (9669, 2), (9670, 2), (9671, 2), (10244, 2), (10245, 2), (10246, 2), (10247, 2), (10820, 2), (10821, 2), (10822, 2), (10823, 2), (10844, 2), (10845, 2), (10846, 2), (10847, 2), (10868, 2), (10869, 2), (10870, 2), (10871, 2)]
theorem det04Term3Row17_decode : SparsePolynomial.decodeCubic 24 det04Term3Row17 = SparsePolynomial.monoTimes [18] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row17 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row17 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [18]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row17_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row18 : CoefficientMerge.Poly := [(1052, 2), (1053, 2), (1054, 2), (1055, 2), (1628, 2), (1629, 2), (1630, 2), (1631, 2), (2204, 2), (2205, 2), (2206, 2), (2207, 2), (2780, 2), (2781, 2), (2782, 2), (2783, 2), (3356, 2), (3357, 2), (3358, 2), (3359, 2), (3932, 2), (3933, 2), (3934, 2), (3935, 2), (4508, 2), (4509, 2), (4510, 2), (4511, 2), (5084, 2), (5085, 2), (5086, 2), (5087, 2), (5660, 2), (5661, 2), (5662, 2), (5663, 2), (6236, 2), (6237, 2), (6238, 2), (6239, 2), (6812, 2), (6813, 2), (6814, 2), (6815, 2), (7388, 2), (7389, 2), (7390, 2), (7391, 2), (7964, 2), (7965, 2), (7966, 2), (7967, 2), (8540, 2), (8541, 2), (8542, 2), (8543, 2), (9116, 2), (9117, 2), (9118, 2), (9119, 2), (9692, 2), (9693, 2), (9694, 2), (9695, 2), (10268, 2), (10269, 2), (10270, 2), (10271, 2), (10844, 2), (10845, 2), (10846, 2), (10847, 2), (11420, 2), (11421, 2), (11422, 2), (11423, 2), (11444, 2), (11445, 2), (11446, 2), (11447, 2)]
theorem det04Term3Row18_decode : SparsePolynomial.decodeCubic 24 det04Term3Row18 = SparsePolynomial.monoTimes [19] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row18 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row18 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [19]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row18_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row19 : CoefficientMerge.Poly := [(1076, 2), (1077, 2), (1078, 2), (1079, 2), (1652, 2), (1653, 2), (1654, 2), (1655, 2), (2228, 2), (2229, 2), (2230, 2), (2231, 2), (2804, 2), (2805, 2), (2806, 2), (2807, 2), (3380, 2), (3381, 2), (3382, 2), (3383, 2), (3956, 2), (3957, 2), (3958, 2), (3959, 2), (4532, 2), (4533, 2), (4534, 2), (4535, 2), (5108, 2), (5109, 2), (5110, 2), (5111, 2), (5684, 2), (5685, 2), (5686, 2), (5687, 2), (6260, 2), (6261, 2), (6262, 2), (6263, 2), (6836, 2), (6837, 2), (6838, 2), (6839, 2), (7412, 2), (7413, 2), (7414, 2), (7415, 2), (7988, 2), (7989, 2), (7990, 2), (7991, 2), (8564, 2), (8565, 2), (8566, 2), (8567, 2), (9140, 2), (9141, 2), (9142, 2), (9143, 2), (9716, 2), (9717, 2), (9718, 2), (9719, 2), (10292, 2), (10293, 2), (10294, 2), (10295, 2), (10868, 2), (10869, 2), (10870, 2), (10871, 2), (11444, 2), (11445, 2), (11446, 2), (11447, 2), (12020, 2), (12021, 2), (12022, 2), (12023, 2)]
theorem det04Term3Row19_decode : SparsePolynomial.decodeCubic 24 det04Term3Row19 = SparsePolynomial.monoTimes [20] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row19 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row19 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [20]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row19_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite24
