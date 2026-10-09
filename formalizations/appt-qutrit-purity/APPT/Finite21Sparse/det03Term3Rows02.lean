import APPT.Finite21Sparse.Det03Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det03Term3Row08 : CoefficientMerge.Poly := [(647, 2), (648, 2), (649, 2), (650, 2), (1088, 2), (1089, 2), (1090, 2), (1091, 2), (1529, 2), (1530, 2), (1531, 2), (1532, 2), (1970, 2), (1971, 2), (1972, 2), (1973, 2), (2411, 2), (2412, 2), (2413, 2), (2414, 2), (2852, 2), (2853, 2), (2854, 2), (2855, 2), (3293, 2), (3294, 2), (3295, 2), (3296, 2), (3734, 2), (3735, 2), (3736, 2), (3737, 2), (4175, 2), (4176, 2), (4177, 2), (4178, 2), (4196, 2), (4197, 2), (4198, 2), (4199, 2), (4217, 2), (4218, 2), (4219, 2), (4220, 2), (4238, 2), (4239, 2), (4240, 2), (4241, 2), (4259, 2), (4260, 2), (4261, 2), (4262, 2), (4280, 2), (4281, 2), (4282, 2), (4283, 2), (4301, 2), (4302, 2), (4303, 2), (4304, 2), (4322, 2), (4323, 2), (4324, 2), (4325, 2), (4343, 2), (4344, 2), (4345, 2), (4346, 2)]
theorem det03Term3Row08_decode : SparsePolynomial.decodeCubic 21 det03Term3Row08 = SparsePolynomial.monoTimes [9] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row08 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row09 : CoefficientMerge.Poly := [(668, 2), (669, 2), (670, 2), (671, 2), (1109, 2), (1110, 2), (1111, 2), (1112, 2), (1550, 2), (1551, 2), (1552, 2), (1553, 2), (1991, 2), (1992, 2), (1993, 2), (1994, 2), (2432, 2), (2433, 2), (2434, 2), (2435, 2), (2873, 2), (2874, 2), (2875, 2), (2876, 2), (3314, 2), (3315, 2), (3316, 2), (3317, 2), (3755, 2), (3756, 2), (3757, 2), (3758, 2), (4196, 2), (4197, 2), (4198, 2), (4199, 2), (4637, 2), (4638, 2), (4639, 2), (4640, 2), (4658, 2), (4659, 2), (4660, 2), (4661, 2), (4679, 2), (4680, 2), (4681, 2), (4682, 2), (4700, 2), (4701, 2), (4702, 2), (4703, 2), (4721, 2), (4722, 2), (4723, 2), (4724, 2), (4742, 2), (4743, 2), (4744, 2), (4745, 2), (4763, 2), (4764, 2), (4765, 2), (4766, 2), (4784, 2), (4785, 2), (4786, 2), (4787, 2)]
theorem det03Term3Row09_decode : SparsePolynomial.decodeCubic 21 det03Term3Row09 = SparsePolynomial.monoTimes [10] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row09 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row10 : CoefficientMerge.Poly := [(689, 2), (690, 2), (691, 2), (692, 2), (1130, 2), (1131, 2), (1132, 2), (1133, 2), (1571, 2), (1572, 2), (1573, 2), (1574, 2), (2012, 2), (2013, 2), (2014, 2), (2015, 2), (2453, 2), (2454, 2), (2455, 2), (2456, 2), (2894, 2), (2895, 2), (2896, 2), (2897, 2), (3335, 2), (3336, 2), (3337, 2), (3338, 2), (3776, 2), (3777, 2), (3778, 2), (3779, 2), (4217, 2), (4218, 2), (4219, 2), (4220, 2), (4658, 2), (4659, 2), (4660, 2), (4661, 2), (5099, 2), (5100, 2), (5101, 2), (5102, 2), (5120, 2), (5121, 2), (5122, 2), (5123, 2), (5141, 2), (5142, 2), (5143, 2), (5144, 2), (5162, 2), (5163, 2), (5164, 2), (5165, 2), (5183, 2), (5184, 2), (5185, 2), (5186, 2), (5204, 2), (5205, 2), (5206, 2), (5207, 2), (5225, 2), (5226, 2), (5227, 2), (5228, 2)]
theorem det03Term3Row10_decode : SparsePolynomial.decodeCubic 21 det03Term3Row10 = SparsePolynomial.monoTimes [11] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row10 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row10 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row10_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row11 : CoefficientMerge.Poly := [(710, 2), (711, 2), (712, 2), (713, 2), (1151, 2), (1152, 2), (1153, 2), (1154, 2), (1592, 2), (1593, 2), (1594, 2), (1595, 2), (2033, 2), (2034, 2), (2035, 2), (2036, 2), (2474, 2), (2475, 2), (2476, 2), (2477, 2), (2915, 2), (2916, 2), (2917, 2), (2918, 2), (3356, 2), (3357, 2), (3358, 2), (3359, 2), (3797, 2), (3798, 2), (3799, 2), (3800, 2), (4238, 2), (4239, 2), (4240, 2), (4241, 2), (4679, 2), (4680, 2), (4681, 2), (4682, 2), (5120, 2), (5121, 2), (5122, 2), (5123, 2), (5561, 2), (5562, 2), (5563, 2), (5564, 2), (5582, 2), (5583, 2), (5584, 2), (5585, 2), (5603, 2), (5604, 2), (5605, 2), (5606, 2), (5624, 2), (5625, 2), (5626, 2), (5627, 2), (5645, 2), (5646, 2), (5647, 2), (5648, 2), (5666, 2), (5667, 2), (5668, 2), (5669, 2)]
theorem det03Term3Row11_decode : SparsePolynomial.decodeCubic 21 det03Term3Row11 = SparsePolynomial.monoTimes [12] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row11 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row11 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [12]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row11_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite21
