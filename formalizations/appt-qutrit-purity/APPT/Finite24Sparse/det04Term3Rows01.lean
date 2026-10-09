import APPT.Finite24Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Term3Row04 : CoefficientMerge.Poly := [(716, 2), (717, 2), (718, 2), (719, 2), (1292, 2), (1293, 2), (1294, 2), (1295, 2), (1868, 2), (1869, 2), (1870, 2), (1871, 2), (2444, 2), (2445, 2), (2446, 2), (2447, 2), (3020, 2), (3021, 2), (3022, 2), (3023, 2), (3044, 2), (3045, 2), (3046, 2), (3047, 2), (3068, 2), (3069, 2), (3070, 2), (3071, 2), (3092, 2), (3093, 2), (3094, 2), (3095, 2), (3116, 2), (3117, 2), (3118, 2), (3119, 2), (3140, 2), (3141, 2), (3142, 2), (3143, 2), (3164, 2), (3165, 2), (3166, 2), (3167, 2), (3188, 2), (3189, 2), (3190, 2), (3191, 2), (3212, 2), (3213, 2), (3214, 2), (3215, 2), (3236, 2), (3237, 2), (3238, 2), (3239, 2), (3260, 2), (3261, 2), (3262, 2), (3263, 2), (3284, 2), (3285, 2), (3286, 2), (3287, 2), (3308, 2), (3309, 2), (3310, 2), (3311, 2), (3332, 2), (3333, 2), (3334, 2), (3335, 2), (3356, 2), (3357, 2), (3358, 2), (3359, 2), (3380, 2), (3381, 2), (3382, 2), (3383, 2)]
theorem det04Term3Row04_decode : SparsePolynomial.decodeCubic 24 det04Term3Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row04 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row05 : CoefficientMerge.Poly := [(740, 2), (741, 2), (742, 2), (743, 2), (1316, 2), (1317, 2), (1318, 2), (1319, 2), (1892, 2), (1893, 2), (1894, 2), (1895, 2), (2468, 2), (2469, 2), (2470, 2), (2471, 2), (3044, 2), (3045, 2), (3046, 2), (3047, 2), (3620, 2), (3621, 2), (3622, 2), (3623, 2), (3644, 2), (3645, 2), (3646, 2), (3647, 2), (3668, 2), (3669, 2), (3670, 2), (3671, 2), (3692, 2), (3693, 2), (3694, 2), (3695, 2), (3716, 2), (3717, 2), (3718, 2), (3719, 2), (3740, 2), (3741, 2), (3742, 2), (3743, 2), (3764, 2), (3765, 2), (3766, 2), (3767, 2), (3788, 2), (3789, 2), (3790, 2), (3791, 2), (3812, 2), (3813, 2), (3814, 2), (3815, 2), (3836, 2), (3837, 2), (3838, 2), (3839, 2), (3860, 2), (3861, 2), (3862, 2), (3863, 2), (3884, 2), (3885, 2), (3886, 2), (3887, 2), (3908, 2), (3909, 2), (3910, 2), (3911, 2), (3932, 2), (3933, 2), (3934, 2), (3935, 2), (3956, 2), (3957, 2), (3958, 2), (3959, 2)]
theorem det04Term3Row05_decode : SparsePolynomial.decodeCubic 24 det04Term3Row05 = SparsePolynomial.monoTimes [6] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row05 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row06 : CoefficientMerge.Poly := [(764, 2), (765, 2), (766, 2), (767, 2), (1340, 2), (1341, 2), (1342, 2), (1343, 2), (1916, 2), (1917, 2), (1918, 2), (1919, 2), (2492, 2), (2493, 2), (2494, 2), (2495, 2), (3068, 2), (3069, 2), (3070, 2), (3071, 2), (3644, 2), (3645, 2), (3646, 2), (3647, 2), (4220, 2), (4221, 2), (4222, 2), (4223, 2), (4244, 2), (4245, 2), (4246, 2), (4247, 2), (4268, 2), (4269, 2), (4270, 2), (4271, 2), (4292, 2), (4293, 2), (4294, 2), (4295, 2), (4316, 2), (4317, 2), (4318, 2), (4319, 2), (4340, 2), (4341, 2), (4342, 2), (4343, 2), (4364, 2), (4365, 2), (4366, 2), (4367, 2), (4388, 2), (4389, 2), (4390, 2), (4391, 2), (4412, 2), (4413, 2), (4414, 2), (4415, 2), (4436, 2), (4437, 2), (4438, 2), (4439, 2), (4460, 2), (4461, 2), (4462, 2), (4463, 2), (4484, 2), (4485, 2), (4486, 2), (4487, 2), (4508, 2), (4509, 2), (4510, 2), (4511, 2), (4532, 2), (4533, 2), (4534, 2), (4535, 2)]
theorem det04Term3Row06_decode : SparsePolynomial.decodeCubic 24 det04Term3Row06 = SparsePolynomial.monoTimes [7] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row06 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row07 : CoefficientMerge.Poly := [(788, 2), (789, 2), (790, 2), (791, 2), (1364, 2), (1365, 2), (1366, 2), (1367, 2), (1940, 2), (1941, 2), (1942, 2), (1943, 2), (2516, 2), (2517, 2), (2518, 2), (2519, 2), (3092, 2), (3093, 2), (3094, 2), (3095, 2), (3668, 2), (3669, 2), (3670, 2), (3671, 2), (4244, 2), (4245, 2), (4246, 2), (4247, 2), (4820, 2), (4821, 2), (4822, 2), (4823, 2), (4844, 2), (4845, 2), (4846, 2), (4847, 2), (4868, 2), (4869, 2), (4870, 2), (4871, 2), (4892, 2), (4893, 2), (4894, 2), (4895, 2), (4916, 2), (4917, 2), (4918, 2), (4919, 2), (4940, 2), (4941, 2), (4942, 2), (4943, 2), (4964, 2), (4965, 2), (4966, 2), (4967, 2), (4988, 2), (4989, 2), (4990, 2), (4991, 2), (5012, 2), (5013, 2), (5014, 2), (5015, 2), (5036, 2), (5037, 2), (5038, 2), (5039, 2), (5060, 2), (5061, 2), (5062, 2), (5063, 2), (5084, 2), (5085, 2), (5086, 2), (5087, 2), (5108, 2), (5109, 2), (5110, 2), (5111, 2)]
theorem det04Term3Row07_decode : SparsePolynomial.decodeCubic 24 det04Term3Row07 = SparsePolynomial.monoTimes [8] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row07 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite24
