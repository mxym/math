import APPT.Finite21Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det00Term3Row04 : CoefficientMerge.Poly := [(564, 2), (565, 2), (566, 2), (1005, 2), (1006, 2), (1007, 2), (1446, 2), (1447, 2), (1448, 2), (1887, 2), (1888, 2), (1889, 2), (2328, 2), (2329, 2), (2330, 2), (2349, 2), (2350, 2), (2351, 2), (2370, 2), (2371, 2), (2372, 2), (2391, 2), (2392, 2), (2393, 2), (2412, 2), (2413, 2), (2414, 2), (2433, 2), (2434, 2), (2435, 2), (2454, 2), (2455, 2), (2456, 2), (2475, 2), (2476, 2), (2477, 2), (2496, 2), (2497, 2), (2498, 2), (2517, 2), (2518, 2), (2519, 2), (2538, 2), (2539, 2), (2540, 2), (2559, 2), (2560, 2), (2561, 2)]
theorem det00Term3Row04_decode : SparsePolynomial.decodeCubic 21 det00Term3Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row04 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det00Term3Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row05 : CoefficientMerge.Poly := [(585, 2), (586, 2), (587, 2), (1026, 2), (1027, 2), (1028, 2), (1467, 2), (1468, 2), (1469, 2), (1908, 2), (1909, 2), (1910, 2), (2349, 2), (2350, 2), (2351, 2), (2790, 2), (2791, 2), (2792, 2), (2811, 2), (2812, 2), (2813, 2), (2832, 2), (2833, 2), (2834, 2), (2853, 2), (2854, 2), (2855, 2), (2874, 2), (2875, 2), (2876, 2), (2895, 2), (2896, 2), (2897, 2), (2916, 2), (2917, 2), (2918, 2), (2937, 2), (2938, 2), (2939, 2), (2958, 2), (2959, 2), (2960, 2), (2979, 2), (2980, 2), (2981, 2), (3000, 2), (3001, 2), (3002, 2)]
theorem det00Term3Row05_decode : SparsePolynomial.decodeCubic 21 det00Term3Row05 = SparsePolynomial.monoTimes [6] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row05 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det00Term3Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row06 : CoefficientMerge.Poly := [(606, 2), (607, 2), (608, 2), (1047, 2), (1048, 2), (1049, 2), (1488, 2), (1489, 2), (1490, 2), (1929, 2), (1930, 2), (1931, 2), (2370, 2), (2371, 2), (2372, 2), (2811, 2), (2812, 2), (2813, 2), (3252, 2), (3253, 2), (3254, 2), (3273, 2), (3274, 2), (3275, 2), (3294, 2), (3295, 2), (3296, 2), (3315, 2), (3316, 2), (3317, 2), (3336, 2), (3337, 2), (3338, 2), (3357, 2), (3358, 2), (3359, 2), (3378, 2), (3379, 2), (3380, 2), (3399, 2), (3400, 2), (3401, 2), (3420, 2), (3421, 2), (3422, 2), (3441, 2), (3442, 2), (3443, 2)]
theorem det00Term3Row06_decode : SparsePolynomial.decodeCubic 21 det00Term3Row06 = SparsePolynomial.monoTimes [7] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row06 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det00Term3Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row07 : CoefficientMerge.Poly := [(627, 2), (628, 2), (629, 2), (1068, 2), (1069, 2), (1070, 2), (1509, 2), (1510, 2), (1511, 2), (1950, 2), (1951, 2), (1952, 2), (2391, 2), (2392, 2), (2393, 2), (2832, 2), (2833, 2), (2834, 2), (3273, 2), (3274, 2), (3275, 2), (3714, 2), (3715, 2), (3716, 2), (3735, 2), (3736, 2), (3737, 2), (3756, 2), (3757, 2), (3758, 2), (3777, 2), (3778, 2), (3779, 2), (3798, 2), (3799, 2), (3800, 2), (3819, 2), (3820, 2), (3821, 2), (3840, 2), (3841, 2), (3842, 2), (3861, 2), (3862, 2), (3863, 2), (3882, 2), (3883, 2), (3884, 2)]
theorem det00Term3Row07_decode : SparsePolynomial.decodeCubic 21 det00Term3Row07 = SparsePolynomial.monoTimes [8] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row07 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det00Term3Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite21
