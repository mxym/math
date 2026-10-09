import APPT.Finite18Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det00Term3Row08 : CoefficientMerge.Poly := [(501, 2), (502, 2), (503, 2), (825, 2), (826, 2), (827, 2), (1149, 2), (1150, 2), (1151, 2), (1473, 2), (1474, 2), (1475, 2), (1797, 2), (1798, 2), (1799, 2), (2121, 2), (2122, 2), (2123, 2), (2445, 2), (2446, 2), (2447, 2), (2769, 2), (2770, 2), (2771, 2), (3093, 2), (3094, 2), (3095, 2), (3111, 2), (3112, 2), (3113, 2), (3129, 2), (3130, 2), (3131, 2), (3147, 2), (3148, 2), (3149, 2), (3165, 2), (3166, 2), (3167, 2)]
theorem det00Term3Row08_decode : SparsePolynomial.decodeCubic 18 det00Term3Row08 = SparsePolynomial.monoTimes [9] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row08 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term3Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row09 : CoefficientMerge.Poly := [(519, 2), (520, 2), (521, 2), (843, 2), (844, 2), (845, 2), (1167, 2), (1168, 2), (1169, 2), (1491, 2), (1492, 2), (1493, 2), (1815, 2), (1816, 2), (1817, 2), (2139, 2), (2140, 2), (2141, 2), (2463, 2), (2464, 2), (2465, 2), (2787, 2), (2788, 2), (2789, 2), (3111, 2), (3112, 2), (3113, 2), (3435, 2), (3436, 2), (3437, 2), (3453, 2), (3454, 2), (3455, 2), (3471, 2), (3472, 2), (3473, 2), (3489, 2), (3490, 2), (3491, 2)]
theorem det00Term3Row09_decode : SparsePolynomial.decodeCubic 18 det00Term3Row09 = SparsePolynomial.monoTimes [10] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row09 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term3Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row10 : CoefficientMerge.Poly := [(537, 2), (538, 2), (539, 2), (861, 2), (862, 2), (863, 2), (1185, 2), (1186, 2), (1187, 2), (1509, 2), (1510, 2), (1511, 2), (1833, 2), (1834, 2), (1835, 2), (2157, 2), (2158, 2), (2159, 2), (2481, 2), (2482, 2), (2483, 2), (2805, 2), (2806, 2), (2807, 2), (3129, 2), (3130, 2), (3131, 2), (3453, 2), (3454, 2), (3455, 2), (3777, 2), (3778, 2), (3779, 2), (3795, 2), (3796, 2), (3797, 2), (3813, 2), (3814, 2), (3815, 2)]
theorem det00Term3Row10_decode : SparsePolynomial.decodeCubic 18 det00Term3Row10 = SparsePolynomial.monoTimes [11] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row10 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term3Row10 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row10_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row11 : CoefficientMerge.Poly := [(555, 2), (556, 2), (557, 2), (879, 2), (880, 2), (881, 2), (1203, 2), (1204, 2), (1205, 2), (1527, 2), (1528, 2), (1529, 2), (1851, 2), (1852, 2), (1853, 2), (2175, 2), (2176, 2), (2177, 2), (2499, 2), (2500, 2), (2501, 2), (2823, 2), (2824, 2), (2825, 2), (3147, 2), (3148, 2), (3149, 2), (3471, 2), (3472, 2), (3473, 2), (3795, 2), (3796, 2), (3797, 2), (4119, 2), (4120, 2), (4121, 2), (4137, 2), (4138, 2), (4139, 2)]
theorem det00Term3Row11_decode : SparsePolynomial.decodeCubic 18 det00Term3Row11 = SparsePolynomial.monoTimes [12] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row11 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term3Row11 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [12]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row11_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite18
