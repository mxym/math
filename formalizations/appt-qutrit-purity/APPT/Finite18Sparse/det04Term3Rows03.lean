import APPT.Finite18Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det04Term3Row12 : CoefficientMerge.Poly := [(572, 2), (573, 2), (574, 2), (575, 2), (896, 2), (897, 2), (898, 2), (899, 2), (1220, 2), (1221, 2), (1222, 2), (1223, 2), (1544, 2), (1545, 2), (1546, 2), (1547, 2), (1868, 2), (1869, 2), (1870, 2), (1871, 2), (2192, 2), (2193, 2), (2194, 2), (2195, 2), (2516, 2), (2517, 2), (2518, 2), (2519, 2), (2840, 2), (2841, 2), (2842, 2), (2843, 2), (3164, 2), (3165, 2), (3166, 2), (3167, 2), (3488, 2), (3489, 2), (3490, 2), (3491, 2), (3812, 2), (3813, 2), (3814, 2), (3815, 2), (4136, 2), (4137, 2), (4138, 2), (4139, 2), (4460, 2), (4461, 2), (4462, 2), (4463, 2), (4478, 2), (4479, 2), (4480, 2), (4481, 2)]
theorem det04Term3Row12_decode : SparsePolynomial.decodeCubic 18 det04Term3Row12 = SparsePolynomial.monoTimes [13] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row12 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row12 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [13]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row12_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row13 : CoefficientMerge.Poly := [(590, 2), (591, 2), (592, 2), (593, 2), (914, 2), (915, 2), (916, 2), (917, 2), (1238, 2), (1239, 2), (1240, 2), (1241, 2), (1562, 2), (1563, 2), (1564, 2), (1565, 2), (1886, 2), (1887, 2), (1888, 2), (1889, 2), (2210, 2), (2211, 2), (2212, 2), (2213, 2), (2534, 2), (2535, 2), (2536, 2), (2537, 2), (2858, 2), (2859, 2), (2860, 2), (2861, 2), (3182, 2), (3183, 2), (3184, 2), (3185, 2), (3506, 2), (3507, 2), (3508, 2), (3509, 2), (3830, 2), (3831, 2), (3832, 2), (3833, 2), (4154, 2), (4155, 2), (4156, 2), (4157, 2), (4478, 2), (4479, 2), (4480, 2), (4481, 2), (4802, 2), (4803, 2), (4804, 2), (4805, 2)]
theorem det04Term3Row13_decode : SparsePolynomial.decodeCubic 18 det04Term3Row13 = SparsePolynomial.monoTimes [14] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row13 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term3Row13 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [14]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row13_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite18
