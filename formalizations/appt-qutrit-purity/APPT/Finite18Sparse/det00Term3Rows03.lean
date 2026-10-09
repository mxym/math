import APPT.Finite18Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det00Term3Row12 : CoefficientMerge.Poly := [(573, 2), (574, 2), (575, 2), (897, 2), (898, 2), (899, 2), (1221, 2), (1222, 2), (1223, 2), (1545, 2), (1546, 2), (1547, 2), (1869, 2), (1870, 2), (1871, 2), (2193, 2), (2194, 2), (2195, 2), (2517, 2), (2518, 2), (2519, 2), (2841, 2), (2842, 2), (2843, 2), (3165, 2), (3166, 2), (3167, 2), (3489, 2), (3490, 2), (3491, 2), (3813, 2), (3814, 2), (3815, 2), (4137, 2), (4138, 2), (4139, 2), (4461, 2), (4462, 2), (4463, 2)]
theorem det00Term3Row12_decode : SparsePolynomial.decodeCubic 18 det00Term3Row12 = SparsePolynomial.monoTimes [13] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row12 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term3Row12 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [13]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row12_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite18
