import APPT.Finite21Sparse.det03Term5Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det03Term5Coeffs : CoefficientMerge.Poly := [(944, 2), (965, 4), (986, 4), (1007, 4), (1028, 4), (1049, 4), (1070, 4), (1091, 4), (1112, 4), (1133, 4), (1154, 4), (1175, 4), (1196, 4), (1217, 4), (1406, 2), (1427, 4), (1448, 4), (1469, 4), (1490, 4), (1511, 4), (1532, 4), (1553, 4), (1574, 4), (1595, 4), (1616, 4), (1637, 4), (1658, 4), (1868, 2), (1889, 4), (1910, 4), (1931, 4), (1952, 4), (1973, 4), (1994, 4), (2015, 4), (2036, 4), (2057, 4), (2078, 4), (2099, 4), (2330, 2), (2351, 4), (2372, 4), (2393, 4), (2414, 4), (2435, 4), (2456, 4), (2477, 4), (2498, 4), (2519, 4), (2540, 4), (2792, 2), (2813, 4), (2834, 4), (2855, 4), (2876, 4), (2897, 4), (2918, 4), (2939, 4), (2960, 4), (2981, 4), (3254, 2), (3275, 4), (3296, 4), (3317, 4), (3338, 4), (3359, 4), (3380, 4), (3401, 4), (3422, 4), (3716, 2), (3737, 4), (3758, 4), (3779, 4), (3800, 4), (3821, 4), (3842, 4), (3863, 4), (4178, 2), (4199, 4), (4220, 4), (4241, 4), (4262, 4), (4283, 4), (4304, 4), (4640, 2), (4661, 4), (4682, 4), (4703, 4), (4724, 4), (4745, 4), (5102, 2), (5123, 4), (5144, 4), (5165, 4), (5186, 4), (5564, 2), (5585, 4), (5606, 4), (5627, 4), (6026, 2), (6047, 4), (6068, 4), (6488, 2), (6509, 4), (6950, 2)]
theorem det03Term5Coeffs_data : det03Term5Coeffs = CoefficientMerge.trim det03Term5Row00 := by decide +kernel
theorem eval_det03Term5Coeffs (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term5Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det03Pair5 := by
  rw [det03Term5Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term5Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair5 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite21
