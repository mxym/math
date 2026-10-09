import APPT.Finite9Sparse.TargetQuadratic
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def targetProductRow08 : CoefficientMerge.Poly := [(8, -936), (17, -1566), (26, -1260), (35, -954), (44, -648), (53, -342), (62, -36), (71, 270), (80, 576), (98, -1566), (107, -2520), (116, -1908), (125, -1296), (134, -684), (143, -72), (152, 540), (161, 1152), (188, -1890), (197, -2862), (206, -1944), (215, -1026), (224, -108), (233, 810), (242, 1728), (278, -1908), (287, -2592), (296, -1368), (305, -144), (314, 1080), (323, 2304), (368, -1620), (377, -1710), (386, -180), (395, 1350), (404, 2880), (458, -1026), (467, -216), (476, 1620), (485, 3456), (548, -126), (557, 1890), (566, 4032), (638, 1080), (647, 4608), (728, 2592)]
theorem targetProductRow08_decode : SparsePolynomial.decodeCubic 9 targetProductRow08 = SparsePolynomial.monoTimes [8] (9 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow08 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow08 = (9 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow08_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
