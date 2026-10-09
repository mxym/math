import APPT.Finite24Sparse.Base00
import APPT.Finite24Sparse.Base01
import APPT.Finite24Sparse.Base02
import APPT.Finite24Sparse.Base03
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0000 : SparsePolynomial.Poly := [([1,1,22], -1), ([1,2,22], -2), ([1,3,22], -2), ([1,4,22], -2), ([1,5,22], -2), ([1,6,22], -2), ([1,7,22], -2), ([1,8,22], -2), ([1,9,22], -2), ([1,10,22], -2), ([1,11,22], -2), ([1,12,22], -2), ([1,13,22], -2), ([1,14,22], -2), ([1,15,22], -2), ([1,16,22], -2), ([1,17,22], -2), ([1,18,22], -2), ([1,19,22], -2), ([2,2,22], -1), ([2,3,22], -2), ([2,4,22], -2), ([2,5,22], -2), ([2,6,22], -2), ([2,7,22], -2), ([2,8,22], -2), ([2,9,22], -2), ([2,10,22], -2), ([2,11,22], -2), ([2,12,22], -2), ([2,13,22], -2), ([2,14,22], -2), ([2,15,22], -2), ([2,16,22], -2), ([2,17,22], -2), ([2,18,22], -2), ([2,19,22], -2), ([3,3,22], -1), ([3,4,22], -2), ([3,5,22], -2), ([3,6,22], -2), ([3,7,22], -2), ([3,8,22], -2), ([3,9,22], -2), ([3,10,22], -2), ([3,11,22], -2), ([3,12,22], -2), ([3,13,22], -2), ([3,14,22], -2), ([3,15,22], -2), ([3,16,22], -2), ([3,17,22], -2), ([3,18,22], -2), ([3,19,22], -2), ([4,4,22], -1), ([4,5,22], -2), ([4,6,22], -2), ([4,7,22], -2), ([4,8,22], -2), ([4,9,22], -2), ([4,10,22], -2), ([4,11,22], -2), ([4,12,22], -2), ([4,13,22], -2), ([4,14,22], -2), ([4,15,22], -2), ([4,16,22], -2), ([4,17,22], -2), ([4,18,22], -2), ([4,19,22], -2), ([5,5,22], -1), ([5,6,22], -2), ([5,7,22], -2), ([5,8,22], -2), ([5,9,22], -2), ([5,10,22], -2), ([5,11,22], -2), ([5,12,22], -2), ([5,13,22], -2), ([5,14,22], -2), ([5,15,22], -2), ([5,16,22], -2), ([5,17,22], -2), ([5,18,22], -2), ([5,19,22], -2), ([6,6,22], -1), ([6,7,22], -2), ([6,8,22], -2), ([6,9,22], -2), ([6,10,22], -2), ([6,11,22], -2), ([6,12,22], -2), ([6,13,22], -2), ([6,14,22], -2), ([6,15,22], -2), ([6,16,22], -2), ([6,17,22], -2), ([6,18,22], -2), ([6,19,22], -2), ([7,7,22], -1), ([7,8,22], -2), ([7,9,22], -2), ([7,10,22], -2), ([7,11,22], -2), ([7,12,22], -2), ([7,13,22], -2), ([7,14,22], -2), ([7,15,22], -2), ([7,16,22], -2), ([7,17,22], -2), ([7,18,22], -2), ([7,19,22], -2), ([8,8,22], -1), ([8,9,22], -2), ([8,10,22], -2), ([8,11,22], -2), ([8,12,22], -2), ([8,13,22], -2), ([8,14,22], -2), ([8,15,22], -2), ([8,16,22], -2), ([8,17,22], -2), ([8,18,22], -2), ([8,19,22], -2), ([9,9,22], -1), ([9,10,22], -2), ([9,11,22], -2), ([9,12,22], -2), ([9,13,22], -2), ([9,14,22], -2), ([9,15,22], -2), ([9,16,22], -2), ([9,17,22], -2), ([9,18,22], -2), ([9,19,22], -2), ([10,10,22], -1), ([10,11,22], -2), ([10,12,22], -2), ([10,13,22], -2), ([10,14,22], -2), ([10,15,22], -2), ([10,16,22], -2), ([10,17,22], -2), ([10,18,22], -2), ([10,19,22], -2), ([11,11,22], -1), ([11,12,22], -2), ([11,13,22], -2), ([11,14,22], -2), ([11,15,22], -2), ([11,16,22], -2), ([11,17,22], -2), ([11,18,22], -2), ([11,19,22], -2), ([12,12,22], -1), ([12,13,22], -2), ([12,14,22], -2), ([12,15,22], -2), ([12,16,22], -2), ([12,17,22], -2), ([12,18,22], -2), ([12,19,22], -2), ([13,13,22], -1), ([13,14,22], -2), ([13,15,22], -2), ([13,16,22], -2), ([13,17,22], -2), ([13,18,22], -2), ([13,19,22], -2), ([14,14,22], -1), ([14,15,22], -2), ([14,16,22], -2), ([14,17,22], -2), ([14,18,22], -2), ([14,19,22], -2), ([15,15,22], -1), ([15,16,22], -2), ([15,17,22], -2), ([15,18,22], -2), ([15,19,22], -2), ([16,16,22], -1), ([16,17,22], -2), ([16,18,22], -2), ([16,19,22], -2), ([17,17,22], -1), ([17,18,22], -2), ([17,19,22], -2), ([18,18,22], -1), ([18,19,22], -2), ([18,22,23], 4), ([19,19,22], -1), ([19,22,23], 4), ([20,22,23], 4), ([21,22,23], 4), ([22,22,23], 4), ([22,23,23], 4)]
theorem atom0000_data : atom0000 = SparsePolynomial.monoTimes [22] 1 base00 := by decide +kernel
theorem eval_atom0000 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0000 = (minorA (outer g) 0 2 * g 22) := by
  rw [atom0000_data, SparsePolynomial.eval_monoTimes, eval_base00]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0000_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60565478400 : Int) atom0000) := by
  rw [SparsePolynomial.eval_scale, eval_atom0000]
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base00_nonneg g hg hA hB
  rw [eval_base00] at hb
  have ht : 0 ≤ (minorA (outer g) 0 2 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0000Coded : CoefficientMerge.Poly := [(622, -1), (646, -2), (670, -2), (694, -2), (718, -2), (742, -2), (766, -2), (790, -2), (814, -2), (838, -2), (862, -2), (886, -2), (910, -2), (934, -2), (958, -2), (982, -2), (1006, -2), (1030, -2), (1054, -2), (1222, -1), (1246, -2), (1270, -2), (1294, -2), (1318, -2), (1342, -2), (1366, -2), (1390, -2), (1414, -2), (1438, -2), (1462, -2), (1486, -2), (1510, -2), (1534, -2), (1558, -2), (1582, -2), (1606, -2), (1630, -2), (1822, -1), (1846, -2), (1870, -2), (1894, -2), (1918, -2), (1942, -2), (1966, -2), (1990, -2), (2014, -2), (2038, -2), (2062, -2), (2086, -2), (2110, -2), (2134, -2), (2158, -2), (2182, -2), (2206, -2), (2422, -1), (2446, -2), (2470, -2), (2494, -2), (2518, -2), (2542, -2), (2566, -2), (2590, -2), (2614, -2), (2638, -2), (2662, -2), (2686, -2), (2710, -2), (2734, -2), (2758, -2), (2782, -2), (3022, -1), (3046, -2), (3070, -2), (3094, -2), (3118, -2), (3142, -2), (3166, -2), (3190, -2), (3214, -2), (3238, -2), (3262, -2), (3286, -2), (3310, -2), (3334, -2), (3358, -2), (3622, -1), (3646, -2), (3670, -2), (3694, -2), (3718, -2), (3742, -2), (3766, -2), (3790, -2), (3814, -2), (3838, -2), (3862, -2), (3886, -2), (3910, -2), (3934, -2), (4222, -1), (4246, -2), (4270, -2), (4294, -2), (4318, -2), (4342, -2), (4366, -2), (4390, -2), (4414, -2), (4438, -2), (4462, -2), (4486, -2), (4510, -2), (4822, -1), (4846, -2), (4870, -2), (4894, -2), (4918, -2), (4942, -2), (4966, -2), (4990, -2), (5014, -2), (5038, -2), (5062, -2), (5086, -2), (5422, -1), (5446, -2), (5470, -2), (5494, -2), (5518, -2), (5542, -2), (5566, -2), (5590, -2), (5614, -2), (5638, -2), (5662, -2), (6022, -1), (6046, -2), (6070, -2), (6094, -2), (6118, -2), (6142, -2), (6166, -2), (6190, -2), (6214, -2), (6238, -2), (6622, -1), (6646, -2), (6670, -2), (6694, -2), (6718, -2), (6742, -2), (6766, -2), (6790, -2), (6814, -2), (7222, -1), (7246, -2), (7270, -2), (7294, -2), (7318, -2), (7342, -2), (7366, -2), (7390, -2), (7822, -1), (7846, -2), (7870, -2), (7894, -2), (7918, -2), (7942, -2), (7966, -2), (8422, -1), (8446, -2), (8470, -2), (8494, -2), (8518, -2), (8542, -2), (9022, -1), (9046, -2), (9070, -2), (9094, -2), (9118, -2), (9622, -1), (9646, -2), (9670, -2), (9694, -2), (10222, -1), (10246, -2), (10270, -2), (10822, -1), (10846, -2), (10919, 4), (11422, -1), (11495, 4), (12071, 4), (12647, 4), (13223, 4), (13247, 4)]
theorem atom0000Coded_decode : atom0000 = SparsePolynomial.decodeCubic 24 atom0000Coded := by decide +kernel
theorem atom0000Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (60565478400 : Int) atom0000Coded) := by
  have h := atom0000_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0000Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0001 : SparsePolynomial.Poly := [([0,6,7], -4), ([1,6,7], -8), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -16), ([6,7,10], -16), ([6,7,11], -16), ([6,7,12], -16), ([6,7,13], -16), ([6,7,14], -16), ([6,7,15], -16), ([6,7,16], -16), ([6,7,17], -16), ([6,7,18], -8), ([6,7,20], 4), ([6,7,21], 12), ([6,7,22], 16), ([6,7,23], 18)]
theorem atom0001_data : atom0001 = SparsePolynomial.monoTimes [6,7] 1 base01 := by decide +kernel
theorem eval_atom0001 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0001 = (quadA (outer g) ![1,2,2] * g 6 * g 7) := by
  rw [atom0001_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0001_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (333287317440 : Int) atom0001) := by
  rw [SparsePolynomial.eval_scale, eval_atom0001]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![1,2,2] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0001Coded : CoefficientMerge.Poly := [(151, -4), (727, -8), (1303, -16), (1879, -16), (2455, -16), (3031, -16), (3607, -16), (3631, -16), (3632, -16), (3633, -16), (3634, -16), (3635, -16), (3636, -16), (3637, -16), (3638, -16), (3639, -16), (3640, -16), (3641, -16), (3642, -8), (3644, 4), (3645, 12), (3646, 16), (3647, 18)]
theorem atom0001Coded_decode : atom0001 = SparsePolynomial.decodeCubic 24 atom0001Coded := by decide +kernel
theorem atom0001Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (333287317440 : Int) atom0001Coded) := by
  have h := atom0001_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0001Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0002 : SparsePolynomial.Poly := [([0,7,8], -4), ([1,7,8], -8), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -16), ([7,8,13], -16), ([7,8,14], -16), ([7,8,15], -16), ([7,8,16], -16), ([7,8,17], -16), ([7,8,18], -8), ([7,8,20], 4), ([7,8,21], 12), ([7,8,22], 16), ([7,8,23], 18)]
theorem atom0002_data : atom0002 = SparsePolynomial.monoTimes [7,8] 1 base01 := by decide +kernel
theorem eval_atom0002 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0002 = (quadA (outer g) ![1,2,2] * g 7 * g 8) := by
  rw [atom0002_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0002_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3930610955040 : Int) atom0002) := by
  rw [SparsePolynomial.eval_scale, eval_atom0002]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![1,2,2] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0002Coded : CoefficientMerge.Poly := [(176, -4), (752, -8), (1328, -16), (1904, -16), (2480, -16), (3056, -16), (3632, -16), (4208, -16), (4232, -16), (4233, -16), (4234, -16), (4235, -16), (4236, -16), (4237, -16), (4238, -16), (4239, -16), (4240, -16), (4241, -16), (4242, -8), (4244, 4), (4245, 12), (4246, 16), (4247, 18)]
theorem atom0002Coded_decode : atom0002 = SparsePolynomial.decodeCubic 24 atom0002Coded := by decide +kernel
theorem atom0002Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3930610955040 : Int) atom0002Coded) := by
  have h := atom0002_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0002Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0003 : SparsePolynomial.Poly := [([0,7,9], -4), ([1,7,9], -8), ([2,7,9], -16), ([3,7,9], -16), ([4,7,9], -16), ([5,7,9], -16), ([6,7,9], -16), ([7,7,9], -16), ([7,8,9], -16), ([7,9,9], -16), ([7,9,10], -16), ([7,9,11], -16), ([7,9,12], -16), ([7,9,13], -16), ([7,9,14], -16), ([7,9,15], -16), ([7,9,16], -16), ([7,9,17], -16), ([7,9,18], -8), ([7,9,20], 4), ([7,9,21], 12), ([7,9,22], 16), ([7,9,23], 18)]
theorem atom0003_data : atom0003 = SparsePolynomial.monoTimes [7,9] 1 base01 := by decide +kernel
theorem eval_atom0003 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0003 = (quadA (outer g) ![1,2,2] * g 7 * g 9) := by
  rw [atom0003_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0003_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (470590991442 : Int) atom0003) := by
  rw [SparsePolynomial.eval_scale, eval_atom0003]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![1,2,2] * g 7 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0003Coded : CoefficientMerge.Poly := [(177, -4), (753, -8), (1329, -16), (1905, -16), (2481, -16), (3057, -16), (3633, -16), (4209, -16), (4233, -16), (4257, -16), (4258, -16), (4259, -16), (4260, -16), (4261, -16), (4262, -16), (4263, -16), (4264, -16), (4265, -16), (4266, -8), (4268, 4), (4269, 12), (4270, 16), (4271, 18)]
theorem atom0003Coded_decode : atom0003 = SparsePolynomial.decodeCubic 24 atom0003Coded := by decide +kernel
theorem atom0003Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (470590991442 : Int) atom0003Coded) := by
  have h := atom0003_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0003Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0004 : SparsePolynomial.Poly := [([0,8,9], -4), ([1,8,9], -8), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -16), ([8,9,13], -16), ([8,9,14], -16), ([8,9,15], -16), ([8,9,16], -16), ([8,9,17], -16), ([8,9,18], -8), ([8,9,20], 4), ([8,9,21], 12), ([8,9,22], 16), ([8,9,23], 18)]
theorem atom0004_data : atom0004 = SparsePolynomial.monoTimes [8,9] 1 base01 := by decide +kernel
theorem eval_atom0004 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0004 = (quadA (outer g) ![1,2,2] * g 8 * g 9) := by
  rw [atom0004_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0004_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3618143020800 : Int) atom0004) := by
  rw [SparsePolynomial.eval_scale, eval_atom0004]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![1,2,2] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0004Coded : CoefficientMerge.Poly := [(201, -4), (777, -8), (1353, -16), (1929, -16), (2505, -16), (3081, -16), (3657, -16), (4233, -16), (4809, -16), (4833, -16), (4834, -16), (4835, -16), (4836, -16), (4837, -16), (4838, -16), (4839, -16), (4840, -16), (4841, -16), (4842, -8), (4844, 4), (4845, 12), (4846, 16), (4847, 18)]
theorem atom0004Coded_decode : atom0004 = SparsePolynomial.decodeCubic 24 atom0004Coded := by decide +kernel
theorem atom0004Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3618143020800 : Int) atom0004Coded) := by
  have h := atom0004_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0004Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0005 : SparsePolynomial.Poly := [([0,8,10], -4), ([1,8,10], -8), ([2,8,10], -16), ([3,8,10], -16), ([4,8,10], -16), ([5,8,10], -16), ([6,8,10], -16), ([7,8,10], -16), ([8,8,10], -16), ([8,9,10], -16), ([8,10,10], -16), ([8,10,11], -16), ([8,10,12], -16), ([8,10,13], -16), ([8,10,14], -16), ([8,10,15], -16), ([8,10,16], -16), ([8,10,17], -16), ([8,10,18], -8), ([8,10,20], 4), ([8,10,21], 12), ([8,10,22], 16), ([8,10,23], 18)]
theorem atom0005_data : atom0005 = SparsePolynomial.monoTimes [8,10] 1 base01 := by decide +kernel
theorem eval_atom0005 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0005 = (quadA (outer g) ![1,2,2] * g 8 * g 10) := by
  rw [atom0005_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0005_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62491530222 : Int) atom0005) := by
  rw [SparsePolynomial.eval_scale, eval_atom0005]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![1,2,2] * g 8 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0005Coded : CoefficientMerge.Poly := [(202, -4), (778, -8), (1354, -16), (1930, -16), (2506, -16), (3082, -16), (3658, -16), (4234, -16), (4810, -16), (4834, -16), (4858, -16), (4859, -16), (4860, -16), (4861, -16), (4862, -16), (4863, -16), (4864, -16), (4865, -16), (4866, -8), (4868, 4), (4869, 12), (4870, 16), (4871, 18)]
theorem atom0005Coded_decode : atom0005 = SparsePolynomial.decodeCubic 24 atom0005Coded := by decide +kernel
theorem atom0005Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62491530222 : Int) atom0005Coded) := by
  have h := atom0005_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0005Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0006 : SparsePolynomial.Poly := [([0,1,19], -4), ([1,1,19], -12), ([1,2,19], -16), ([1,3,19], -16), ([1,4,19], -16), ([1,5,19], -16), ([1,6,19], -16), ([1,7,19], -16), ([1,8,19], -16), ([1,9,19], -16), ([1,10,19], -16), ([1,11,19], -16), ([1,12,19], -16), ([1,13,19], -16), ([1,14,19], -16), ([1,15,19], -16), ([1,16,19], -16), ([1,17,19], -16), ([1,18,19], -8), ([1,19,19], -4), ([1,19,20], 4), ([1,19,21], 6), ([1,19,22], 10), ([1,19,23], 18)]
theorem atom0006_data : atom0006 = SparsePolynomial.monoTimes [1,19] 1 base02 := by decide +kernel
theorem eval_atom0006 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0006 = (quadA (outer g) ![2,1,2] * g 1 * g 19) := by
  rw [atom0006_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0006_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4199313888000 : Int) atom0006) := by
  rw [SparsePolynomial.eval_scale, eval_atom0006]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0006Coded : CoefficientMerge.Poly := [(43, -4), (619, -12), (643, -16), (667, -16), (691, -16), (715, -16), (739, -16), (763, -16), (787, -16), (811, -16), (835, -16), (859, -16), (883, -16), (907, -16), (931, -16), (955, -16), (979, -16), (1003, -16), (1027, -8), (1051, -4), (1052, 4), (1053, 6), (1054, 10), (1055, 18)]
theorem atom0006Coded_decode : atom0006 = SparsePolynomial.decodeCubic 24 atom0006Coded := by decide +kernel
theorem atom0006Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4199313888000 : Int) atom0006Coded) := by
  have h := atom0006_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0006Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0007 : SparsePolynomial.Poly := [([0,1,21], -4), ([1,1,21], -12), ([1,2,21], -16), ([1,3,21], -16), ([1,4,21], -16), ([1,5,21], -16), ([1,6,21], -16), ([1,7,21], -16), ([1,8,21], -16), ([1,9,21], -16), ([1,10,21], -16), ([1,11,21], -16), ([1,12,21], -16), ([1,13,21], -16), ([1,14,21], -16), ([1,15,21], -16), ([1,16,21], -16), ([1,17,21], -16), ([1,18,21], -8), ([1,19,21], -4), ([1,20,21], 4), ([1,21,21], 6), ([1,21,22], 10), ([1,21,23], 18)]
theorem atom0007_data : atom0007 = SparsePolynomial.monoTimes [1,21] 1 base02 := by decide +kernel
theorem eval_atom0007 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0007 = (quadA (outer g) ![2,1,2] * g 1 * g 21) := by
  rw [atom0007_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0007_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (272866809600 : Int) atom0007) := by
  rw [SparsePolynomial.eval_scale, eval_atom0007]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0007Coded : CoefficientMerge.Poly := [(45, -4), (621, -12), (645, -16), (669, -16), (693, -16), (717, -16), (741, -16), (765, -16), (789, -16), (813, -16), (837, -16), (861, -16), (885, -16), (909, -16), (933, -16), (957, -16), (981, -16), (1005, -16), (1029, -8), (1053, -4), (1077, 4), (1101, 6), (1102, 10), (1103, 18)]
theorem atom0007Coded_decode : atom0007 = SparsePolynomial.decodeCubic 24 atom0007Coded := by decide +kernel
theorem atom0007Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (272866809600 : Int) atom0007Coded) := by
  have h := atom0007_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0007Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0008 : SparsePolynomial.Poly := [([0,1,22], -4), ([1,1,22], -12), ([1,2,22], -16), ([1,3,22], -16), ([1,4,22], -16), ([1,5,22], -16), ([1,6,22], -16), ([1,7,22], -16), ([1,8,22], -16), ([1,9,22], -16), ([1,10,22], -16), ([1,11,22], -16), ([1,12,22], -16), ([1,13,22], -16), ([1,14,22], -16), ([1,15,22], -16), ([1,16,22], -16), ([1,17,22], -16), ([1,18,22], -8), ([1,19,22], -4), ([1,20,22], 4), ([1,21,22], 6), ([1,22,22], 10), ([1,22,23], 18)]
theorem atom0008_data : atom0008 = SparsePolynomial.monoTimes [1,22] 1 base02 := by decide +kernel
theorem eval_atom0008 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0008 = (quadA (outer g) ![2,1,2] * g 1 * g 22) := by
  rw [atom0008_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0008_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (779887920000 : Int) atom0008) := by
  rw [SparsePolynomial.eval_scale, eval_atom0008]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0008Coded : CoefficientMerge.Poly := [(46, -4), (622, -12), (646, -16), (670, -16), (694, -16), (718, -16), (742, -16), (766, -16), (790, -16), (814, -16), (838, -16), (862, -16), (886, -16), (910, -16), (934, -16), (958, -16), (982, -16), (1006, -16), (1030, -8), (1054, -4), (1078, 4), (1102, 6), (1126, 10), (1127, 18)]
theorem atom0008Coded_decode : atom0008 = SparsePolynomial.decodeCubic 24 atom0008Coded := by decide +kernel
theorem atom0008Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (779887920000 : Int) atom0008Coded) := by
  have h := atom0008_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0008Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0009 : SparsePolynomial.Poly := [([0,1,23], -4), ([1,1,23], -12), ([1,2,23], -16), ([1,3,23], -16), ([1,4,23], -16), ([1,5,23], -16), ([1,6,23], -16), ([1,7,23], -16), ([1,8,23], -16), ([1,9,23], -16), ([1,10,23], -16), ([1,11,23], -16), ([1,12,23], -16), ([1,13,23], -16), ([1,14,23], -16), ([1,15,23], -16), ([1,16,23], -16), ([1,17,23], -16), ([1,18,23], -8), ([1,19,23], -4), ([1,20,23], 4), ([1,21,23], 6), ([1,22,23], 10), ([1,23,23], 18)]
theorem atom0009_data : atom0009 = SparsePolynomial.monoTimes [1,23] 1 base02 := by decide +kernel
theorem eval_atom0009 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0009 = (quadA (outer g) ![2,1,2] * g 1 * g 23) := by
  rw [atom0009_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0009_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1333326456000 : Int) atom0009) := by
  rw [SparsePolynomial.eval_scale, eval_atom0009]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0009Coded : CoefficientMerge.Poly := [(47, -4), (623, -12), (647, -16), (671, -16), (695, -16), (719, -16), (743, -16), (767, -16), (791, -16), (815, -16), (839, -16), (863, -16), (887, -16), (911, -16), (935, -16), (959, -16), (983, -16), (1007, -16), (1031, -8), (1055, -4), (1079, 4), (1103, 6), (1127, 10), (1151, 18)]
theorem atom0009Coded_decode : atom0009 = SparsePolynomial.decodeCubic 24 atom0009Coded := by decide +kernel
theorem atom0009Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1333326456000 : Int) atom0009Coded) := by
  have h := atom0009_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0009Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0010 : SparsePolynomial.Poly := [([0,3,22], -4), ([1,3,22], -12), ([2,3,22], -16), ([3,3,22], -16), ([3,4,22], -16), ([3,5,22], -16), ([3,6,22], -16), ([3,7,22], -16), ([3,8,22], -16), ([3,9,22], -16), ([3,10,22], -16), ([3,11,22], -16), ([3,12,22], -16), ([3,13,22], -16), ([3,14,22], -16), ([3,15,22], -16), ([3,16,22], -16), ([3,17,22], -16), ([3,18,22], -8), ([3,19,22], -4), ([3,20,22], 4), ([3,21,22], 6), ([3,22,22], 10), ([3,22,23], 18)]
theorem atom0010_data : atom0010 = SparsePolynomial.monoTimes [3,22] 1 base02 := by decide +kernel
theorem eval_atom0010 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0010 = (quadA (outer g) ![2,1,2] * g 3 * g 22) := by
  rw [atom0010_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0010_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3323772244800 : Int) atom0010) := by
  rw [SparsePolynomial.eval_scale, eval_atom0010]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 3 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0010Coded : CoefficientMerge.Poly := [(94, -4), (670, -12), (1246, -16), (1822, -16), (1846, -16), (1870, -16), (1894, -16), (1918, -16), (1942, -16), (1966, -16), (1990, -16), (2014, -16), (2038, -16), (2062, -16), (2086, -16), (2110, -16), (2134, -16), (2158, -16), (2182, -8), (2206, -4), (2230, 4), (2254, 6), (2278, 10), (2279, 18)]
theorem atom0010Coded_decode : atom0010 = SparsePolynomial.decodeCubic 24 atom0010Coded := by decide +kernel
theorem atom0010Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3323772244800 : Int) atom0010Coded) := by
  have h := atom0010_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0010Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0011 : SparsePolynomial.Poly := [([0,4,22], -4), ([1,4,22], -12), ([2,4,22], -16), ([3,4,22], -16), ([4,4,22], -16), ([4,5,22], -16), ([4,6,22], -16), ([4,7,22], -16), ([4,8,22], -16), ([4,9,22], -16), ([4,10,22], -16), ([4,11,22], -16), ([4,12,22], -16), ([4,13,22], -16), ([4,14,22], -16), ([4,15,22], -16), ([4,16,22], -16), ([4,17,22], -16), ([4,18,22], -8), ([4,19,22], -4), ([4,20,22], 4), ([4,21,22], 6), ([4,22,22], 10), ([4,22,23], 18)]
theorem atom0011_data : atom0011 = SparsePolynomial.monoTimes [4,22] 1 base02 := by decide +kernel
theorem eval_atom0011 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0011 = (quadA (outer g) ![2,1,2] * g 4 * g 22) := by
  rw [atom0011_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0011_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8406856197600 : Int) atom0011) := by
  rw [SparsePolynomial.eval_scale, eval_atom0011]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 4 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0011Coded : CoefficientMerge.Poly := [(118, -4), (694, -12), (1270, -16), (1846, -16), (2422, -16), (2446, -16), (2470, -16), (2494, -16), (2518, -16), (2542, -16), (2566, -16), (2590, -16), (2614, -16), (2638, -16), (2662, -16), (2686, -16), (2710, -16), (2734, -16), (2758, -8), (2782, -4), (2806, 4), (2830, 6), (2854, 10), (2855, 18)]
theorem atom0011Coded_decode : atom0011 = SparsePolynomial.decodeCubic 24 atom0011Coded := by decide +kernel
theorem atom0011Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8406856197600 : Int) atom0011Coded) := by
  have h := atom0011_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0011Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0012 : SparsePolynomial.Poly := [([0,5,22], -4), ([1,5,22], -12), ([2,5,22], -16), ([3,5,22], -16), ([4,5,22], -16), ([5,5,22], -16), ([5,6,22], -16), ([5,7,22], -16), ([5,8,22], -16), ([5,9,22], -16), ([5,10,22], -16), ([5,11,22], -16), ([5,12,22], -16), ([5,13,22], -16), ([5,14,22], -16), ([5,15,22], -16), ([5,16,22], -16), ([5,17,22], -16), ([5,18,22], -8), ([5,19,22], -4), ([5,20,22], 4), ([5,21,22], 6), ([5,22,22], 10), ([5,22,23], 18)]
theorem atom0012_data : atom0012 = SparsePolynomial.monoTimes [5,22] 1 base02 := by decide +kernel
theorem eval_atom0012 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0012 = (quadA (outer g) ![2,1,2] * g 5 * g 22) := by
  rw [atom0012_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0012_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12010271112000 : Int) atom0012) := by
  rw [SparsePolynomial.eval_scale, eval_atom0012]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 5 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0012Coded : CoefficientMerge.Poly := [(142, -4), (718, -12), (1294, -16), (1870, -16), (2446, -16), (3022, -16), (3046, -16), (3070, -16), (3094, -16), (3118, -16), (3142, -16), (3166, -16), (3190, -16), (3214, -16), (3238, -16), (3262, -16), (3286, -16), (3310, -16), (3334, -8), (3358, -4), (3382, 4), (3406, 6), (3430, 10), (3431, 18)]
theorem atom0012Coded_decode : atom0012 = SparsePolynomial.decodeCubic 24 atom0012Coded := by decide +kernel
theorem atom0012Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12010271112000 : Int) atom0012Coded) := by
  have h := atom0012_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0012Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0013 : SparsePolynomial.Poly := [([0,5,23], -4), ([1,5,23], -12), ([2,5,23], -16), ([3,5,23], -16), ([4,5,23], -16), ([5,5,23], -16), ([5,6,23], -16), ([5,7,23], -16), ([5,8,23], -16), ([5,9,23], -16), ([5,10,23], -16), ([5,11,23], -16), ([5,12,23], -16), ([5,13,23], -16), ([5,14,23], -16), ([5,15,23], -16), ([5,16,23], -16), ([5,17,23], -16), ([5,18,23], -8), ([5,19,23], -4), ([5,20,23], 4), ([5,21,23], 6), ([5,22,23], 10), ([5,23,23], 18)]
theorem atom0013_data : atom0013 = SparsePolynomial.monoTimes [5,23] 1 base02 := by decide +kernel
theorem eval_atom0013 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0013 = (quadA (outer g) ![2,1,2] * g 5 * g 23) := by
  rw [atom0013_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0013_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10009006509600 : Int) atom0013) := by
  rw [SparsePolynomial.eval_scale, eval_atom0013]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 5 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0013Coded : CoefficientMerge.Poly := [(143, -4), (719, -12), (1295, -16), (1871, -16), (2447, -16), (3023, -16), (3047, -16), (3071, -16), (3095, -16), (3119, -16), (3143, -16), (3167, -16), (3191, -16), (3215, -16), (3239, -16), (3263, -16), (3287, -16), (3311, -16), (3335, -8), (3359, -4), (3383, 4), (3407, 6), (3431, 10), (3455, 18)]
theorem atom0013Coded_decode : atom0013 = SparsePolynomial.decodeCubic 24 atom0013Coded := by decide +kernel
theorem atom0013Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10009006509600 : Int) atom0013Coded) := by
  have h := atom0013_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0013Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0014 : SparsePolynomial.Poly := [([0,6,22], -4), ([1,6,22], -12), ([2,6,22], -16), ([3,6,22], -16), ([4,6,22], -16), ([5,6,22], -16), ([6,6,22], -16), ([6,7,22], -16), ([6,8,22], -16), ([6,9,22], -16), ([6,10,22], -16), ([6,11,22], -16), ([6,12,22], -16), ([6,13,22], -16), ([6,14,22], -16), ([6,15,22], -16), ([6,16,22], -16), ([6,17,22], -16), ([6,18,22], -8), ([6,19,22], -4), ([6,20,22], 4), ([6,21,22], 6), ([6,22,22], 10), ([6,22,23], 18)]
theorem atom0014_data : atom0014 = SparsePolynomial.monoTimes [6,22] 1 base02 := by decide +kernel
theorem eval_atom0014 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0014 = (quadA (outer g) ![2,1,2] * g 6 * g 22) := by
  rw [atom0014_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0014_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15528360456000 : Int) atom0014) := by
  rw [SparsePolynomial.eval_scale, eval_atom0014]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 6 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0014Coded : CoefficientMerge.Poly := [(166, -4), (742, -12), (1318, -16), (1894, -16), (2470, -16), (3046, -16), (3622, -16), (3646, -16), (3670, -16), (3694, -16), (3718, -16), (3742, -16), (3766, -16), (3790, -16), (3814, -16), (3838, -16), (3862, -16), (3886, -16), (3910, -8), (3934, -4), (3958, 4), (3982, 6), (4006, 10), (4007, 18)]
theorem atom0014Coded_decode : atom0014 = SparsePolynomial.decodeCubic 24 atom0014Coded := by decide +kernel
theorem atom0014Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15528360456000 : Int) atom0014Coded) := by
  have h := atom0014_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0014Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0015 : SparsePolynomial.Poly := [([0,6,23], -4), ([1,6,23], -12), ([2,6,23], -16), ([3,6,23], -16), ([4,6,23], -16), ([5,6,23], -16), ([6,6,23], -16), ([6,7,23], -16), ([6,8,23], -16), ([6,9,23], -16), ([6,10,23], -16), ([6,11,23], -16), ([6,12,23], -16), ([6,13,23], -16), ([6,14,23], -16), ([6,15,23], -16), ([6,16,23], -16), ([6,17,23], -16), ([6,18,23], -8), ([6,19,23], -4), ([6,20,23], 4), ([6,21,23], 6), ([6,22,23], 10), ([6,23,23], 18)]
theorem atom0015_data : atom0015 = SparsePolynomial.monoTimes [6,23] 1 base02 := by decide +kernel
theorem eval_atom0015 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0015 = (quadA (outer g) ![2,1,2] * g 6 * g 23) := by
  rw [atom0015_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0015_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12749596977600 : Int) atom0015) := by
  rw [SparsePolynomial.eval_scale, eval_atom0015]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 6 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0015Coded : CoefficientMerge.Poly := [(167, -4), (743, -12), (1319, -16), (1895, -16), (2471, -16), (3047, -16), (3623, -16), (3647, -16), (3671, -16), (3695, -16), (3719, -16), (3743, -16), (3767, -16), (3791, -16), (3815, -16), (3839, -16), (3863, -16), (3887, -16), (3911, -8), (3935, -4), (3959, 4), (3983, 6), (4007, 10), (4031, 18)]
theorem atom0015Coded_decode : atom0015 = SparsePolynomial.decodeCubic 24 atom0015Coded := by decide +kernel
theorem atom0015Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12749596977600 : Int) atom0015Coded) := by
  have h := atom0015_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0015Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0016 : SparsePolynomial.Poly := [([0,7,22], -4), ([1,7,22], -12), ([2,7,22], -16), ([3,7,22], -16), ([4,7,22], -16), ([5,7,22], -16), ([6,7,22], -16), ([7,7,22], -16), ([7,8,22], -16), ([7,9,22], -16), ([7,10,22], -16), ([7,11,22], -16), ([7,12,22], -16), ([7,13,22], -16), ([7,14,22], -16), ([7,15,22], -16), ([7,16,22], -16), ([7,17,22], -16), ([7,18,22], -8), ([7,19,22], -4), ([7,20,22], 4), ([7,21,22], 6), ([7,22,22], 10), ([7,22,23], 18)]
theorem atom0016_data : atom0016 = SparsePolynomial.monoTimes [7,22] 1 base02 := by decide +kernel
theorem eval_atom0016 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0016 = (quadA (outer g) ![2,1,2] * g 7 * g 22) := by
  rw [atom0016_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0016_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16200880673600 : Int) atom0016) := by
  rw [SparsePolynomial.eval_scale, eval_atom0016]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 7 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0016Coded : CoefficientMerge.Poly := [(190, -4), (766, -12), (1342, -16), (1918, -16), (2494, -16), (3070, -16), (3646, -16), (4222, -16), (4246, -16), (4270, -16), (4294, -16), (4318, -16), (4342, -16), (4366, -16), (4390, -16), (4414, -16), (4438, -16), (4462, -16), (4486, -8), (4510, -4), (4534, 4), (4558, 6), (4582, 10), (4583, 18)]
theorem atom0016Coded_decode : atom0016 = SparsePolynomial.decodeCubic 24 atom0016Coded := by decide +kernel
theorem atom0016Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16200880673600 : Int) atom0016Coded) := by
  have h := atom0016_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0016Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0017 : SparsePolynomial.Poly := [([0,7,23], -4), ([1,7,23], -12), ([2,7,23], -16), ([3,7,23], -16), ([4,7,23], -16), ([5,7,23], -16), ([6,7,23], -16), ([7,7,23], -16), ([7,8,23], -16), ([7,9,23], -16), ([7,10,23], -16), ([7,11,23], -16), ([7,12,23], -16), ([7,13,23], -16), ([7,14,23], -16), ([7,15,23], -16), ([7,16,23], -16), ([7,17,23], -16), ([7,18,23], -8), ([7,19,23], -4), ([7,20,23], 4), ([7,21,23], 6), ([7,22,23], 10), ([7,23,23], 18)]
theorem atom0017_data : atom0017 = SparsePolynomial.monoTimes [7,23] 1 base02 := by decide +kernel
theorem eval_atom0017 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0017 = (quadA (outer g) ![2,1,2] * g 7 * g 23) := by
  rw [atom0017_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0017_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12798766159200 : Int) atom0017) := by
  rw [SparsePolynomial.eval_scale, eval_atom0017]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 7 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0017Coded : CoefficientMerge.Poly := [(191, -4), (767, -12), (1343, -16), (1919, -16), (2495, -16), (3071, -16), (3647, -16), (4223, -16), (4247, -16), (4271, -16), (4295, -16), (4319, -16), (4343, -16), (4367, -16), (4391, -16), (4415, -16), (4439, -16), (4463, -16), (4487, -8), (4511, -4), (4535, 4), (4559, 6), (4583, 10), (4607, 18)]
theorem atom0017Coded_decode : atom0017 = SparsePolynomial.decodeCubic 24 atom0017Coded := by decide +kernel
theorem atom0017Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12798766159200 : Int) atom0017Coded) := by
  have h := atom0017_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0017Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0018 : SparsePolynomial.Poly := [([0,8,22], -4), ([1,8,22], -12), ([2,8,22], -16), ([3,8,22], -16), ([4,8,22], -16), ([5,8,22], -16), ([6,8,22], -16), ([7,8,22], -16), ([8,8,22], -16), ([8,9,22], -16), ([8,10,22], -16), ([8,11,22], -16), ([8,12,22], -16), ([8,13,22], -16), ([8,14,22], -16), ([8,15,22], -16), ([8,16,22], -16), ([8,17,22], -16), ([8,18,22], -8), ([8,19,22], -4), ([8,20,22], 4), ([8,21,22], 6), ([8,22,22], 10), ([8,22,23], 18)]
theorem atom0018_data : atom0018 = SparsePolynomial.monoTimes [8,22] 1 base02 := by decide +kernel
theorem eval_atom0018 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0018 = (quadA (outer g) ![2,1,2] * g 8 * g 22) := by
  rw [atom0018_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0018_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16293805012800 : Int) atom0018) := by
  rw [SparsePolynomial.eval_scale, eval_atom0018]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 8 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0018Coded : CoefficientMerge.Poly := [(214, -4), (790, -12), (1366, -16), (1942, -16), (2518, -16), (3094, -16), (3670, -16), (4246, -16), (4822, -16), (4846, -16), (4870, -16), (4894, -16), (4918, -16), (4942, -16), (4966, -16), (4990, -16), (5014, -16), (5038, -16), (5062, -8), (5086, -4), (5110, 4), (5134, 6), (5158, 10), (5159, 18)]
theorem atom0018Coded_decode : atom0018 = SparsePolynomial.decodeCubic 24 atom0018Coded := by decide +kernel
theorem atom0018Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16293805012800 : Int) atom0018Coded) := by
  have h := atom0018_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0018Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0019 : SparsePolynomial.Poly := [([0,8,23], -4), ([1,8,23], -12), ([2,8,23], -16), ([3,8,23], -16), ([4,8,23], -16), ([5,8,23], -16), ([6,8,23], -16), ([7,8,23], -16), ([8,8,23], -16), ([8,9,23], -16), ([8,10,23], -16), ([8,11,23], -16), ([8,12,23], -16), ([8,13,23], -16), ([8,14,23], -16), ([8,15,23], -16), ([8,16,23], -16), ([8,17,23], -16), ([8,18,23], -8), ([8,19,23], -4), ([8,20,23], 4), ([8,21,23], 6), ([8,22,23], 10), ([8,23,23], 18)]
theorem atom0019_data : atom0019 = SparsePolynomial.monoTimes [8,23] 1 base02 := by decide +kernel
theorem eval_atom0019 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0019 = (quadA (outer g) ![2,1,2] * g 8 * g 23) := by
  rw [atom0019_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0019_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12195889977600 : Int) atom0019) := by
  rw [SparsePolynomial.eval_scale, eval_atom0019]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 8 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0019Coded : CoefficientMerge.Poly := [(215, -4), (791, -12), (1367, -16), (1943, -16), (2519, -16), (3095, -16), (3671, -16), (4247, -16), (4823, -16), (4847, -16), (4871, -16), (4895, -16), (4919, -16), (4943, -16), (4967, -16), (4991, -16), (5015, -16), (5039, -16), (5063, -8), (5087, -4), (5111, 4), (5135, 6), (5159, 10), (5183, 18)]
theorem atom0019Coded_decode : atom0019 = SparsePolynomial.decodeCubic 24 atom0019Coded := by decide +kernel
theorem atom0019Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12195889977600 : Int) atom0019Coded) := by
  have h := atom0019_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0019Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0020 : SparsePolynomial.Poly := [([0,9,22], -4), ([1,9,22], -12), ([2,9,22], -16), ([3,9,22], -16), ([4,9,22], -16), ([5,9,22], -16), ([6,9,22], -16), ([7,9,22], -16), ([8,9,22], -16), ([9,9,22], -16), ([9,10,22], -16), ([9,11,22], -16), ([9,12,22], -16), ([9,13,22], -16), ([9,14,22], -16), ([9,15,22], -16), ([9,16,22], -16), ([9,17,22], -16), ([9,18,22], -8), ([9,19,22], -4), ([9,20,22], 4), ([9,21,22], 6), ([9,22,22], 10), ([9,22,23], 18)]
theorem atom0020_data : atom0020 = SparsePolynomial.monoTimes [9,22] 1 base02 := by decide +kernel
theorem eval_atom0020 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0020 = (quadA (outer g) ![2,1,2] * g 9 * g 22) := by
  rw [atom0020_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0020_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13827946297920 : Int) atom0020) := by
  rw [SparsePolynomial.eval_scale, eval_atom0020]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 9 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0020Coded : CoefficientMerge.Poly := [(238, -4), (814, -12), (1390, -16), (1966, -16), (2542, -16), (3118, -16), (3694, -16), (4270, -16), (4846, -16), (5422, -16), (5446, -16), (5470, -16), (5494, -16), (5518, -16), (5542, -16), (5566, -16), (5590, -16), (5614, -16), (5638, -8), (5662, -4), (5686, 4), (5710, 6), (5734, 10), (5735, 18)]
theorem atom0020Coded_decode : atom0020 = SparsePolynomial.decodeCubic 24 atom0020Coded := by decide +kernel
theorem atom0020Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (13827946297920 : Int) atom0020Coded) := by
  have h := atom0020_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0020Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0021 : SparsePolynomial.Poly := [([0,9,23], -4), ([1,9,23], -12), ([2,9,23], -16), ([3,9,23], -16), ([4,9,23], -16), ([5,9,23], -16), ([6,9,23], -16), ([7,9,23], -16), ([8,9,23], -16), ([9,9,23], -16), ([9,10,23], -16), ([9,11,23], -16), ([9,12,23], -16), ([9,13,23], -16), ([9,14,23], -16), ([9,15,23], -16), ([9,16,23], -16), ([9,17,23], -16), ([9,18,23], -8), ([9,19,23], -4), ([9,20,23], 4), ([9,21,23], 6), ([9,22,23], 10), ([9,23,23], 18)]
theorem atom0021_data : atom0021 = SparsePolynomial.monoTimes [9,23] 1 base02 := by decide +kernel
theorem eval_atom0021 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0021 = (quadA (outer g) ![2,1,2] * g 9 * g 23) := by
  rw [atom0021_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0021_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9159699974688 : Int) atom0021) := by
  rw [SparsePolynomial.eval_scale, eval_atom0021]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 9 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0021Coded : CoefficientMerge.Poly := [(239, -4), (815, -12), (1391, -16), (1967, -16), (2543, -16), (3119, -16), (3695, -16), (4271, -16), (4847, -16), (5423, -16), (5447, -16), (5471, -16), (5495, -16), (5519, -16), (5543, -16), (5567, -16), (5591, -16), (5615, -16), (5639, -8), (5663, -4), (5687, 4), (5711, 6), (5735, 10), (5759, 18)]
theorem atom0021Coded_decode : atom0021 = SparsePolynomial.decodeCubic 24 atom0021Coded := by decide +kernel
theorem atom0021Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9159699974688 : Int) atom0021Coded) := by
  have h := atom0021_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0021Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0022 : SparsePolynomial.Poly := [([0,10,22], -4), ([1,10,22], -12), ([2,10,22], -16), ([3,10,22], -16), ([4,10,22], -16), ([5,10,22], -16), ([6,10,22], -16), ([7,10,22], -16), ([8,10,22], -16), ([9,10,22], -16), ([10,10,22], -16), ([10,11,22], -16), ([10,12,22], -16), ([10,13,22], -16), ([10,14,22], -16), ([10,15,22], -16), ([10,16,22], -16), ([10,17,22], -16), ([10,18,22], -8), ([10,19,22], -4), ([10,20,22], 4), ([10,21,22], 6), ([10,22,22], 10), ([10,22,23], 18)]
theorem atom0022_data : atom0022 = SparsePolynomial.monoTimes [10,22] 1 base02 := by decide +kernel
theorem eval_atom0022 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0022 = (quadA (outer g) ![2,1,2] * g 10 * g 22) := by
  rw [atom0022_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0022_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6953120185920 : Int) atom0022) := by
  rw [SparsePolynomial.eval_scale, eval_atom0022]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 10 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0022Coded : CoefficientMerge.Poly := [(262, -4), (838, -12), (1414, -16), (1990, -16), (2566, -16), (3142, -16), (3718, -16), (4294, -16), (4870, -16), (5446, -16), (6022, -16), (6046, -16), (6070, -16), (6094, -16), (6118, -16), (6142, -16), (6166, -16), (6190, -16), (6214, -8), (6238, -4), (6262, 4), (6286, 6), (6310, 10), (6311, 18)]
theorem atom0022Coded_decode : atom0022 = SparsePolynomial.decodeCubic 24 atom0022Coded := by decide +kernel
theorem atom0022Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6953120185920 : Int) atom0022Coded) := by
  have h := atom0022_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0022Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0023 : SparsePolynomial.Poly := [([0,10,23], -4), ([1,10,23], -12), ([2,10,23], -16), ([3,10,23], -16), ([4,10,23], -16), ([5,10,23], -16), ([6,10,23], -16), ([7,10,23], -16), ([8,10,23], -16), ([9,10,23], -16), ([10,10,23], -16), ([10,11,23], -16), ([10,12,23], -16), ([10,13,23], -16), ([10,14,23], -16), ([10,15,23], -16), ([10,16,23], -16), ([10,17,23], -16), ([10,18,23], -8), ([10,19,23], -4), ([10,20,23], 4), ([10,21,23], 6), ([10,22,23], 10), ([10,23,23], 18)]
theorem atom0023_data : atom0023 = SparsePolynomial.monoTimes [10,23] 1 base02 := by decide +kernel
theorem eval_atom0023 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0023 = (quadA (outer g) ![2,1,2] * g 10 * g 23) := by
  rw [atom0023_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0023_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2025030241728 : Int) atom0023) := by
  rw [SparsePolynomial.eval_scale, eval_atom0023]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 10 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0023Coded : CoefficientMerge.Poly := [(263, -4), (839, -12), (1415, -16), (1991, -16), (2567, -16), (3143, -16), (3719, -16), (4295, -16), (4871, -16), (5447, -16), (6023, -16), (6047, -16), (6071, -16), (6095, -16), (6119, -16), (6143, -16), (6167, -16), (6191, -16), (6215, -8), (6239, -4), (6263, 4), (6287, 6), (6311, 10), (6335, 18)]
theorem atom0023Coded_decode : atom0023 = SparsePolynomial.decodeCubic 24 atom0023Coded := by decide +kernel
theorem atom0023Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2025030241728 : Int) atom0023Coded) := by
  have h := atom0023_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0023Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0024 : SparsePolynomial.Poly := [([0,11,22], -4), ([1,11,22], -12), ([2,11,22], -16), ([3,11,22], -16), ([4,11,22], -16), ([5,11,22], -16), ([6,11,22], -16), ([7,11,22], -16), ([8,11,22], -16), ([9,11,22], -16), ([10,11,22], -16), ([11,11,22], -16), ([11,12,22], -16), ([11,13,22], -16), ([11,14,22], -16), ([11,15,22], -16), ([11,16,22], -16), ([11,17,22], -16), ([11,18,22], -8), ([11,19,22], -4), ([11,20,22], 4), ([11,21,22], 6), ([11,22,22], 10), ([11,22,23], 18)]
theorem atom0024_data : atom0024 = SparsePolynomial.monoTimes [11,22] 1 base02 := by decide +kernel
theorem eval_atom0024 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0024 = (quadA (outer g) ![2,1,2] * g 11 * g 22) := by
  rw [atom0024_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0024_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38098109760 : Int) atom0024) := by
  rw [SparsePolynomial.eval_scale, eval_atom0024]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 11 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0024Coded : CoefficientMerge.Poly := [(286, -4), (862, -12), (1438, -16), (2014, -16), (2590, -16), (3166, -16), (3742, -16), (4318, -16), (4894, -16), (5470, -16), (6046, -16), (6622, -16), (6646, -16), (6670, -16), (6694, -16), (6718, -16), (6742, -16), (6766, -16), (6790, -8), (6814, -4), (6838, 4), (6862, 6), (6886, 10), (6887, 18)]
theorem atom0024Coded_decode : atom0024 = SparsePolynomial.decodeCubic 24 atom0024Coded := by decide +kernel
theorem atom0024Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (38098109760 : Int) atom0024Coded) := by
  have h := atom0024_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0024Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0025 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -16), ([4,4,4], -16), ([4,4,5], -16), ([4,4,6], -16), ([4,4,7], -16), ([4,4,8], -16), ([4,4,9], -16), ([4,4,10], -16), ([4,4,11], -16), ([4,4,12], -16), ([4,4,13], -16), ([4,4,14], -16), ([4,4,15], -16), ([4,4,16], -16), ([4,4,17], -16), ([4,4,18], -14), ([4,4,19], -10), ([4,4,20], -6), ([4,4,21], 2), ([4,4,22], 10), ([4,4,23], 18)]
theorem atom0025_data : atom0025 = SparsePolynomial.monoTimes [4,4] 1 base03 := by decide +kernel
theorem eval_atom0025 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0025 = (quadA (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0025_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0025_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1080956872800 : Int) atom0025) := by
  rw [SparsePolynomial.eval_scale, eval_atom0025]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0025Coded : CoefficientMerge.Poly := [(100, -8), (676, -12), (1252, -16), (1828, -16), (2404, -16), (2405, -16), (2406, -16), (2407, -16), (2408, -16), (2409, -16), (2410, -16), (2411, -16), (2412, -16), (2413, -16), (2414, -16), (2415, -16), (2416, -16), (2417, -16), (2418, -14), (2419, -10), (2420, -6), (2421, 2), (2422, 10), (2423, 18)]
theorem atom0025Coded_decode : atom0025 = SparsePolynomial.decodeCubic 24 atom0025Coded := by decide +kernel
theorem atom0025Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1080956872800 : Int) atom0025Coded) := by
  have h := atom0025_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0025Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0026 : SparsePolynomial.Poly := [([0,5,5], -8), ([1,5,5], -12), ([2,5,5], -16), ([3,5,5], -16), ([4,5,5], -16), ([5,5,5], -16), ([5,5,6], -16), ([5,5,7], -16), ([5,5,8], -16), ([5,5,9], -16), ([5,5,10], -16), ([5,5,11], -16), ([5,5,12], -16), ([5,5,13], -16), ([5,5,14], -16), ([5,5,15], -16), ([5,5,16], -16), ([5,5,17], -16), ([5,5,18], -14), ([5,5,19], -10), ([5,5,20], -6), ([5,5,21], 2), ([5,5,22], 10), ([5,5,23], 18)]
theorem atom0026_data : atom0026 = SparsePolynomial.monoTimes [5,5] 1 base03 := by decide +kernel
theorem eval_atom0026 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0026 = (quadA (outer g) ![2,2,1] * g 5 * g 5) := by
  rw [atom0026_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0026_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2184140851200 : Int) atom0026) := by
  rw [SparsePolynomial.eval_scale, eval_atom0026]
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 5 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0026Coded : CoefficientMerge.Poly := [(125, -8), (701, -12), (1277, -16), (1853, -16), (2429, -16), (3005, -16), (3006, -16), (3007, -16), (3008, -16), (3009, -16), (3010, -16), (3011, -16), (3012, -16), (3013, -16), (3014, -16), (3015, -16), (3016, -16), (3017, -16), (3018, -14), (3019, -10), (3020, -6), (3021, 2), (3022, 10), (3023, 18)]
theorem atom0026Coded_decode : atom0026 = SparsePolynomial.decodeCubic 24 atom0026Coded := by decide +kernel
theorem atom0026Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2184140851200 : Int) atom0026Coded) := by
  have h := atom0026_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0026Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0027 : SparsePolynomial.Poly := [([0,6,6], -8), ([1,6,6], -12), ([2,6,6], -16), ([3,6,6], -16), ([4,6,6], -16), ([5,6,6], -16), ([6,6,6], -16), ([6,6,7], -16), ([6,6,8], -16), ([6,6,9], -16), ([6,6,10], -16), ([6,6,11], -16), ([6,6,12], -16), ([6,6,13], -16), ([6,6,14], -16), ([6,6,15], -16), ([6,6,16], -16), ([6,6,17], -16), ([6,6,18], -14), ([6,6,19], -10), ([6,6,20], -6), ([6,6,21], 2), ([6,6,22], 10), ([6,6,23], 18)]
theorem atom0027_data : atom0027 = SparsePolynomial.monoTimes [6,6] 1 base03 := by decide +kernel
theorem eval_atom0027 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0027 = (quadA (outer g) ![2,2,1] * g 6 * g 6) := by
  rw [atom0027_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0027_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4146158016000 : Int) atom0027) := by
  rw [SparsePolynomial.eval_scale, eval_atom0027]
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 6 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0027Coded : CoefficientMerge.Poly := [(150, -8), (726, -12), (1302, -16), (1878, -16), (2454, -16), (3030, -16), (3606, -16), (3607, -16), (3608, -16), (3609, -16), (3610, -16), (3611, -16), (3612, -16), (3613, -16), (3614, -16), (3615, -16), (3616, -16), (3617, -16), (3618, -14), (3619, -10), (3620, -6), (3621, 2), (3622, 10), (3623, 18)]
theorem atom0027Coded_decode : atom0027 = SparsePolynomial.decodeCubic 24 atom0027Coded := by decide +kernel
theorem atom0027Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4146158016000 : Int) atom0027Coded) := by
  have h := atom0027_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0027Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0028 : SparsePolynomial.Poly := [([0,6,7], -8), ([1,6,7], -12), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -16), ([6,7,10], -16), ([6,7,11], -16), ([6,7,12], -16), ([6,7,13], -16), ([6,7,14], -16), ([6,7,15], -16), ([6,7,16], -16), ([6,7,17], -16), ([6,7,18], -14), ([6,7,19], -10), ([6,7,20], -6), ([6,7,21], 2), ([6,7,22], 10), ([6,7,23], 18)]
theorem atom0028_data : atom0028 = SparsePolynomial.monoTimes [6,7] 1 base03 := by decide +kernel
theorem eval_atom0028 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0028 = (quadA (outer g) ![2,2,1] * g 6 * g 7) := by
  rw [atom0028_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0028_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2572271708160 : Int) atom0028) := by
  rw [SparsePolynomial.eval_scale, eval_atom0028]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0028Coded : CoefficientMerge.Poly := [(151, -8), (727, -12), (1303, -16), (1879, -16), (2455, -16), (3031, -16), (3607, -16), (3631, -16), (3632, -16), (3633, -16), (3634, -16), (3635, -16), (3636, -16), (3637, -16), (3638, -16), (3639, -16), (3640, -16), (3641, -16), (3642, -14), (3643, -10), (3644, -6), (3645, 2), (3646, 10), (3647, 18)]
theorem atom0028Coded_decode : atom0028 = SparsePolynomial.decodeCubic 24 atom0028Coded := by decide +kernel
theorem atom0028Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2572271708160 : Int) atom0028Coded) := by
  have h := atom0028_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0028Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0029 : SparsePolynomial.Poly := [([0,7,7], -8), ([1,7,7], -12), ([2,7,7], -16), ([3,7,7], -16), ([4,7,7], -16), ([5,7,7], -16), ([6,7,7], -16), ([7,7,7], -16), ([7,7,8], -16), ([7,7,9], -16), ([7,7,10], -16), ([7,7,11], -16), ([7,7,12], -16), ([7,7,13], -16), ([7,7,14], -16), ([7,7,15], -16), ([7,7,16], -16), ([7,7,17], -16), ([7,7,18], -14), ([7,7,19], -10), ([7,7,20], -6), ([7,7,21], 2), ([7,7,22], 10), ([7,7,23], 18)]
theorem atom0029_data : atom0029 = SparsePolynomial.monoTimes [7,7] 1 base03 := by decide +kernel
theorem eval_atom0029 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0029 = (quadA (outer g) ![2,2,1] * g 7 * g 7) := by
  rw [atom0029_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0029_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5310862233600 : Int) atom0029) := by
  rw [SparsePolynomial.eval_scale, eval_atom0029]
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 7 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0029Coded : CoefficientMerge.Poly := [(175, -8), (751, -12), (1327, -16), (1903, -16), (2479, -16), (3055, -16), (3631, -16), (4207, -16), (4208, -16), (4209, -16), (4210, -16), (4211, -16), (4212, -16), (4213, -16), (4214, -16), (4215, -16), (4216, -16), (4217, -16), (4218, -14), (4219, -10), (4220, -6), (4221, 2), (4222, 10), (4223, 18)]
theorem atom0029Coded_decode : atom0029 = SparsePolynomial.decodeCubic 24 atom0029Coded := by decide +kernel
theorem atom0029Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5310862233600 : Int) atom0029Coded) := by
  have h := atom0029_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0029Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0030 : SparsePolynomial.Poly := [([0,7,8], -8), ([1,7,8], -12), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -16), ([7,8,13], -16), ([7,8,14], -16), ([7,8,15], -16), ([7,8,16], -16), ([7,8,17], -16), ([7,8,18], -14), ([7,8,19], -10), ([7,8,20], -6), ([7,8,21], 2), ([7,8,22], 10), ([7,8,23], 18)]
theorem atom0030_data : atom0030 = SparsePolynomial.monoTimes [7,8] 1 base03 := by decide +kernel
theorem eval_atom0030 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0030 = (quadA (outer g) ![2,2,1] * g 7 * g 8) := by
  rw [atom0030_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0030_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1739053414560 : Int) atom0030) := by
  rw [SparsePolynomial.eval_scale, eval_atom0030]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0030Coded : CoefficientMerge.Poly := [(176, -8), (752, -12), (1328, -16), (1904, -16), (2480, -16), (3056, -16), (3632, -16), (4208, -16), (4232, -16), (4233, -16), (4234, -16), (4235, -16), (4236, -16), (4237, -16), (4238, -16), (4239, -16), (4240, -16), (4241, -16), (4242, -14), (4243, -10), (4244, -6), (4245, 2), (4246, 10), (4247, 18)]
theorem atom0030Coded_decode : atom0030 = SparsePolynomial.decodeCubic 24 atom0030Coded := by decide +kernel
theorem atom0030Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1739053414560 : Int) atom0030Coded) := by
  have h := atom0030_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0030Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0031 : SparsePolynomial.Poly := [([0,8,8], -8), ([1,8,8], -12), ([2,8,8], -16), ([3,8,8], -16), ([4,8,8], -16), ([5,8,8], -16), ([6,8,8], -16), ([7,8,8], -16), ([8,8,8], -16), ([8,8,9], -16), ([8,8,10], -16), ([8,8,11], -16), ([8,8,12], -16), ([8,8,13], -16), ([8,8,14], -16), ([8,8,15], -16), ([8,8,16], -16), ([8,8,17], -16), ([8,8,18], -14), ([8,8,19], -10), ([8,8,20], -6), ([8,8,21], 2), ([8,8,22], 10), ([8,8,23], 18)]
theorem atom0031_data : atom0031 = SparsePolynomial.monoTimes [8,8] 1 base03 := by decide +kernel
theorem eval_atom0031 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0031 = (quadA (outer g) ![2,2,1] * g 8 * g 8) := by
  rw [atom0031_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0031_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7037837452800 : Int) atom0031) := by
  rw [SparsePolynomial.eval_scale, eval_atom0031]
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 8 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0031Coded : CoefficientMerge.Poly := [(200, -8), (776, -12), (1352, -16), (1928, -16), (2504, -16), (3080, -16), (3656, -16), (4232, -16), (4808, -16), (4809, -16), (4810, -16), (4811, -16), (4812, -16), (4813, -16), (4814, -16), (4815, -16), (4816, -16), (4817, -16), (4818, -14), (4819, -10), (4820, -6), (4821, 2), (4822, 10), (4823, 18)]
theorem atom0031Coded_decode : atom0031 = SparsePolynomial.decodeCubic 24 atom0031Coded := by decide +kernel
theorem atom0031Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7037837452800 : Int) atom0031Coded) := by
  have h := atom0031_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0031Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0032 : SparsePolynomial.Poly := [([0,8,9], -8), ([1,8,9], -12), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -16), ([8,9,13], -16), ([8,9,14], -16), ([8,9,15], -16), ([8,9,16], -16), ([8,9,17], -16), ([8,9,18], -14), ([8,9,19], -10), ([8,9,20], -6), ([8,9,21], 2), ([8,9,22], 10), ([8,9,23], 18)]
theorem atom0032_data : atom0032 = SparsePolynomial.monoTimes [8,9] 1 base03 := by decide +kernel
theorem eval_atom0032 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0032 = (quadA (outer g) ![2,2,1] * g 8 * g 9) := by
  rw [atom0032_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0032_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4195405665792 : Int) atom0032) := by
  rw [SparsePolynomial.eval_scale, eval_atom0032]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0032Coded : CoefficientMerge.Poly := [(201, -8), (777, -12), (1353, -16), (1929, -16), (2505, -16), (3081, -16), (3657, -16), (4233, -16), (4809, -16), (4833, -16), (4834, -16), (4835, -16), (4836, -16), (4837, -16), (4838, -16), (4839, -16), (4840, -16), (4841, -16), (4842, -14), (4843, -10), (4844, -6), (4845, 2), (4846, 10), (4847, 18)]
theorem atom0032Coded_decode : atom0032 = SparsePolynomial.decodeCubic 24 atom0032Coded := by decide +kernel
theorem atom0032Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4195405665792 : Int) atom0032Coded) := by
  have h := atom0032_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0032Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0033 : SparsePolynomial.Poly := [([0,8,10], -8), ([1,8,10], -12), ([2,8,10], -16), ([3,8,10], -16), ([4,8,10], -16), ([5,8,10], -16), ([6,8,10], -16), ([7,8,10], -16), ([8,8,10], -16), ([8,9,10], -16), ([8,10,10], -16), ([8,10,11], -16), ([8,10,12], -16), ([8,10,13], -16), ([8,10,14], -16), ([8,10,15], -16), ([8,10,16], -16), ([8,10,17], -16), ([8,10,18], -14), ([8,10,19], -10), ([8,10,20], -6), ([8,10,21], 2), ([8,10,22], 10), ([8,10,23], 18)]
theorem atom0033_data : atom0033 = SparsePolynomial.monoTimes [8,10] 1 base03 := by decide +kernel
theorem eval_atom0033 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0033 = (quadA (outer g) ![2,2,1] * g 8 * g 10) := by
  rw [atom0033_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0033_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1378144449792 : Int) atom0033) := by
  rw [SparsePolynomial.eval_scale, eval_atom0033]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 8 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0033Coded : CoefficientMerge.Poly := [(202, -8), (778, -12), (1354, -16), (1930, -16), (2506, -16), (3082, -16), (3658, -16), (4234, -16), (4810, -16), (4834, -16), (4858, -16), (4859, -16), (4860, -16), (4861, -16), (4862, -16), (4863, -16), (4864, -16), (4865, -16), (4866, -14), (4867, -10), (4868, -6), (4869, 2), (4870, 10), (4871, 18)]
theorem atom0033Coded_decode : atom0033 = SparsePolynomial.decodeCubic 24 atom0033Coded := by decide +kernel
theorem atom0033Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1378144449792 : Int) atom0033Coded) := by
  have h := atom0033_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0033Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0034 : SparsePolynomial.Poly := [([0,9,9], -8), ([1,9,9], -12), ([2,9,9], -16), ([3,9,9], -16), ([4,9,9], -16), ([5,9,9], -16), ([6,9,9], -16), ([7,9,9], -16), ([8,9,9], -16), ([9,9,9], -16), ([9,9,10], -16), ([9,9,11], -16), ([9,9,12], -16), ([9,9,13], -16), ([9,9,14], -16), ([9,9,15], -16), ([9,9,16], -16), ([9,9,17], -16), ([9,9,18], -14), ([9,9,19], -10), ([9,9,20], -6), ([9,9,21], 2), ([9,9,22], 10), ([9,9,23], 18)]
theorem atom0034_data : atom0034 = SparsePolynomial.monoTimes [9,9] 1 base03 := by decide +kernel
theorem eval_atom0034 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0034 = (quadA (outer g) ![2,2,1] * g 9 * g 9) := by
  rw [atom0034_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0034_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8139571368192 : Int) atom0034) := by
  rw [SparsePolynomial.eval_scale, eval_atom0034]
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 9 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0034Coded : CoefficientMerge.Poly := [(225, -8), (801, -12), (1377, -16), (1953, -16), (2529, -16), (3105, -16), (3681, -16), (4257, -16), (4833, -16), (5409, -16), (5410, -16), (5411, -16), (5412, -16), (5413, -16), (5414, -16), (5415, -16), (5416, -16), (5417, -16), (5418, -14), (5419, -10), (5420, -6), (5421, 2), (5422, 10), (5423, 18)]
theorem atom0034Coded_decode : atom0034 = SparsePolynomial.decodeCubic 24 atom0034Coded := by decide +kernel
theorem atom0034Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8139571368192 : Int) atom0034Coded) := by
  have h := atom0034_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0034Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0035 : SparsePolynomial.Poly := [([0,9,10], -8), ([1,9,10], -12), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -16), ([9,10,13], -16), ([9,10,14], -16), ([9,10,15], -16), ([9,10,16], -16), ([9,10,17], -16), ([9,10,18], -14), ([9,10,19], -10), ([9,10,20], -6), ([9,10,21], 2), ([9,10,22], 10), ([9,10,23], 18)]
theorem atom0035_data : atom0035 = SparsePolynomial.monoTimes [9,10] 1 base03 := by decide +kernel
theorem eval_atom0035 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0035 = (quadA (outer g) ![2,2,1] * g 9 * g 10) := by
  rw [atom0035_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0035_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8281664607744 : Int) atom0035) := by
  rw [SparsePolynomial.eval_scale, eval_atom0035]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0035Coded : CoefficientMerge.Poly := [(226, -8), (802, -12), (1378, -16), (1954, -16), (2530, -16), (3106, -16), (3682, -16), (4258, -16), (4834, -16), (5410, -16), (5434, -16), (5435, -16), (5436, -16), (5437, -16), (5438, -16), (5439, -16), (5440, -16), (5441, -16), (5442, -14), (5443, -10), (5444, -6), (5445, 2), (5446, 10), (5447, 18)]
theorem atom0035Coded_decode : atom0035 = SparsePolynomial.decodeCubic 24 atom0035Coded := by decide +kernel
theorem atom0035Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8281664607744 : Int) atom0035Coded) := by
  have h := atom0035_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0035Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0036 : SparsePolynomial.Poly := [([0,10,10], -8), ([1,10,10], -12), ([2,10,10], -16), ([3,10,10], -16), ([4,10,10], -16), ([5,10,10], -16), ([6,10,10], -16), ([7,10,10], -16), ([8,10,10], -16), ([9,10,10], -16), ([10,10,10], -16), ([10,10,11], -16), ([10,10,12], -16), ([10,10,13], -16), ([10,10,14], -16), ([10,10,15], -16), ([10,10,16], -16), ([10,10,17], -16), ([10,10,18], -14), ([10,10,19], -10), ([10,10,20], -6), ([10,10,21], 2), ([10,10,22], 10), ([10,10,23], 18)]
theorem atom0036_data : atom0036 = SparsePolynomial.monoTimes [10,10] 1 base03 := by decide +kernel
theorem eval_atom0036 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0036 = (quadA (outer g) ![2,2,1] * g 10 * g 10) := by
  rw [atom0036_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0036_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7505953373952 : Int) atom0036) := by
  rw [SparsePolynomial.eval_scale, eval_atom0036]
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 10 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0036Coded : CoefficientMerge.Poly := [(250, -8), (826, -12), (1402, -16), (1978, -16), (2554, -16), (3130, -16), (3706, -16), (4282, -16), (4858, -16), (5434, -16), (6010, -16), (6011, -16), (6012, -16), (6013, -16), (6014, -16), (6015, -16), (6016, -16), (6017, -16), (6018, -14), (6019, -10), (6020, -6), (6021, 2), (6022, 10), (6023, 18)]
theorem atom0036Coded_decode : atom0036 = SparsePolynomial.decodeCubic 24 atom0036Coded := by decide +kernel
theorem atom0036Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7505953373952 : Int) atom0036Coded) := by
  have h := atom0036_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0036Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0037 : SparsePolynomial.Poly := [([0,10,11], -8), ([1,10,11], -12), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -16), ([10,11,13], -16), ([10,11,14], -16), ([10,11,15], -16), ([10,11,16], -16), ([10,11,17], -16), ([10,11,18], -14), ([10,11,19], -10), ([10,11,20], -6), ([10,11,21], 2), ([10,11,22], 10), ([10,11,23], 18)]
theorem atom0037_data : atom0037 = SparsePolynomial.monoTimes [10,11] 1 base03 := by decide +kernel
theorem eval_atom0037 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0037 = (quadA (outer g) ![2,2,1] * g 10 * g 11) := by
  rw [atom0037_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0037_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4857012757872 : Int) atom0037) := by
  rw [SparsePolynomial.eval_scale, eval_atom0037]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0037Coded : CoefficientMerge.Poly := [(251, -8), (827, -12), (1403, -16), (1979, -16), (2555, -16), (3131, -16), (3707, -16), (4283, -16), (4859, -16), (5435, -16), (6011, -16), (6035, -16), (6036, -16), (6037, -16), (6038, -16), (6039, -16), (6040, -16), (6041, -16), (6042, -14), (6043, -10), (6044, -6), (6045, 2), (6046, 10), (6047, 18)]
theorem atom0037Coded_decode : atom0037 = SparsePolynomial.decodeCubic 24 atom0037Coded := by decide +kernel
theorem atom0037Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4857012757872 : Int) atom0037Coded) := by
  have h := atom0037_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0037Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0038 : SparsePolynomial.Poly := [([0,11,11], -8), ([1,11,11], -12), ([2,11,11], -16), ([3,11,11], -16), ([4,11,11], -16), ([5,11,11], -16), ([6,11,11], -16), ([7,11,11], -16), ([8,11,11], -16), ([9,11,11], -16), ([10,11,11], -16), ([11,11,11], -16), ([11,11,12], -16), ([11,11,13], -16), ([11,11,14], -16), ([11,11,15], -16), ([11,11,16], -16), ([11,11,17], -16), ([11,11,18], -14), ([11,11,19], -10), ([11,11,20], -6), ([11,11,21], 2), ([11,11,22], 10), ([11,11,23], 18)]
theorem atom0038_data : atom0038 = SparsePolynomial.monoTimes [11,11] 1 base03 := by decide +kernel
theorem eval_atom0038 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0038 = (quadA (outer g) ![2,2,1] * g 11 * g 11) := by
  rw [atom0038_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0038_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5186234916720 : Int) atom0038) := by
  rw [SparsePolynomial.eval_scale, eval_atom0038]
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 11 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0038Coded : CoefficientMerge.Poly := [(275, -8), (851, -12), (1427, -16), (2003, -16), (2579, -16), (3155, -16), (3731, -16), (4307, -16), (4883, -16), (5459, -16), (6035, -16), (6611, -16), (6612, -16), (6613, -16), (6614, -16), (6615, -16), (6616, -16), (6617, -16), (6618, -14), (6619, -10), (6620, -6), (6621, 2), (6622, 10), (6623, 18)]
theorem atom0038Coded_decode : atom0038 = SparsePolynomial.decodeCubic 24 atom0038Coded := by decide +kernel
theorem atom0038Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5186234916720 : Int) atom0038Coded) := by
  have h := atom0038_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0038Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block000 : CoefficientMerge.Poly := [(43, -16797255552000), (45, -1091467238400), (46, -3119551680000), (47, -5333305824000), (94, -13295088979200), (100, -8647654982400), (118, -33627424790400), (125, -17473126809600), (142, -48041084448000), (143, -40036026038400), (150, -33169264128000), (151, -21911322935040), (166, -62113441824000), (167, -50998387910400), (175, -42486897868800), (176, -29634871136640), (177, -1882363965768), (190, -64803522694400), (191, -51195064636800), (200, -56302699622400), (201, -48035817409536), (202, -11275121719224), (214, -65175220051200), (215, -48783559910400), (225, -65116570945536), (226, -66253316861952), (238, -55311785191680), (239, -36638799898752), (250, -60047626991616), (251, -38856102062976), (262, -27812480743680), (263, -8100120966912), (275, -41489879333760), (286, -152392439040), (619, -50391766656000), (621, -3274401715200), (622, -9419220518400), (623, -15999917472000), (643, -67189022208000), (645, -4365868953600), (646, -12599337676800), (647, -21333223296000), (667, -67189022208000), (669, -4365868953600), (670, -52484604614400), (671, -21333223296000), (676, -12971482473600), (691, -67189022208000), (693, -4365868953600), (694, -113481612048000), (695, -21333223296000), (701, -26209690214400), (715, -67189022208000), (717, -4365868953600), (718, -156722591020800), (719, -141441301411200), (726, -49753896192000), (727, -33533559037440), (739, -67189022208000), (741, -4365868953600), (742, -198939663148800), (743, -174328387027200), (751, -63730346803200), (752, -52313528615040), (753, -3764727931536), (763, -67189022208000), (765, -4365868953600), (766, -207009905760000), (767, -174918417206400), (776, -84454049433600), (777, -79290012155904), (778, -17037665639280), (787, -67189022208000), (789, -4365868953600), (790, -208124997830400), (791, -167683903027200), (801, -97674856418304), (802, -99379975292928), (811, -67189022208000), (813, -4365868953600), (814, -178534693251840), (815, -131249622992256), (826, -90071440487424), (827, -58284153094464), (835, -67189022208000), (837, -4365868953600), (838, -96036779907840), (839, -45633586196736), (851, -62234819000640), (859, -67189022208000), (861, -4365868953600), (862, -13056514993920), (863, -21333223296000), (883, -67189022208000), (885, -4365868953600), (886, -12599337676800), (887, -21333223296000), (907, -67189022208000), (909, -4365868953600), (910, -12599337676800), (911, -21333223296000), (931, -67189022208000), (933, -4365868953600), (934, -12599337676800), (935, -21333223296000), (955, -67189022208000), (957, -4365868953600), (958, -12599337676800), (959, -21333223296000), (979, -67189022208000), (981, -4365868953600), (982, -12599337676800), (983, -21333223296000), (1003, -67189022208000), (1005, -4365868953600), (1006, -12599337676800), (1007, -21333223296000), (1027, -33594511104000), (1029, -2182934476800), (1030, -6360234316800), (1031, -10666611648000), (1051, -16797255552000), (1052, 16797255552000), (1053, 24104416089600), (1054, 38752456243200), (1055, 70254344160000), (1077, 1091467238400), (1078, 3119551680000), (1079, 5333305824000), (1101, 1637200857600), (1102, 7407995616000), (1103, 12911561308800), (1126, 7798879200000), (1127, 27371247120000), (1151, 23999876208000), (1222, -60565478400), (1246, -53301486873600), (1252, -17295309964800), (1270, -134630830118400), (1277, -34946253619200), (1294, -192285468748800), (1295, -160144104153600), (1302, -66338528256000), (1303, -46488944409600), (1318, -248574898252800), (1319, -203993551641600), (1327, -84973795737600), (1328, -90714629913600), (1329, -7529455863072), (1342, -259335221734400), (1343, -204780258547200), (1352, -112605399244800), (1353, -125016778985472), (1354, -23050175680224), (1366, -260822011161600), (1367, -195134239641600), (1377, -130233141891072), (1378, -132506633723904), (1390, -221368271723520), (1391, -146555199595008), (1402, -120095253983232), (1403, -77712204125952), (1414, -111371053931520), (1415, -32400483867648), (1427, -82979758667520), (1438, -730700712960), (1462, -121130956800), (1486, -121130956800), (1510, -121130956800), (1534, -121130956800), (1558, -121130956800), (1582, -121130956800), (1606, -121130956800), (1630, -121130956800), (1822, -53240921395200), (1828, -17295309964800), (1846, -187811186035200), (1853, -34946253619200), (1870, -245465824665600), (1871, -160144104153600), (1878, -66338528256000), (1879, -46488944409600), (1894, -301755254169600), (1895, -203993551641600), (1903, -84973795737600), (1904, -90714629913600), (1905, -7529455863072), (1918, -312515577651200), (1919, -204780258547200), (1928, -112605399244800), (1929, -125016778985472), (1930, -23050175680224), (1942, -314002367078400), (1943, -195134239641600), (1953, -130233141891072), (1954, -132506633723904), (1966, -274548627640320), (1967, -146555199595008), (1978, -120095253983232), (1979, -77712204125952), (1990, -164551409848320), (1991, -32400483867648), (2003, -82979758667520), (2014, -53911056629760), (2038, -53301486873600), (2062, -53301486873600), (2086, -53301486873600), (2110, -53301486873600), (2134, -53301486873600), (2158, -53301486873600), (2182, -26711308915200), (2206, -13416219936000), (2230, 13295088979200), (2254, 19942633468800), (2278, 33237722448000), (2279, 59827900406400), (2404, -17295309964800), (2405, -17295309964800), (2406, -17295309964800), (2407, -17295309964800), (2408, -17295309964800), (2409, -17295309964800), (2410, -17295309964800), (2411, -17295309964800), (2412, -17295309964800), (2413, -17295309964800), (2414, -17295309964800), (2415, -17295309964800), (2416, -17295309964800), (2417, -17295309964800), (2418, -15133396219200), (2419, -10809568728000), (2420, -6485741236800), (2421, 2161913745600), (2422, -123760695912000), (2423, 19457223710400), (2429, -34946253619200), (2446, -326795167910400), (2447, -160144104153600), (2454, -66338528256000), (2455, -46488944409600), (2470, -383084597414400), (2471, -203993551641600), (2479, -84973795737600), (2480, -90714629913600), (2481, -7529455863072), (2494, -393844920896000), (2495, -204780258547200), (2504, -112605399244800), (2505, -125016778985472), (2506, -23050175680224), (2518, -395331710323200), (2519, -195134239641600), (2529, -130233141891072), (2530, -132506633723904), (2542, -355877970885120), (2543, -146555199595008), (2554, -120095253983232), (2555, -77712204125952), (2566, -245880753093120), (2567, -32400483867648), (2579, -82979758667520), (2590, -135240399874560), (2614, -134630830118400), (2638, -134630830118400), (2662, -134630830118400), (2686, -134630830118400), (2710, -134630830118400), (2734, -134630830118400), (2758, -67375980537600), (2782, -33748555747200), (2806, 33627424790400), (2830, 50441137185600), (2854, 84068561976000), (2855, 151323411556800), (3005, -34946253619200), (3006, -34946253619200), (3007, -34946253619200), (3008, -34946253619200), (3009, -34946253619200), (3010, -34946253619200), (3011, -34946253619200), (3012, -34946253619200), (3013, -34946253619200), (3014, -34946253619200), (3015, -34946253619200), (3016, -34946253619200), (3017, -34946253619200), (3018, -30577971916800), (3019, -21841408512000), (3020, -13104845107200), (3021, 4368281702400), (3022, -170383494758400), (3023, -120829568832000), (3030, -66338528256000), (3031, -46488944409600), (3046, -440739236044800), (3047, -364137655795200), (3055, -84973795737600), (3056, -90714629913600), (3057, -7529455863072), (3070, -451499559526400), (3071, -364924362700800), (3080, -112605399244800), (3081, -125016778985472), (3082, -23050175680224), (3094, -452986348953600), (3095, -355278343795200), (3105, -130233141891072), (3106, -132506633723904), (3118, -413532609515520), (3119, -306699303748608), (3130, -120095253983232), (3131, -77712204125952), (3142, -303535391723520), (3143, -192544588021248), (3155, -82979758667520), (3166, -192895038504960), (3167, -160144104153600), (3190, -192285468748800), (3191, -160144104153600), (3214, -192285468748800), (3215, -160144104153600), (3238, -192285468748800), (3239, -160144104153600), (3262, -192285468748800), (3263, -160144104153600), (3286, -192285468748800), (3287, -160144104153600), (3310, -192285468748800), (3311, -160144104153600), (3334, -96203299852800), (3335, -80072052076800), (3358, -48162215404800), (3359, -40036026038400), (3382, 48041084448000), (3383, 40036026038400), (3406, 72061626672000), (3407, 60054039057600), (3430, 120102711120000), (3431, 316274945112000), (3455, 180162117172800), (3606, -66338528256000), (3607, -112827472665600), (3608, -66338528256000), (3609, -66338528256000), (3610, -66338528256000), (3611, -66338528256000), (3612, -66338528256000), (3613, -66338528256000), (3614, -66338528256000), (3615, -66338528256000), (3616, -66338528256000), (3617, -66338528256000), (3618, -58046212224000), (3619, -41461580160000), (3620, -24876948096000), (3621, 8292316032000), (3622, -207052752614400), (3623, -129362707353600), (3631, -131462740147200), (3632, -137203574323200), (3633, -54018400272672), (3634, -46488944409600), (3635, -46488944409600), (3636, -46488944409600), (3637, -46488944409600), (3638, -46488944409600), (3639, -46488944409600), (3640, -46488944409600), (3641, -46488944409600), (3642, -38678102453760), (3643, -25722717081600), (3644, -14100480979200), (3645, 9143991225600), (3646, -476733674869760), (3647, -356473747728000), (3656, -112605399244800), (3657, -125016778985472), (3658, -23050175680224), (3670, -509275778457600), (3671, -399127791283200), (3681, -130233141891072), (3682, -132506633723904), (3694, -469822039019520), (3695, -350548751236608), (3706, -120095253983232), (3707, -77712204125952), (3718, -359824821227520), (3719, -236394035509248), (3731, -82979758667520), (3742, -249184468008960), (3743, -203993551641600), (3766, -248574898252800), (3767, -203993551641600), (3790, -248574898252800), (3791, -203993551641600), (3814, -248574898252800), (3815, -203993551641600), (3838, -248574898252800), (3839, -203993551641600), (3862, -248574898252800), (3863, -203993551641600), (3886, -248574898252800), (3887, -203993551641600), (3910, -124348014604800), (3911, -101996775820800), (3934, -62234572780800), (3935, -50998387910400), (3958, 62113441824000), (3959, 50998387910400), (3982, 93170162736000), (3983, 76497581865600), (4006, 155283604560000), (4007, 407006457984000), (4031, 229492745596800), (4207, -84973795737600), (4208, -175688425651200), (4209, -92503251600672), (4210, -84973795737600), (4211, -84973795737600), (4212, -84973795737600), (4213, -84973795737600), (4214, -84973795737600), (4215, -84973795737600), (4216, -84973795737600), (4217, -84973795737600), (4218, -74352071270400), (4219, -53108622336000), (4220, -31865173401600), (4221, 10621724467200), (4222, -206166033920000), (4223, -109184738342400), (4232, -203320029158400), (4233, -223260864762144), (4234, -113764805593824), (4235, -90714629913600), (4236, -90714629913600), (4237, -90714629913600), (4238, -90714629913600), (4239, -90714629913600), (4240, -90714629913600), (4241, -90714629913600), (4242, -55791635444160), (4243, -17390534145600), (4244, 5288123332800), (4245, 50645438289600), (4246, -439755792512960), (4247, -297860539536000), (4257, -137762597754144), (4258, -140036089586976), (4259, -7529455863072), (4260, -7529455863072), (4261, -7529455863072), (4262, -7529455863072), (4263, -7529455863072), (4264, -7529455863072), (4265, -7529455863072), (4266, -3764727931536), (4268, 1882363965768), (4269, 5647091897304), (4270, -473052906638048), (4271, -342864820296252), (4282, -120095253983232), (4283, -77712204125952), (4294, -370585144709120), (4295, -237180742414848), (4307, -82979758667520), (4318, -259944791490560), (4319, -204780258547200), (4342, -259335221734400), (4343, -204780258547200), (4366, -259335221734400), (4367, -204780258547200), (4390, -259335221734400), (4391, -204780258547200), (4414, -259335221734400), (4415, -204780258547200), (4438, -259335221734400), (4439, -204780258547200), (4462, -259335221734400), (4463, -204780258547200), (4486, -129728176345600), (4487, -102390129273600), (4510, -64924653651200), (4511, -51195064636800), (4534, 64803522694400), (4535, 51195064636800), (4558, 97205284041600), (4559, 76792596955200), (4582, 162008806736000), (4583, 419603513716800), (4607, 230377790865600), (4808, -112605399244800), (4809, -237622178230272), (4810, -135655574925024), (4811, -112605399244800), (4812, -112605399244800), (4813, -112605399244800), (4814, -112605399244800), (4815, -112605399244800), (4816, -112605399244800), (4817, -112605399244800), (4818, -98529724339200), (4819, -70378374528000), (4820, -42227024716800), (4821, 14075674905600), (4822, -190383071155200), (4823, -68453165491200), (4833, -255249920876544), (4834, -280573588389600), (4835, -125016778985472), (4836, -125016778985472), (4837, -125016778985472), (4838, -125016778985472), (4839, -125016778985472), (4840, -125016778985472), (4841, -125016778985472), (4842, -87680823487488), (4843, -41954056657920), (4844, -10699861911552), (4845, 51808527581184), (4846, -382224806937600), (4847, -201045562877952), (4858, -143145429663456), (4859, -100762379806176), (4860, -23050175680224), (4861, -23050175680224), (4862, -23050175680224), (4863, -23050175680224), (4864, -23050175680224), (4865, -23050175680224), (4866, -19793954538864), (4867, -13781444497920), (4868, -8018900577864), (4869, 3506187262248), (4870, -357290625154848), (4871, -201603275868996), (4883, -82979758667520), (4894, -261431580917760), (4895, -195134239641600), (4918, -260822011161600), (4919, -195134239641600), (4942, -260822011161600), (4943, -195134239641600), (4966, -260822011161600), (4967, -195134239641600), (4990, -260822011161600), (4991, -195134239641600), (5014, -260822011161600), (5015, -195134239641600), (5038, -260822011161600), (5039, -195134239641600), (5062, -130471571059200), (5063, -97567119820800), (5086, -65296351008000), (5087, -48783559910400), (5110, 65175220051200), (5111, 48783559910400), (5134, 97762830076800), (5135, 73175339865600), (5158, 162938050128000), (5159, 415247390006400), (5183, 219526019596800), (5409, -130233141891072), (5410, -262739775614976), (5411, -130233141891072), (5412, -130233141891072), (5413, -130233141891072), (5414, -130233141891072), (5415, -130233141891072), (5416, -130233141891072), (5417, -130233141891072), (5418, -113953999154688), (5419, -81395713681920), (5420, -48837428209152), (5421, 16279142736384), (5422, -139911992563200), (5423, -42914967552), (5434, -252601887707136), (5435, -210218837849856), (5436, -132506633723904), (5437, -132506633723904), (5438, -132506633723904), (5439, -132506633723904), (5440, -132506633723904), (5441, -132506633723904), (5442, -115943304508416), (5443, -82816646077440), (5444, -49689987646464), (5445, 16563329215488), (5446, -249801548620800), (5447, -29885720523264), (5459, -82979758667520), (5470, -221977841479680), (5471, -146555199595008), (5494, -221368271723520), (5495, -146555199595008), (5518, -221368271723520), (5519, -146555199595008), (5542, -221368271723520), (5543, -146555199595008), (5566, -221368271723520), (5567, -146555199595008), (5590, -221368271723520), (5591, -146555199595008), (5614, -221368271723520), (5615, -146555199595008), (5638, -110744701340160), (5639, -73277599797504), (5662, -55432916148480), (5663, -36638799898752), (5686, 55311785191680), (5687, 36638799898752), (5710, 82967677787520), (5711, 54958199848128), (5734, 138279462979200), (5735, 340500033109440), (5759, 164874599544384), (6010, -120095253983232), (6011, -197807458109184), (6012, -120095253983232), (6013, -120095253983232), (6014, -120095253983232), (6015, -120095253983232), (6016, -120095253983232), (6017, -120095253983232), (6018, -105083347235328), (6019, -75059533739520), (6020, -45035720243712), (6021, 15011906747904), (6022, -36250954713600), (6023, 102706676863488), (6035, -160691962793472), (6036, -77712204125952), (6037, -77712204125952), (6038, -77712204125952), (6039, -77712204125952), (6040, -77712204125952), (6041, -77712204125952), (6042, -67998178610208), (6043, -48570127578720), (6044, -29142076547232), (6045, 9714025515744), (6046, -63410496108960), (6047, 55025745774048), (6070, -111371053931520), (6071, -32400483867648), (6094, -111371053931520), (6095, -32400483867648), (6118, -111371053931520), (6119, -32400483867648), (6142, -111371053931520), (6143, -32400483867648), (6166, -111371053931520), (6167, -32400483867648), (6190, -111371053931520), (6191, -32400483867648), (6214, -55746092444160), (6215, -16200241933824), (6238, -27933611700480), (6239, -8100120966912), (6262, 27812480743680), (6263, 8100120966912), (6286, 41718721115520), (6287, 12150181450368), (6310, 69531201859200), (6311, 145406465763840), (6335, 36450544351104), (6611, -82979758667520), (6612, -82979758667520), (6613, -82979758667520), (6614, -82979758667520), (6615, -82979758667520), (6616, -82979758667520), (6617, -82979758667520), (6618, -72607288834080), (6619, -51862349167200), (6620, -31117409500320), (6621, 10372469833440), (6622, 51192213932640), (6623, 93352228500960), (6646, -730700712960), (6670, -730700712960), (6694, -730700712960), (6718, -730700712960), (6742, -730700712960), (6766, -730700712960), (6790, -425915834880), (6814, -273523395840), (6838, 152392439040), (6862, 228588658560), (6886, 380981097600), (6887, 685765975680), (7222, -60565478400), (7246, -121130956800), (7270, -121130956800), (7294, -121130956800), (7318, -121130956800), (7342, -121130956800), (7366, -121130956800), (7390, -121130956800), (7822, -60565478400), (7846, -121130956800), (7870, -121130956800), (7894, -121130956800), (7918, -121130956800), (7942, -121130956800), (7966, -121130956800), (8422, -60565478400), (8446, -121130956800), (8470, -121130956800), (8494, -121130956800), (8518, -121130956800), (8542, -121130956800), (9022, -60565478400), (9046, -121130956800), (9070, -121130956800), (9094, -121130956800), (9118, -121130956800), (9622, -60565478400), (9646, -121130956800), (9670, -121130956800), (9694, -121130956800), (10222, -60565478400), (10246, -121130956800), (10270, -121130956800), (10822, -60565478400), (10846, -121130956800), (10919, 242261913600), (11422, -60565478400), (11495, 242261913600), (12071, 242261913600), (12647, 242261913600), (13223, 242261913600), (13247, 242261913600)]
theorem block000_data : block000 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60565478400 : Int) atom0000Coded) (CoefficientMerge.scale (333287317440 : Int) atom0001Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3930610955040 : Int) atom0002Coded) (CoefficientMerge.scale (470590991442 : Int) atom0003Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3618143020800 : Int) atom0004Coded) (CoefficientMerge.scale (62491530222 : Int) atom0005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4199313888000 : Int) atom0006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272866809600 : Int) atom0007Coded) (CoefficientMerge.scale (779887920000 : Int) atom0008Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1333326456000 : Int) atom0009Coded) (CoefficientMerge.scale (3323772244800 : Int) atom0010Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8406856197600 : Int) atom0011Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12010271112000 : Int) atom0012Coded) (CoefficientMerge.scale (10009006509600 : Int) atom0013Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15528360456000 : Int) atom0014Coded) (CoefficientMerge.scale (12749596977600 : Int) atom0015Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16200880673600 : Int) atom0016Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12798766159200 : Int) atom0017Coded) (CoefficientMerge.scale (16293805012800 : Int) atom0018Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12195889977600 : Int) atom0019Coded) (CoefficientMerge.scale (13827946297920 : Int) atom0020Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159699974688 : Int) atom0021Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6953120185920 : Int) atom0022Coded) (CoefficientMerge.scale (2025030241728 : Int) atom0023Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38098109760 : Int) atom0024Coded) (CoefficientMerge.scale (1080956872800 : Int) atom0025Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2184140851200 : Int) atom0026Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4146158016000 : Int) atom0027Coded) (CoefficientMerge.scale (2572271708160 : Int) atom0028Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5310862233600 : Int) atom0029Coded) (CoefficientMerge.scale (1739053414560 : Int) atom0030Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7037837452800 : Int) atom0031Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4195405665792 : Int) atom0032Coded) (CoefficientMerge.scale (1378144449792 : Int) atom0033Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8139571368192 : Int) atom0034Coded) (CoefficientMerge.scale (8281664607744 : Int) atom0035Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7505953373952 : Int) atom0036Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4857012757872 : Int) atom0037Coded) (CoefficientMerge.scale (5186234916720 : Int) atom0038Coded))))))) := by decide +kernel
theorem block000_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block000 := by
  rw [block000_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0000Coded_nonneg g hg hA hB) (atom0001Coded_nonneg g hg hA hB)) (add_nonneg (atom0002Coded_nonneg g hg hA hB) (atom0003Coded_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom0004Coded_nonneg g hg hA hB) (atom0005Coded_nonneg g hg hA hB)) (add_nonneg (atom0006Coded_nonneg g hg hA hB) (add_nonneg (atom0007Coded_nonneg g hg hA hB) (atom0008Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0009Coded_nonneg g hg hA hB) (atom0010Coded_nonneg g hg hA hB)) (add_nonneg (atom0011Coded_nonneg g hg hA hB) (add_nonneg (atom0012Coded_nonneg g hg hA hB) (atom0013Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0014Coded_nonneg g hg hA hB) (atom0015Coded_nonneg g hg hA hB)) (add_nonneg (atom0016Coded_nonneg g hg hA hB) (add_nonneg (atom0017Coded_nonneg g hg hA hB) (atom0018Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0019Coded_nonneg g hg hA hB) (atom0020Coded_nonneg g hg hA hB)) (add_nonneg (atom0021Coded_nonneg g hg hA hB) (add_nonneg (atom0022Coded_nonneg g hg hA hB) (atom0023Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0024Coded_nonneg g hg hA hB) (atom0025Coded_nonneg g hg hA hB)) (add_nonneg (atom0026Coded_nonneg g hg hA hB) (add_nonneg (atom0027Coded_nonneg g hg hA hB) (atom0028Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0029Coded_nonneg g hg hA hB) (atom0030Coded_nonneg g hg hA hB)) (add_nonneg (atom0031Coded_nonneg g hg hA hB) (add_nonneg (atom0032Coded_nonneg g hg hA hB) (atom0033Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0034Coded_nonneg g hg hA hB) (atom0035Coded_nonneg g hg hA hB)) (add_nonneg (atom0036Coded_nonneg g hg hA hB) (add_nonneg (atom0037Coded_nonneg g hg hA hB) (atom0038Coded_nonneg g hg hA hB)))))))

end APPT.Finite24
