import APPT.Finite24Sparse.Base08
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0209 : SparsePolynomial.Poly := [([0,10,12], -8), ([1,10,12], -12), ([2,10,12], -16), ([3,10,12], -16), ([4,10,12], -16), ([5,10,12], -16), ([6,10,12], -16), ([7,10,12], -16), ([8,10,12], -16), ([9,10,12], -16), ([10,10,12], -16), ([10,11,12], -16), ([10,12,12], -16), ([10,12,13], -16), ([10,12,14], -16), ([10,12,15], -16), ([10,12,16], -16), ([10,12,17], -16), ([10,12,18], -14), ([10,12,19], -10), ([10,12,20], -2), ([10,12,21], 2), ([10,12,22], 10), ([10,12,23], 18)]
theorem atom0209_data : atom0209 = SparsePolynomial.monoTimes [10,12] 1 base08 := by decide +kernel
theorem eval_atom0209 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0209 = (quadB (outer g) ![2,2,1] * g 10 * g 12) := by
  rw [atom0209_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0209_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (559159273728 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0209Coded : CoefficientMerge.Poly := [(252, -8), (828, -12), (1404, -16), (1980, -16), (2556, -16), (3132, -16), (3708, -16), (4284, -16), (4860, -16), (5436, -16), (6012, -16), (6036, -16), (6060, -16), (6061, -16), (6062, -16), (6063, -16), (6064, -16), (6065, -16), (6066, -14), (6067, -10), (6068, -2), (6069, 2), (6070, 10), (6071, 18)]
theorem atom0209Coded_decode : atom0209 = SparsePolynomial.decodeCubic 24 atom0209Coded := by decide +kernel
theorem atom0209Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (559159273728 : Int) atom0209Coded) := by
  have h := atom0209_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0209Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0210 : SparsePolynomial.Poly := [([0,11,11], -8), ([1,11,11], -12), ([2,11,11], -16), ([3,11,11], -16), ([4,11,11], -16), ([5,11,11], -16), ([6,11,11], -16), ([7,11,11], -16), ([8,11,11], -16), ([9,11,11], -16), ([10,11,11], -16), ([11,11,11], -16), ([11,11,12], -16), ([11,11,13], -16), ([11,11,14], -16), ([11,11,15], -16), ([11,11,16], -16), ([11,11,17], -16), ([11,11,18], -14), ([11,11,19], -10), ([11,11,20], -2), ([11,11,21], 2), ([11,11,22], 10), ([11,11,23], 18)]
theorem atom0210_data : atom0210 = SparsePolynomial.monoTimes [11,11] 1 base08 := by decide +kernel
theorem eval_atom0210 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0210 = (quadB (outer g) ![2,2,1] * g 11 * g 11) := by
  rw [atom0210_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0210_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2572011413136 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210Coded : CoefficientMerge.Poly := [(275, -8), (851, -12), (1427, -16), (2003, -16), (2579, -16), (3155, -16), (3731, -16), (4307, -16), (4883, -16), (5459, -16), (6035, -16), (6611, -16), (6612, -16), (6613, -16), (6614, -16), (6615, -16), (6616, -16), (6617, -16), (6618, -14), (6619, -10), (6620, -2), (6621, 2), (6622, 10), (6623, 18)]
theorem atom0210Coded_decode : atom0210 = SparsePolynomial.decodeCubic 24 atom0210Coded := by decide +kernel
theorem atom0210Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2572011413136 : Int) atom0210Coded) := by
  have h := atom0210_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0210Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0211 : SparsePolynomial.Poly := [([0,11,12], -8), ([1,11,12], -12), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -16), ([11,12,13], -16), ([11,12,14], -16), ([11,12,15], -16), ([11,12,16], -16), ([11,12,17], -16), ([11,12,18], -14), ([11,12,19], -10), ([11,12,20], -2), ([11,12,21], 2), ([11,12,22], 10), ([11,12,23], 18)]
theorem atom0211_data : atom0211 = SparsePolynomial.monoTimes [11,12] 1 base08 := by decide +kernel
theorem eval_atom0211 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0211 = (quadB (outer g) ![2,2,1] * g 11 * g 12) := by
  rw [atom0211_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0211_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7092350065152 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211Coded : CoefficientMerge.Poly := [(276, -8), (852, -12), (1428, -16), (2004, -16), (2580, -16), (3156, -16), (3732, -16), (4308, -16), (4884, -16), (5460, -16), (6036, -16), (6612, -16), (6636, -16), (6637, -16), (6638, -16), (6639, -16), (6640, -16), (6641, -16), (6642, -14), (6643, -10), (6644, -2), (6645, 2), (6646, 10), (6647, 18)]
theorem atom0211Coded_decode : atom0211 = SparsePolynomial.decodeCubic 24 atom0211Coded := by decide +kernel
theorem atom0211Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7092350065152 : Int) atom0211Coded) := by
  have h := atom0211_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0211Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0212 : SparsePolynomial.Poly := [([0,11,13], -8), ([1,11,13], -12), ([2,11,13], -16), ([3,11,13], -16), ([4,11,13], -16), ([5,11,13], -16), ([6,11,13], -16), ([7,11,13], -16), ([8,11,13], -16), ([9,11,13], -16), ([10,11,13], -16), ([11,11,13], -16), ([11,12,13], -16), ([11,13,13], -16), ([11,13,14], -16), ([11,13,15], -16), ([11,13,16], -16), ([11,13,17], -16), ([11,13,18], -14), ([11,13,19], -10), ([11,13,20], -2), ([11,13,21], 2), ([11,13,22], 10), ([11,13,23], 18)]
theorem atom0212_data : atom0212 = SparsePolynomial.monoTimes [11,13] 1 base08 := by decide +kernel
theorem eval_atom0212 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0212 = (quadB (outer g) ![2,2,1] * g 11 * g 13) := by
  rw [atom0212_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0212_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1676193146496 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212Coded : CoefficientMerge.Poly := [(277, -8), (853, -12), (1429, -16), (2005, -16), (2581, -16), (3157, -16), (3733, -16), (4309, -16), (4885, -16), (5461, -16), (6037, -16), (6613, -16), (6637, -16), (6661, -16), (6662, -16), (6663, -16), (6664, -16), (6665, -16), (6666, -14), (6667, -10), (6668, -2), (6669, 2), (6670, 10), (6671, 18)]
theorem atom0212Coded_decode : atom0212 = SparsePolynomial.decodeCubic 24 atom0212Coded := by decide +kernel
theorem atom0212Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1676193146496 : Int) atom0212Coded) := by
  have h := atom0212_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0212Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0213 : SparsePolynomial.Poly := [([0,12,12], -8), ([1,12,12], -12), ([2,12,12], -16), ([3,12,12], -16), ([4,12,12], -16), ([5,12,12], -16), ([6,12,12], -16), ([7,12,12], -16), ([8,12,12], -16), ([9,12,12], -16), ([10,12,12], -16), ([11,12,12], -16), ([12,12,12], -16), ([12,12,13], -16), ([12,12,14], -16), ([12,12,15], -16), ([12,12,16], -16), ([12,12,17], -16), ([12,12,18], -14), ([12,12,19], -10), ([12,12,20], -2), ([12,12,21], 2), ([12,12,22], 10), ([12,12,23], 18)]
theorem atom0213_data : atom0213 = SparsePolynomial.monoTimes [12,12] 1 base08 := by decide +kernel
theorem eval_atom0213 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0213 = (quadB (outer g) ![2,2,1] * g 12 * g 12) := by
  rw [atom0213_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0213_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6218852276736 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213Coded : CoefficientMerge.Poly := [(300, -8), (876, -12), (1452, -16), (2028, -16), (2604, -16), (3180, -16), (3756, -16), (4332, -16), (4908, -16), (5484, -16), (6060, -16), (6636, -16), (7212, -16), (7213, -16), (7214, -16), (7215, -16), (7216, -16), (7217, -16), (7218, -14), (7219, -10), (7220, -2), (7221, 2), (7222, 10), (7223, 18)]
theorem atom0213Coded_decode : atom0213 = SparsePolynomial.decodeCubic 24 atom0213Coded := by decide +kernel
theorem atom0213Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6218852276736 : Int) atom0213Coded) := by
  have h := atom0213_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0213Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0214 : SparsePolynomial.Poly := [([0,12,13], -8), ([1,12,13], -12), ([2,12,13], -16), ([3,12,13], -16), ([4,12,13], -16), ([5,12,13], -16), ([6,12,13], -16), ([7,12,13], -16), ([8,12,13], -16), ([9,12,13], -16), ([10,12,13], -16), ([11,12,13], -16), ([12,12,13], -16), ([12,13,13], -16), ([12,13,14], -16), ([12,13,15], -16), ([12,13,16], -16), ([12,13,17], -16), ([12,13,18], -14), ([12,13,19], -10), ([12,13,20], -2), ([12,13,21], 2), ([12,13,22], 10), ([12,13,23], 18)]
theorem atom0214_data : atom0214 = SparsePolynomial.monoTimes [12,13] 1 base08 := by decide +kernel
theorem eval_atom0214 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0214 = (quadB (outer g) ![2,2,1] * g 12 * g 13) := by
  rw [atom0214_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0214_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6417696928896 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214Coded : CoefficientMerge.Poly := [(301, -8), (877, -12), (1453, -16), (2029, -16), (2605, -16), (3181, -16), (3757, -16), (4333, -16), (4909, -16), (5485, -16), (6061, -16), (6637, -16), (7213, -16), (7237, -16), (7238, -16), (7239, -16), (7240, -16), (7241, -16), (7242, -14), (7243, -10), (7244, -2), (7245, 2), (7246, 10), (7247, 18)]
theorem atom0214Coded_decode : atom0214 = SparsePolynomial.decodeCubic 24 atom0214Coded := by decide +kernel
theorem atom0214Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6417696928896 : Int) atom0214Coded) := by
  have h := atom0214_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0214Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0215 : SparsePolynomial.Poly := [([0,12,14], -8), ([1,12,14], -12), ([2,12,14], -16), ([3,12,14], -16), ([4,12,14], -16), ([5,12,14], -16), ([6,12,14], -16), ([7,12,14], -16), ([8,12,14], -16), ([9,12,14], -16), ([10,12,14], -16), ([11,12,14], -16), ([12,12,14], -16), ([12,13,14], -16), ([12,14,14], -16), ([12,14,15], -16), ([12,14,16], -16), ([12,14,17], -16), ([12,14,18], -14), ([12,14,19], -10), ([12,14,20], -2), ([12,14,21], 2), ([12,14,22], 10), ([12,14,23], 18)]
theorem atom0215_data : atom0215 = SparsePolynomial.monoTimes [12,14] 1 base08 := by decide +kernel
theorem eval_atom0215 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0215 = (quadB (outer g) ![2,2,1] * g 12 * g 14) := by
  rw [atom0215_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0215_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (562580233776 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215Coded : CoefficientMerge.Poly := [(302, -8), (878, -12), (1454, -16), (2030, -16), (2606, -16), (3182, -16), (3758, -16), (4334, -16), (4910, -16), (5486, -16), (6062, -16), (6638, -16), (7214, -16), (7238, -16), (7262, -16), (7263, -16), (7264, -16), (7265, -16), (7266, -14), (7267, -10), (7268, -2), (7269, 2), (7270, 10), (7271, 18)]
theorem atom0215Coded_decode : atom0215 = SparsePolynomial.decodeCubic 24 atom0215Coded := by decide +kernel
theorem atom0215Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (562580233776 : Int) atom0215Coded) := by
  have h := atom0215_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0215Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0216 : SparsePolynomial.Poly := [([0,13,13], -8), ([1,13,13], -12), ([2,13,13], -16), ([3,13,13], -16), ([4,13,13], -16), ([5,13,13], -16), ([6,13,13], -16), ([7,13,13], -16), ([8,13,13], -16), ([9,13,13], -16), ([10,13,13], -16), ([11,13,13], -16), ([12,13,13], -16), ([13,13,13], -16), ([13,13,14], -16), ([13,13,15], -16), ([13,13,16], -16), ([13,13,17], -16), ([13,13,18], -14), ([13,13,19], -10), ([13,13,20], -2), ([13,13,21], 2), ([13,13,22], 10), ([13,13,23], 18)]
theorem atom0216_data : atom0216 = SparsePolynomial.monoTimes [13,13] 1 base08 := by decide +kernel
theorem eval_atom0216 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0216 = (quadB (outer g) ![2,2,1] * g 13 * g 13) := by
  rw [atom0216_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0216_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7083593193600 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216Coded : CoefficientMerge.Poly := [(325, -8), (901, -12), (1477, -16), (2053, -16), (2629, -16), (3205, -16), (3781, -16), (4357, -16), (4933, -16), (5509, -16), (6085, -16), (6661, -16), (7237, -16), (7813, -16), (7814, -16), (7815, -16), (7816, -16), (7817, -16), (7818, -14), (7819, -10), (7820, -2), (7821, 2), (7822, 10), (7823, 18)]
theorem atom0216Coded_decode : atom0216 = SparsePolynomial.decodeCubic 24 atom0216Coded := by decide +kernel
theorem atom0216Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7083593193600 : Int) atom0216Coded) := by
  have h := atom0216_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0216Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0217 : SparsePolynomial.Poly := [([0,13,14], -8), ([1,13,14], -12), ([2,13,14], -16), ([3,13,14], -16), ([4,13,14], -16), ([5,13,14], -16), ([6,13,14], -16), ([7,13,14], -16), ([8,13,14], -16), ([9,13,14], -16), ([10,13,14], -16), ([11,13,14], -16), ([12,13,14], -16), ([13,13,14], -16), ([13,14,14], -16), ([13,14,15], -16), ([13,14,16], -16), ([13,14,17], -16), ([13,14,18], -14), ([13,14,19], -10), ([13,14,20], -2), ([13,14,21], 2), ([13,14,22], 10), ([13,14,23], 18)]
theorem atom0217_data : atom0217 = SparsePolynomial.monoTimes [13,14] 1 base08 := by decide +kernel
theorem eval_atom0217 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0217 = (quadB (outer g) ![2,2,1] * g 13 * g 14) := by
  rw [atom0217_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0217_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7708218986160 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217Coded : CoefficientMerge.Poly := [(326, -8), (902, -12), (1478, -16), (2054, -16), (2630, -16), (3206, -16), (3782, -16), (4358, -16), (4934, -16), (5510, -16), (6086, -16), (6662, -16), (7238, -16), (7814, -16), (7838, -16), (7839, -16), (7840, -16), (7841, -16), (7842, -14), (7843, -10), (7844, -2), (7845, 2), (7846, 10), (7847, 18)]
theorem atom0217Coded_decode : atom0217 = SparsePolynomial.decodeCubic 24 atom0217Coded := by decide +kernel
theorem atom0217Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7708218986160 : Int) atom0217Coded) := by
  have h := atom0217_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0217Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0218 : SparsePolynomial.Poly := [([0,13,15], -8), ([1,13,15], -12), ([2,13,15], -16), ([3,13,15], -16), ([4,13,15], -16), ([5,13,15], -16), ([6,13,15], -16), ([7,13,15], -16), ([8,13,15], -16), ([9,13,15], -16), ([10,13,15], -16), ([11,13,15], -16), ([12,13,15], -16), ([13,13,15], -16), ([13,14,15], -16), ([13,15,15], -16), ([13,15,16], -16), ([13,15,17], -16), ([13,15,18], -14), ([13,15,19], -10), ([13,15,20], -2), ([13,15,21], 2), ([13,15,22], 10), ([13,15,23], 18)]
theorem atom0218_data : atom0218 = SparsePolynomial.monoTimes [13,15] 1 base08 := by decide +kernel
theorem eval_atom0218 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0218 = (quadB (outer g) ![2,2,1] * g 13 * g 15) := by
  rw [atom0218_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0218_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (678085107840 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218Coded : CoefficientMerge.Poly := [(327, -8), (903, -12), (1479, -16), (2055, -16), (2631, -16), (3207, -16), (3783, -16), (4359, -16), (4935, -16), (5511, -16), (6087, -16), (6663, -16), (7239, -16), (7815, -16), (7839, -16), (7863, -16), (7864, -16), (7865, -16), (7866, -14), (7867, -10), (7868, -2), (7869, 2), (7870, 10), (7871, 18)]
theorem atom0218Coded_decode : atom0218 = SparsePolynomial.decodeCubic 24 atom0218Coded := by decide +kernel
theorem atom0218Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (678085107840 : Int) atom0218Coded) := by
  have h := atom0218_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0218Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0219 : SparsePolynomial.Poly := [([0,14,14], -8), ([1,14,14], -12), ([2,14,14], -16), ([3,14,14], -16), ([4,14,14], -16), ([5,14,14], -16), ([6,14,14], -16), ([7,14,14], -16), ([8,14,14], -16), ([9,14,14], -16), ([10,14,14], -16), ([11,14,14], -16), ([12,14,14], -16), ([13,14,14], -16), ([14,14,14], -16), ([14,14,15], -16), ([14,14,16], -16), ([14,14,17], -16), ([14,14,18], -14), ([14,14,19], -10), ([14,14,20], -2), ([14,14,21], 2), ([14,14,22], 10), ([14,14,23], 18)]
theorem atom0219_data : atom0219 = SparsePolynomial.monoTimes [14,14] 1 base08 := by decide +kernel
theorem eval_atom0219 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0219 = (quadB (outer g) ![2,2,1] * g 14 * g 14) := by
  rw [atom0219_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0219_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7509374334000 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219Coded : CoefficientMerge.Poly := [(350, -8), (926, -12), (1502, -16), (2078, -16), (2654, -16), (3230, -16), (3806, -16), (4382, -16), (4958, -16), (5534, -16), (6110, -16), (6686, -16), (7262, -16), (7838, -16), (8414, -16), (8415, -16), (8416, -16), (8417, -16), (8418, -14), (8419, -10), (8420, -2), (8421, 2), (8422, 10), (8423, 18)]
theorem atom0219Coded_decode : atom0219 = SparsePolynomial.decodeCubic 24 atom0219Coded := by decide +kernel
theorem atom0219Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7509374334000 : Int) atom0219Coded) := by
  have h := atom0219_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0219Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0220 : SparsePolynomial.Poly := [([0,14,15], -8), ([1,14,15], -12), ([2,14,15], -16), ([3,14,15], -16), ([4,14,15], -16), ([5,14,15], -16), ([6,14,15], -16), ([7,14,15], -16), ([8,14,15], -16), ([9,14,15], -16), ([10,14,15], -16), ([11,14,15], -16), ([12,14,15], -16), ([13,14,15], -16), ([14,14,15], -16), ([14,15,15], -16), ([14,15,16], -16), ([14,15,17], -16), ([14,15,18], -14), ([14,15,19], -10), ([14,15,20], -2), ([14,15,21], 2), ([14,15,22], 10), ([14,15,23], 18)]
theorem atom0220_data : atom0220 = SparsePolynomial.monoTimes [14,15] 1 base08 := by decide +kernel
theorem eval_atom0220 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0220 = (quadB (outer g) ![2,2,1] * g 14 * g 15) := by
  rw [atom0220_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0220_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7384764083760 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220Coded : CoefficientMerge.Poly := [(351, -8), (927, -12), (1503, -16), (2079, -16), (2655, -16), (3231, -16), (3807, -16), (4383, -16), (4959, -16), (5535, -16), (6111, -16), (6687, -16), (7263, -16), (7839, -16), (8415, -16), (8439, -16), (8440, -16), (8441, -16), (8442, -14), (8443, -10), (8444, -2), (8445, 2), (8446, 10), (8447, 18)]
theorem atom0220Coded_decode : atom0220 = SparsePolynomial.decodeCubic 24 atom0220Coded := by decide +kernel
theorem atom0220Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7384764083760 : Int) atom0220Coded) := by
  have h := atom0220_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0220Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0221 : SparsePolynomial.Poly := [([0,14,16], -8), ([1,14,16], -12), ([2,14,16], -16), ([3,14,16], -16), ([4,14,16], -16), ([5,14,16], -16), ([6,14,16], -16), ([7,14,16], -16), ([8,14,16], -16), ([9,14,16], -16), ([10,14,16], -16), ([11,14,16], -16), ([12,14,16], -16), ([13,14,16], -16), ([14,14,16], -16), ([14,15,16], -16), ([14,16,16], -16), ([14,16,17], -16), ([14,16,18], -14), ([14,16,19], -10), ([14,16,20], -2), ([14,16,21], 2), ([14,16,22], 10), ([14,16,23], 18)]
theorem atom0221_data : atom0221 = SparsePolynomial.monoTimes [14,16] 1 base08 := by decide +kernel
theorem eval_atom0221 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0221 = (quadB (outer g) ![2,2,1] * g 14 * g 16) := by
  rw [atom0221_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0221_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (201182894640 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221Coded : CoefficientMerge.Poly := [(352, -8), (928, -12), (1504, -16), (2080, -16), (2656, -16), (3232, -16), (3808, -16), (4384, -16), (4960, -16), (5536, -16), (6112, -16), (6688, -16), (7264, -16), (7840, -16), (8416, -16), (8440, -16), (8464, -16), (8465, -16), (8466, -14), (8467, -10), (8468, -2), (8469, 2), (8470, 10), (8471, 18)]
theorem atom0221Coded_decode : atom0221 = SparsePolynomial.decodeCubic 24 atom0221Coded := by decide +kernel
theorem atom0221Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (201182894640 : Int) atom0221Coded) := by
  have h := atom0221_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0221Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0222 : SparsePolynomial.Poly := [([0,15,15], -8), ([1,15,15], -12), ([2,15,15], -16), ([3,15,15], -16), ([4,15,15], -16), ([5,15,15], -16), ([6,15,15], -16), ([7,15,15], -16), ([8,15,15], -16), ([9,15,15], -16), ([10,15,15], -16), ([11,15,15], -16), ([12,15,15], -16), ([13,15,15], -16), ([14,15,15], -16), ([15,15,15], -16), ([15,15,16], -16), ([15,15,17], -16), ([15,15,18], -14), ([15,15,19], -10), ([15,15,20], -2), ([15,15,21], 2), ([15,15,22], 10), ([15,15,23], 18)]
theorem atom0222_data : atom0222 = SparsePolynomial.monoTimes [15,15] 1 base08 := by decide +kernel
theorem eval_atom0222 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0222 = (quadB (outer g) ![2,2,1] * g 15 * g 15) := by
  rw [atom0222_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0222_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6760138291200 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 15 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222Coded : CoefficientMerge.Poly := [(375, -8), (951, -12), (1527, -16), (2103, -16), (2679, -16), (3255, -16), (3831, -16), (4407, -16), (4983, -16), (5559, -16), (6135, -16), (6711, -16), (7287, -16), (7863, -16), (8439, -16), (9015, -16), (9016, -16), (9017, -16), (9018, -14), (9019, -10), (9020, -2), (9021, 2), (9022, 10), (9023, 18)]
theorem atom0222Coded_decode : atom0222 = SparsePolynomial.decodeCubic 24 atom0222Coded := by decide +kernel
theorem atom0222Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6760138291200 : Int) atom0222Coded) := by
  have h := atom0222_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0222Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0223 : SparsePolynomial.Poly := [([0,15,16], -8), ([1,15,16], -12), ([2,15,16], -16), ([3,15,16], -16), ([4,15,16], -16), ([5,15,16], -16), ([6,15,16], -16), ([7,15,16], -16), ([8,15,16], -16), ([9,15,16], -16), ([10,15,16], -16), ([11,15,16], -16), ([12,15,16], -16), ([13,15,16], -16), ([14,15,16], -16), ([15,15,16], -16), ([15,16,16], -16), ([15,16,17], -16), ([15,16,18], -14), ([15,16,19], -10), ([15,16,20], -2), ([15,16,21], 2), ([15,16,22], 10), ([15,16,23], 18)]
theorem atom0223_data : atom0223 = SparsePolynomial.monoTimes [15,16] 1 base08 := by decide +kernel
theorem eval_atom0223 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0223 = (quadB (outer g) ![2,2,1] * g 15 * g 16) := by
  rw [atom0223_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0223_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5732844687360 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 15 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223Coded : CoefficientMerge.Poly := [(376, -8), (952, -12), (1528, -16), (2104, -16), (2680, -16), (3256, -16), (3832, -16), (4408, -16), (4984, -16), (5560, -16), (6136, -16), (6712, -16), (7288, -16), (7864, -16), (8440, -16), (9016, -16), (9040, -16), (9041, -16), (9042, -14), (9043, -10), (9044, -2), (9045, 2), (9046, 10), (9047, 18)]
theorem atom0223Coded_decode : atom0223 = SparsePolynomial.decodeCubic 24 atom0223Coded := by decide +kernel
theorem atom0223Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5732844687360 : Int) atom0223Coded) := by
  have h := atom0223_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0223Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0224 : SparsePolynomial.Poly := [([0,16,16], -8), ([1,16,16], -12), ([2,16,16], -16), ([3,16,16], -16), ([4,16,16], -16), ([5,16,16], -16), ([6,16,16], -16), ([7,16,16], -16), ([8,16,16], -16), ([9,16,16], -16), ([10,16,16], -16), ([11,16,16], -16), ([12,16,16], -16), ([13,16,16], -16), ([14,16,16], -16), ([15,16,16], -16), ([16,16,16], -16), ([16,16,17], -16), ([16,16,18], -14), ([16,16,19], -10), ([16,16,20], -2), ([16,16,21], 2), ([16,16,22], 10), ([16,16,23], 18)]
theorem atom0224_data : atom0224 = SparsePolynomial.monoTimes [16,16] 1 base08 := by decide +kernel
theorem eval_atom0224 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0224 = (quadB (outer g) ![2,2,1] * g 16 * g 16) := by
  rw [atom0224_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0224_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5857454937600 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 16 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224Coded : CoefficientMerge.Poly := [(400, -8), (976, -12), (1552, -16), (2128, -16), (2704, -16), (3280, -16), (3856, -16), (4432, -16), (5008, -16), (5584, -16), (6160, -16), (6736, -16), (7312, -16), (7888, -16), (8464, -16), (9040, -16), (9616, -16), (9617, -16), (9618, -14), (9619, -10), (9620, -2), (9621, 2), (9622, 10), (9623, 18)]
theorem atom0224Coded_decode : atom0224 = SparsePolynomial.decodeCubic 24 atom0224Coded := by decide +kernel
theorem atom0224Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5857454937600 : Int) atom0224Coded) := by
  have h := atom0224_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0224Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0225 : SparsePolynomial.Poly := [([0,16,17], -8), ([1,16,17], -12), ([2,16,17], -16), ([3,16,17], -16), ([4,16,17], -16), ([5,16,17], -16), ([6,16,17], -16), ([7,16,17], -16), ([8,16,17], -16), ([9,16,17], -16), ([10,16,17], -16), ([11,16,17], -16), ([12,16,17], -16), ([13,16,17], -16), ([14,16,17], -16), ([15,16,17], -16), ([16,16,17], -16), ([16,17,17], -16), ([16,17,18], -14), ([16,17,19], -10), ([16,17,20], -2), ([16,17,21], 2), ([16,17,22], 10), ([16,17,23], 18)]
theorem atom0225_data : atom0225 = SparsePolynomial.monoTimes [16,17] 1 base08 := by decide +kernel
theorem eval_atom0225 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0225 = (quadB (outer g) ![2,2,1] * g 16 * g 17) := by
  rw [atom0225_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0225_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2325757324800 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 16 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225Coded : CoefficientMerge.Poly := [(401, -8), (977, -12), (1553, -16), (2129, -16), (2705, -16), (3281, -16), (3857, -16), (4433, -16), (5009, -16), (5585, -16), (6161, -16), (6737, -16), (7313, -16), (7889, -16), (8465, -16), (9041, -16), (9617, -16), (9641, -16), (9642, -14), (9643, -10), (9644, -2), (9645, 2), (9646, 10), (9647, 18)]
theorem atom0225Coded_decode : atom0225 = SparsePolynomial.decodeCubic 24 atom0225Coded := by decide +kernel
theorem atom0225Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2325757324800 : Int) atom0225Coded) := by
  have h := atom0225_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0225Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0226 : SparsePolynomial.Poly := [([0,17,17], -8), ([1,17,17], -12), ([2,17,17], -16), ([3,17,17], -16), ([4,17,17], -16), ([5,17,17], -16), ([6,17,17], -16), ([7,17,17], -16), ([8,17,17], -16), ([9,17,17], -16), ([10,17,17], -16), ([11,17,17], -16), ([12,17,17], -16), ([13,17,17], -16), ([14,17,17], -16), ([15,17,17], -16), ([16,17,17], -16), ([17,17,17], -16), ([17,17,18], -14), ([17,17,19], -10), ([17,17,20], -2), ([17,17,21], 2), ([17,17,22], 10), ([17,17,23], 18)]
theorem atom0226_data : atom0226 = SparsePolynomial.monoTimes [17,17] 1 base08 := by decide +kernel
theorem eval_atom0226 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0226 = (quadB (outer g) ![2,2,1] * g 17 * g 17) := by
  rw [atom0226_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0226_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3848485132800 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 17 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226Coded : CoefficientMerge.Poly := [(425, -8), (1001, -12), (1577, -16), (2153, -16), (2729, -16), (3305, -16), (3881, -16), (4457, -16), (5033, -16), (5609, -16), (6185, -16), (6761, -16), (7337, -16), (7913, -16), (8489, -16), (9065, -16), (9641, -16), (10217, -16), (10218, -14), (10219, -10), (10220, -2), (10221, 2), (10222, 10), (10223, 18)]
theorem atom0226Coded_decode : atom0226 = SparsePolynomial.decodeCubic 24 atom0226Coded := by decide +kernel
theorem atom0226Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3848485132800 : Int) atom0226Coded) := by
  have h := atom0226_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0226Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0227 : SparsePolynomial.Poly := [([0,19,19], -8), ([1,19,19], -12), ([2,19,19], -16), ([3,19,19], -16), ([4,19,19], -16), ([5,19,19], -16), ([6,19,19], -16), ([7,19,19], -16), ([8,19,19], -16), ([9,19,19], -16), ([10,19,19], -16), ([11,19,19], -16), ([12,19,19], -16), ([13,19,19], -16), ([14,19,19], -16), ([15,19,19], -16), ([16,19,19], -16), ([17,19,19], -16), ([18,19,19], -14), ([19,19,19], -10), ([19,19,20], -2), ([19,19,21], 2), ([19,19,22], 10), ([19,19,23], 18)]
theorem atom0227_data : atom0227 = SparsePolynomial.monoTimes [19,19] 1 base08 := by decide +kernel
theorem eval_atom0227 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0227 = (quadB (outer g) ![2,2,1] * g 19 * g 19) := by
  rw [atom0227_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0227_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (612355645440 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 19 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227Coded : CoefficientMerge.Poly := [(475, -8), (1051, -12), (1627, -16), (2203, -16), (2779, -16), (3355, -16), (3931, -16), (4507, -16), (5083, -16), (5659, -16), (6235, -16), (6811, -16), (7387, -16), (7963, -16), (8539, -16), (9115, -16), (9691, -16), (10267, -16), (10843, -14), (11419, -10), (11420, -2), (11421, 2), (11422, 10), (11423, 18)]
theorem atom0227Coded_decode : atom0227 = SparsePolynomial.decodeCubic 24 atom0227Coded := by decide +kernel
theorem atom0227Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (612355645440 : Int) atom0227Coded) := by
  have h := atom0227_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0227Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0228 : SparsePolynomial.Poly := [([0,0,11], 1)]
theorem eval_atom0228 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0228 = ((g 0) * (g 0) * (g 11)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0228_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2323663382304 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 0) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228Coded : CoefficientMerge.Poly := [(11, 1)]
theorem atom0228Coded_decode : atom0228 = SparsePolynomial.decodeCubic 24 atom0228Coded := by decide +kernel
theorem atom0228Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2323663382304 : Int) atom0228Coded) := by
  have h := atom0228_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0228Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0229 : SparsePolynomial.Poly := [([0,0,12], 1)]
theorem eval_atom0229 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0229 = ((g 0) * (g 0) * (g 12)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0229_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27162605029824 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 0) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229Coded : CoefficientMerge.Poly := [(12, 1)]
theorem atom0229Coded_decode : atom0229 = SparsePolynomial.decodeCubic 24 atom0229Coded := by decide +kernel
theorem atom0229Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27162605029824 : Int) atom0229Coded) := by
  have h := atom0229_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0229Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0230 : SparsePolynomial.Poly := [([0,0,13], 1)]
theorem eval_atom0230 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0230 = ((g 0) * (g 0) * (g 13)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0230_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15418433923200 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 0) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230Coded : CoefficientMerge.Poly := [(13, 1)]
theorem atom0230Coded_decode : atom0230 = SparsePolynomial.decodeCubic 24 atom0230Coded := by decide +kernel
theorem atom0230Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15418433923200 : Int) atom0230Coded) := by
  have h := atom0230_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0230Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0231 : SparsePolynomial.Poly := [([0,0,18], 1)]
theorem eval_atom0231 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0231 = ((g 0) * (g 0) * (g 18)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0231_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11502930700800 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 0) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231Coded : CoefficientMerge.Poly := [(18, 1)]
theorem atom0231Coded_decode : atom0231 = SparsePolynomial.decodeCubic 24 atom0231Coded := by decide +kernel
theorem atom0231Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11502930700800 : Int) atom0231Coded) := by
  have h := atom0231_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0231Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0232 : SparsePolynomial.Poly := [([0,0,19], 1)]
theorem eval_atom0232 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0232 = ((g 0) * (g 0) * (g 19)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0232_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8419890124800 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 0) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232Coded : CoefficientMerge.Poly := [(19, 1)]
theorem atom0232Coded_decode : atom0232 = SparsePolynomial.decodeCubic 24 atom0232Coded := by decide +kernel
theorem atom0232Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8419890124800 : Int) atom0232Coded) := by
  have h := atom0232_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0232Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0233 : SparsePolynomial.Poly := [([0,0,20], 1)]
theorem eval_atom0233 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0233 = ((g 0) * (g 0) * (g 20)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0233_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5336849548800 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 0) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233Coded : CoefficientMerge.Poly := [(20, 1)]
theorem atom0233Coded_decode : atom0233 = SparsePolynomial.decodeCubic 24 atom0233Coded := by decide +kernel
theorem atom0233Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5336849548800 : Int) atom0233Coded) := by
  have h := atom0233_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0233Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0234 : SparsePolynomial.Poly := [([0,0,21], 1)]
theorem eval_atom0234 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0234 = ((g 0) * (g 0) * (g 21)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0234_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2253808972800 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 0) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234Coded : CoefficientMerge.Poly := [(21, 1)]
theorem atom0234Coded_decode : atom0234 = SparsePolynomial.decodeCubic 24 atom0234Coded := by decide +kernel
theorem atom0234Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2253808972800 : Int) atom0234Coded) := by
  have h := atom0234_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0234Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0235 : SparsePolynomial.Poly := [([0,1,1], 1)]
theorem eval_atom0235 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0235 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0235_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2338858368000 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235Coded : CoefficientMerge.Poly := [(25, 1)]
theorem atom0235Coded_decode : atom0235 = SparsePolynomial.decodeCubic 24 atom0235Coded := by decide +kernel
theorem atom0235Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2338858368000 : Int) atom0235Coded) := by
  have h := atom0235_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0235Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0236 : SparsePolynomial.Poly := [([0,1,2], 1)]
theorem eval_atom0236 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0236 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0236_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60480751161600 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236Coded : CoefficientMerge.Poly := [(26, 1)]
theorem atom0236Coded_decode : atom0236 = SparsePolynomial.decodeCubic 24 atom0236Coded := by decide +kernel
theorem atom0236Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (60480751161600 : Int) atom0236Coded) := by
  have h := atom0236_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0236Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0237 : SparsePolynomial.Poly := [([0,1,3], 1)]
theorem eval_atom0237 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0237 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0237_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59959823616000 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237Coded : CoefficientMerge.Poly := [(27, 1)]
theorem atom0237Coded_decode : atom0237 = SparsePolynomial.decodeCubic 24 atom0237Coded := by decide +kernel
theorem atom0237Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59959823616000 : Int) atom0237Coded) := by
  have h := atom0237_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0237Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0238 : SparsePolynomial.Poly := [([0,1,4], 1)]
theorem eval_atom0238 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0238 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0238_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59438896070400 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238Coded : CoefficientMerge.Poly := [(28, 1)]
theorem atom0238Coded_decode : atom0238 = SparsePolynomial.decodeCubic 24 atom0238Coded := by decide +kernel
theorem atom0238Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59438896070400 : Int) atom0238Coded) := by
  have h := atom0238_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0238Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0239 : SparsePolynomial.Poly := [([0,1,5], 1)]
theorem eval_atom0239 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0239 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0239_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62359415395200 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239Coded : CoefficientMerge.Poly := [(29, 1)]
theorem atom0239Coded_decode : atom0239 = SparsePolynomial.decodeCubic 24 atom0239Coded := by decide +kernel
theorem atom0239Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62359415395200 : Int) atom0239Coded) := by
  have h := atom0239_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0239Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0240 : SparsePolynomial.Poly := [([0,1,6], 1)]
theorem eval_atom0240 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0240 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0240_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58397040979200 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0240Coded : CoefficientMerge.Poly := [(30, 1)]
theorem atom0240Coded_decode : atom0240 = SparsePolynomial.decodeCubic 24 atom0240Coded := by decide +kernel
theorem atom0240Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (58397040979200 : Int) atom0240Coded) := by
  have h := atom0240_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0240Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0241 : SparsePolynomial.Poly := [([0,1,7], 1)]
theorem eval_atom0241 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0241 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0241_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57876113433600 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241Coded : CoefficientMerge.Poly := [(31, 1)]
theorem atom0241Coded_decode : atom0241 = SparsePolynomial.decodeCubic 24 atom0241Coded := by decide +kernel
theorem atom0241Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57876113433600 : Int) atom0241Coded) := by
  have h := atom0241_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0241Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0242 : SparsePolynomial.Poly := [([0,1,8], 1)]
theorem eval_atom0242 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0242 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0242_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57355185888000 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242Coded : CoefficientMerge.Poly := [(32, 1)]
theorem atom0242Coded_decode : atom0242 = SparsePolynomial.decodeCubic 24 atom0242Coded := by decide +kernel
theorem atom0242Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57355185888000 : Int) atom0242Coded) := by
  have h := atom0242_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0242Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0243 : SparsePolynomial.Poly := [([0,1,9], 1)]
theorem eval_atom0243 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0243 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0243_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59840148865464 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243Coded : CoefficientMerge.Poly := [(33, 1)]
theorem atom0243Coded_decode : atom0243 = SparsePolynomial.decodeCubic 24 atom0243Coded := by decide +kernel
theorem atom0243Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59840148865464 : Int) atom0243Coded) := by
  have h := atom0243_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0243Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0244 : SparsePolynomial.Poly := [([0,1,10], 1)]
theorem eval_atom0244 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0244 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0244_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68140969836984 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244Coded : CoefficientMerge.Poly := [(34, 1)]
theorem atom0244Coded_decode : atom0244 = SparsePolynomial.decodeCubic 24 atom0244Coded := by decide +kernel
theorem atom0244Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (68140969836984 : Int) atom0244Coded) := by
  have h := atom0244_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0244Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0245 : SparsePolynomial.Poly := [([0,1,11], 1)]
theorem eval_atom0245 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0245 = ((g 0) * (g 1) * (g 11)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0245_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79108072262208 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245Coded : CoefficientMerge.Poly := [(35, 1)]
theorem atom0245Coded_decode : atom0245 = SparsePolynomial.decodeCubic 24 atom0245Coded := by decide +kernel
theorem atom0245Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (79108072262208 : Int) atom0245Coded) := by
  have h := atom0245_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0245Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0246 : SparsePolynomial.Poly := [([0,1,12], 1)]
theorem eval_atom0246 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0246 = ((g 0) * (g 1) * (g 12)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0246_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129806548299648 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246Coded : CoefficientMerge.Poly := [(36, 1)]
theorem atom0246Coded_decode : atom0246 = SparsePolynomial.decodeCubic 24 atom0246Coded := by decide +kernel
theorem atom0246Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129806548299648 : Int) atom0246Coded) := by
  have h := atom0246_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0246Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0247 : SparsePolynomial.Poly := [([0,1,13], 1)]
theorem eval_atom0247 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0247 = ((g 0) * (g 1) * (g 13)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0247_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107338798828800 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247Coded : CoefficientMerge.Poly := [(37, 1)]
theorem atom0247Coded_decode : atom0247 = SparsePolynomial.decodeCubic 24 atom0247Coded := by decide +kernel
theorem atom0247Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (107338798828800 : Int) atom0247Coded) := by
  have h := atom0247_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0247Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0248 : SparsePolynomial.Poly := [([0,1,14], 1)]
theorem eval_atom0248 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0248 = ((g 0) * (g 1) * (g 14)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0248_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77522523724800 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248Coded : CoefficientMerge.Poly := [(38, 1)]
theorem atom0248Coded_decode : atom0248 = SparsePolynomial.decodeCubic 24 atom0248Coded := by decide +kernel
theorem atom0248Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (77522523724800 : Int) atom0248Coded) := by
  have h := atom0248_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0248Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0249 : SparsePolynomial.Poly := [([0,1,15], 1)]
theorem eval_atom0249 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0249 = ((g 0) * (g 1) * (g 15)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0249_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78227402803200 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249Coded : CoefficientMerge.Poly := [(39, 1)]
theorem atom0249Coded_decode : atom0249 = SparsePolynomial.decodeCubic 24 atom0249Coded := by decide +kernel
theorem atom0249Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (78227402803200 : Int) atom0249Coded) := by
  have h := atom0249_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0249Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0250 : SparsePolynomial.Poly := [([0,1,16], 1)]
theorem eval_atom0250 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0250 = ((g 0) * (g 1) * (g 16)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0250_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73021026758400 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250Coded : CoefficientMerge.Poly := [(40, 1)]
theorem atom0250Coded_decode : atom0250 = SparsePolynomial.decodeCubic 24 atom0250Coded := by decide +kernel
theorem atom0250Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (73021026758400 : Int) atom0250Coded) := by
  have h := atom0250_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0250Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0251 : SparsePolynomial.Poly := [([0,1,17], 1)]
theorem eval_atom0251 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0251 = ((g 0) * (g 1) * (g 17)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0251_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72781019942400 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251Coded : CoefficientMerge.Poly := [(41, 1)]
theorem atom0251Coded_decode : atom0251 = SparsePolynomial.decodeCubic 24 atom0251Coded := by decide +kernel
theorem atom0251Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (72781019942400 : Int) atom0251Coded) := by
  have h := atom0251_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0251Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0252 : SparsePolynomial.Poly := [([0,1,18], 1)]
theorem eval_atom0252 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0252 = ((g 0) * (g 1) * (g 18)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0252_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102984186412800 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 1) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252Coded : CoefficientMerge.Poly := [(42, 1)]
theorem atom0252Coded_decode : atom0252 = SparsePolynomial.decodeCubic 24 atom0252Coded := by decide +kernel
theorem atom0252Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102984186412800 : Int) atom0252Coded) := by
  have h := atom0252_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0252Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0253 : SparsePolynomial.Poly := [([0,1,19], 1)]
theorem eval_atom0253 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0253 = ((g 0) * (g 1) * (g 19)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0253_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40961914963200 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 1) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253Coded : CoefficientMerge.Poly := [(43, 1)]
theorem atom0253Coded_decode : atom0253 = SparsePolynomial.decodeCubic 24 atom0253Coded := by decide +kernel
theorem atom0253Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40961914963200 : Int) atom0253Coded) := by
  have h := atom0253_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0253Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0254 : SparsePolynomial.Poly := [([0,1,20], 1)]
theorem eval_atom0254 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0254 = ((g 0) * (g 1) * (g 20)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0254_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12512892268800 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 1) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254Coded : CoefficientMerge.Poly := [(44, 1)]
theorem atom0254Coded_decode : atom0254 = SparsePolynomial.decodeCubic 24 atom0254Coded := by decide +kernel
theorem atom0254Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12512892268800 : Int) atom0254Coded) := by
  have h := atom0254_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0254Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0255 : SparsePolynomial.Poly := [([0,1,21], 1)]
theorem eval_atom0255 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0255 = ((g 0) * (g 1) * (g 21)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0255_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5205731731200 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 1) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0255Coded : CoefficientMerge.Poly := [(45, 1)]
theorem atom0255Coded_decode : atom0255 = SparsePolynomial.decodeCubic 24 atom0255Coded := by decide +kernel
theorem atom0255Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5205731731200 : Int) atom0255Coded) := by
  have h := atom0255_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0255Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0256 : SparsePolynomial.Poly := [([0,1,22], 1)]
theorem eval_atom0256 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0256 = ((g 0) * (g 1) * (g 22)) := by
  norm_num [atom0256, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0256_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4086988550400 : Int) atom0256) := by
  rw [SparsePolynomial.eval_scale, eval_atom0256]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 1) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0256Coded : CoefficientMerge.Poly := [(46, 1)]
theorem atom0256Coded_decode : atom0256 = SparsePolynomial.decodeCubic 24 atom0256Coded := by decide +kernel
theorem atom0256Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4086988550400 : Int) atom0256Coded) := by
  have h := atom0256_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0256Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0257 : SparsePolynomial.Poly := [([0,2,2], 1)]
theorem eval_atom0257 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0257 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0257, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0257_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65275410816000 : Int) atom0257) := by
  rw [SparsePolynomial.eval_scale, eval_atom0257]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0257Coded : CoefficientMerge.Poly := [(50, 1)]
theorem atom0257Coded_decode : atom0257 = SparsePolynomial.decodeCubic 24 atom0257Coded := by decide +kernel
theorem atom0257Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65275410816000 : Int) atom0257Coded) := by
  have h := atom0257_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0257Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0258 : SparsePolynomial.Poly := [([0,2,3], 1)]
theorem eval_atom0258 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0258 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0258, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0258_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132592007116800 : Int) atom0258) := by
  rw [SparsePolynomial.eval_scale, eval_atom0258]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0258Coded : CoefficientMerge.Poly := [(51, 1)]
theorem atom0258Coded_decode : atom0258 = SparsePolynomial.decodeCubic 24 atom0258Coded := by decide +kernel
theorem atom0258Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (132592007116800 : Int) atom0258Coded) := by
  have h := atom0258_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0258Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0259 : SparsePolynomial.Poly := [([0,2,4], 1)]
theorem eval_atom0259 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0259 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0259, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0259_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134633192601600 : Int) atom0259) := by
  rw [SparsePolynomial.eval_scale, eval_atom0259]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0259Coded : CoefficientMerge.Poly := [(52, 1)]
theorem atom0259Coded_decode : atom0259 = SparsePolynomial.decodeCubic 24 atom0259Coded := by decide +kernel
theorem atom0259Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134633192601600 : Int) atom0259Coded) := by
  have h := atom0259_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0259Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0260 : SparsePolynomial.Poly := [([0,2,5], 1)]
theorem eval_atom0260 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0260 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0260, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0260_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136674378086400 : Int) atom0260) := by
  rw [SparsePolynomial.eval_scale, eval_atom0260]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0260Coded : CoefficientMerge.Poly := [(53, 1)]
theorem atom0260Coded_decode : atom0260 = SparsePolynomial.decodeCubic 24 atom0260Coded := by decide +kernel
theorem atom0260Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (136674378086400 : Int) atom0260Coded) := by
  have h := atom0260_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0260Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0261 : SparsePolynomial.Poly := [([0,2,6], 1)]
theorem eval_atom0261 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0261 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0261, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0261_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (138715563571200 : Int) atom0261) := by
  rw [SparsePolynomial.eval_scale, eval_atom0261]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0261Coded : CoefficientMerge.Poly := [(54, 1)]
theorem atom0261Coded_decode : atom0261 = SparsePolynomial.decodeCubic 24 atom0261Coded := by decide +kernel
theorem atom0261Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (138715563571200 : Int) atom0261Coded) := by
  have h := atom0261_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0261Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0262 : SparsePolynomial.Poly := [([0,2,7], 1)]
theorem eval_atom0262 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0262 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0262, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0262_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140756749056000 : Int) atom0262) := by
  rw [SparsePolynomial.eval_scale, eval_atom0262]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0262Coded : CoefficientMerge.Poly := [(55, 1)]
theorem atom0262Coded_decode : atom0262 = SparsePolynomial.decodeCubic 24 atom0262Coded := by decide +kernel
theorem atom0262Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (140756749056000 : Int) atom0262Coded) := by
  have h := atom0262_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0262Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0263 : SparsePolynomial.Poly := [([0,2,8], 1)]
theorem eval_atom0263 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0263 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0263, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0263_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142797934540800 : Int) atom0263) := by
  rw [SparsePolynomial.eval_scale, eval_atom0263]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0263Coded : CoefficientMerge.Poly := [(56, 1)]
theorem atom0263Coded_decode : atom0263 = SparsePolynomial.decodeCubic 24 atom0263Coded := by decide +kernel
theorem atom0263Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142797934540800 : Int) atom0263Coded) := by
  have h := atom0263_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0263Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0264 : SparsePolynomial.Poly := [([0,2,9], 1)]
theorem eval_atom0264 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0264 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0264, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0264_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144839120025600 : Int) atom0264) := by
  rw [SparsePolynomial.eval_scale, eval_atom0264]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0264Coded : CoefficientMerge.Poly := [(57, 1)]
theorem atom0264Coded_decode : atom0264 = SparsePolynomial.decodeCubic 24 atom0264Coded := by decide +kernel
theorem atom0264Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144839120025600 : Int) atom0264Coded) := by
  have h := atom0264_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0264Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0265 : SparsePolynomial.Poly := [([0,2,10], 1)]
theorem eval_atom0265 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0265 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0265, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0265_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146880305510400 : Int) atom0265) := by
  rw [SparsePolynomial.eval_scale, eval_atom0265]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0265Coded : CoefficientMerge.Poly := [(58, 1)]
theorem atom0265Coded_decode : atom0265 = SparsePolynomial.decodeCubic 24 atom0265Coded := by decide +kernel
theorem atom0265Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146880305510400 : Int) atom0265Coded) := by
  have h := atom0265_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0265Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0266 : SparsePolynomial.Poly := [([0,2,11], 1)]
theorem eval_atom0266 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0266 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0266, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0266_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153568817759808 : Int) atom0266) := by
  rw [SparsePolynomial.eval_scale, eval_atom0266]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0266Coded : CoefficientMerge.Poly := [(59, 1)]
theorem atom0266Coded_decode : atom0266 = SparsePolynomial.decodeCubic 24 atom0266Coded := by decide +kernel
theorem atom0266Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153568817759808 : Int) atom0266Coded) := by
  have h := atom0266_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0266Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0267 : SparsePolynomial.Poly := [([0,2,12], 1)]
theorem eval_atom0267 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0267 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0267, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0267_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (205287886539648 : Int) atom0267) := by
  rw [SparsePolynomial.eval_scale, eval_atom0267]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0267Coded : CoefficientMerge.Poly := [(60, 1)]
theorem atom0267Coded_decode : atom0267 = SparsePolynomial.decodeCubic 24 atom0267Coded := by decide +kernel
theorem atom0267Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205287886539648 : Int) atom0267Coded) := by
  have h := atom0267_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0267Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0268 : SparsePolynomial.Poly := [([0,2,13], 1)]
theorem eval_atom0268 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0268 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0268, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0268_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183840729811200 : Int) atom0268) := by
  rw [SparsePolynomial.eval_scale, eval_atom0268]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0268Coded : CoefficientMerge.Poly := [(61, 1)]
theorem atom0268Coded_decode : atom0268 = SparsePolynomial.decodeCubic 24 atom0268Coded := by decide +kernel
theorem atom0268Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (183840729811200 : Int) atom0268Coded) := by
  have h := atom0268_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0268Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0269 : SparsePolynomial.Poly := [([0,2,14], 1)]
theorem eval_atom0269 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0269 = ((g 0) * (g 2) * (g 14)) := by
  norm_num [atom0269, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0269_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155045047449600 : Int) atom0269) := by
  rw [SparsePolynomial.eval_scale, eval_atom0269]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0269Coded : CoefficientMerge.Poly := [(62, 1)]
theorem atom0269Coded_decode : atom0269 = SparsePolynomial.decodeCubic 24 atom0269Coded := by decide +kernel
theorem atom0269Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155045047449600 : Int) atom0269Coded) := by
  have h := atom0269_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0269Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0270 : SparsePolynomial.Poly := [([0,2,15], 1)]
theorem eval_atom0270 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0270 = ((g 0) * (g 2) * (g 15)) := by
  norm_num [atom0270, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0270_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157086232934400 : Int) atom0270) := by
  rw [SparsePolynomial.eval_scale, eval_atom0270]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0270Coded : CoefficientMerge.Poly := [(63, 1)]
theorem atom0270Coded_decode : atom0270 = SparsePolynomial.decodeCubic 24 atom0270Coded := by decide +kernel
theorem atom0270Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (157086232934400 : Int) atom0270Coded) := by
  have h := atom0270_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0270Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0271 : SparsePolynomial.Poly := [([0,2,16], 1)]
theorem eval_atom0271 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0271 = ((g 0) * (g 2) * (g 16)) := by
  norm_num [atom0271, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0271_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159127418419200 : Int) atom0271) := by
  rw [SparsePolynomial.eval_scale, eval_atom0271]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0271Coded : CoefficientMerge.Poly := [(64, 1)]
theorem atom0271Coded_decode : atom0271 = SparsePolynomial.decodeCubic 24 atom0271Coded := by decide +kernel
theorem atom0271Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159127418419200 : Int) atom0271Coded) := by
  have h := atom0271_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0271Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0272 : SparsePolynomial.Poly := [([0,2,17], 1)]
theorem eval_atom0272 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0272 = ((g 0) * (g 2) * (g 17)) := by
  norm_num [atom0272, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0272_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161168603904000 : Int) atom0272) := by
  rw [SparsePolynomial.eval_scale, eval_atom0272]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0272Coded : CoefficientMerge.Poly := [(65, 1)]
theorem atom0272Coded_decode : atom0272 = SparsePolynomial.decodeCubic 24 atom0272Coded := by decide +kernel
theorem atom0272Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (161168603904000 : Int) atom0272Coded) := by
  have h := atom0272_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0272Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0273 : SparsePolynomial.Poly := [([0,2,18], 1)]
theorem eval_atom0273 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0273 = ((g 0) * (g 2) * (g 18)) := by
  norm_num [atom0273, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0273_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183818320963200 : Int) atom0273) := by
  rw [SparsePolynomial.eval_scale, eval_atom0273]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0273Coded : CoefficientMerge.Poly := [(66, 1)]
theorem atom0273Coded_decode : atom0273 = SparsePolynomial.decodeCubic 24 atom0273Coded := by decide +kernel
theorem atom0273Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (183818320963200 : Int) atom0273Coded) := by
  have h := atom0273_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0273Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0274 : SparsePolynomial.Poly := [([0,2,19], 1)]
theorem eval_atom0274 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0274 = ((g 0) * (g 2) * (g 19)) := by
  norm_num [atom0274, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0274_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104477866416000 : Int) atom0274) := by
  rw [SparsePolynomial.eval_scale, eval_atom0274]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0274Coded : CoefficientMerge.Poly := [(67, 1)]
theorem atom0274Coded_decode : atom0274 = SparsePolynomial.decodeCubic 24 atom0274Coded := by decide +kernel
theorem atom0274Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (104477866416000 : Int) atom0274Coded) := by
  have h := atom0274_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0274Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0275 : SparsePolynomial.Poly := [([0,2,20], 1)]
theorem eval_atom0275 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0275 = ((g 0) * (g 2) * (g 20)) := by
  norm_num [atom0275, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0275_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90763651440000 : Int) atom0275) := by
  rw [SparsePolynomial.eval_scale, eval_atom0275]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0275Coded : CoefficientMerge.Poly := [(68, 1)]
theorem atom0275Coded_decode : atom0275 = SparsePolynomial.decodeCubic 24 atom0275Coded := by decide +kernel
theorem atom0275Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (90763651440000 : Int) atom0275Coded) := by
  have h := atom0275_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0275Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0276 : SparsePolynomial.Poly := [([0,2,21], 1)]
theorem eval_atom0276 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0276 = ((g 0) * (g 2) * (g 21)) := by
  norm_num [atom0276, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0276_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11423196892800 : Int) atom0276) := by
  rw [SparsePolynomial.eval_scale, eval_atom0276]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 2) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0276Coded : CoefficientMerge.Poly := [(69, 1)]
theorem atom0276Coded_decode : atom0276 = SparsePolynomial.decodeCubic 24 atom0276Coded := by decide +kernel
theorem atom0276Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11423196892800 : Int) atom0276Coded) := by
  have h := atom0276_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0276Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0277 : SparsePolynomial.Poly := [([0,2,22], 1)]
theorem eval_atom0277 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0277 = ((g 0) * (g 2) * (g 22)) := by
  norm_num [atom0277, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0277_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20816644867200 : Int) atom0277) := by
  rw [SparsePolynomial.eval_scale, eval_atom0277]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 2) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0277Coded : CoefficientMerge.Poly := [(70, 1)]
theorem atom0277Coded_decode : atom0277 = SparsePolynomial.decodeCubic 24 atom0277Coded := by decide +kernel
theorem atom0277Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (20816644867200 : Int) atom0277Coded) := by
  have h := atom0277_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0277Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0278 : SparsePolynomial.Poly := [([0,3,3], 1)]
theorem eval_atom0278 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0278 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0278, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0278_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64233555724800 : Int) atom0278) := by
  rw [SparsePolynomial.eval_scale, eval_atom0278]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0278Coded : CoefficientMerge.Poly := [(75, 1)]
theorem atom0278Coded_decode : atom0278 = SparsePolynomial.decodeCubic 24 atom0278Coded := by decide +kernel
theorem atom0278Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (64233555724800 : Int) atom0278Coded) := by
  have h := atom0278_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0278Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0279 : SparsePolynomial.Poly := [([0,3,4], 1)]
theorem eval_atom0279 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0279 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0279, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0279_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131528889676800 : Int) atom0279) := by
  rw [SparsePolynomial.eval_scale, eval_atom0279]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0279Coded : CoefficientMerge.Poly := [(76, 1)]
theorem atom0279Coded_decode : atom0279 = SparsePolynomial.decodeCubic 24 atom0279Coded := by decide +kernel
theorem atom0279Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (131528889676800 : Int) atom0279Coded) := by
  have h := atom0279_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0279Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0280 : SparsePolynomial.Poly := [([0,3,5], 1)]
theorem eval_atom0280 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0280 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0280_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134590667904000 : Int) atom0280) := by
  rw [SparsePolynomial.eval_scale, eval_atom0280]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0280Coded : CoefficientMerge.Poly := [(77, 1)]
theorem atom0280Coded_decode : atom0280 = SparsePolynomial.decodeCubic 24 atom0280Coded := by decide +kernel
theorem atom0280Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134590667904000 : Int) atom0280Coded) := by
  have h := atom0280_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0280Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0281 : SparsePolynomial.Poly := [([0,3,6], 1)]
theorem eval_atom0281 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0281 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0281, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0281_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137652446131200 : Int) atom0281) := by
  rw [SparsePolynomial.eval_scale, eval_atom0281]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0281Coded : CoefficientMerge.Poly := [(78, 1)]
theorem atom0281Coded_decode : atom0281 = SparsePolynomial.decodeCubic 24 atom0281Coded := by decide +kernel
theorem atom0281Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (137652446131200 : Int) atom0281Coded) := by
  have h := atom0281_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0281Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0282 : SparsePolynomial.Poly := [([0,3,7], 1)]
theorem eval_atom0282 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0282 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0282, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0282_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140714224358400 : Int) atom0282) := by
  rw [SparsePolynomial.eval_scale, eval_atom0282]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0282Coded : CoefficientMerge.Poly := [(79, 1)]
theorem atom0282Coded_decode : atom0282 = SparsePolynomial.decodeCubic 24 atom0282Coded := by decide +kernel
theorem atom0282Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (140714224358400 : Int) atom0282Coded) := by
  have h := atom0282_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0282Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0283 : SparsePolynomial.Poly := [([0,3,8], 1)]
theorem eval_atom0283 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0283 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0283, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0283_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (143776002585600 : Int) atom0283) := by
  rw [SparsePolynomial.eval_scale, eval_atom0283]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0283Coded : CoefficientMerge.Poly := [(80, 1)]
theorem atom0283Coded_decode : atom0283 = SparsePolynomial.decodeCubic 24 atom0283Coded := by decide +kernel
theorem atom0283Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (143776002585600 : Int) atom0283Coded) := by
  have h := atom0283_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0283Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0284 : SparsePolynomial.Poly := [([0,3,9], 1)]
theorem eval_atom0284 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0284 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0284, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0284_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146837780812800 : Int) atom0284) := by
  rw [SparsePolynomial.eval_scale, eval_atom0284]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0284Coded : CoefficientMerge.Poly := [(81, 1)]
theorem atom0284Coded_decode : atom0284 = SparsePolynomial.decodeCubic 24 atom0284Coded := by decide +kernel
theorem atom0284Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146837780812800 : Int) atom0284Coded) := by
  have h := atom0284_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0284Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0285 : SparsePolynomial.Poly := [([0,3,10], 1)]
theorem eval_atom0285 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0285 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0285, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0285_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149899559040000 : Int) atom0285) := by
  rw [SparsePolynomial.eval_scale, eval_atom0285]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0285Coded : CoefficientMerge.Poly := [(82, 1)]
theorem atom0285Coded_decode : atom0285 = SparsePolynomial.decodeCubic 24 atom0285Coded := by decide +kernel
theorem atom0285Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149899559040000 : Int) atom0285Coded) := by
  have h := atom0285_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0285Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0286 : SparsePolynomial.Poly := [([0,3,11], 1)]
theorem eval_atom0286 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0286 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0286, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0286_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157608664031808 : Int) atom0286) := by
  rw [SparsePolynomial.eval_scale, eval_atom0286]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0286Coded : CoefficientMerge.Poly := [(83, 1)]
theorem atom0286Coded_decode : atom0286 = SparsePolynomial.decodeCubic 24 atom0286Coded := by decide +kernel
theorem atom0286Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (157608664031808 : Int) atom0286Coded) := by
  have h := atom0286_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0286Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0287 : SparsePolynomial.Poly := [([0,3,12], 1)]
theorem eval_atom0287 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0287 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0287, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0287_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210348325554048 : Int) atom0287) := by
  rw [SparsePolynomial.eval_scale, eval_atom0287]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0287Coded : CoefficientMerge.Poly := [(84, 1)]
theorem atom0287Coded_decode : atom0287 = SparsePolynomial.decodeCubic 24 atom0287Coded := by decide +kernel
theorem atom0287Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (210348325554048 : Int) atom0287Coded) := by
  have h := atom0287_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0287Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0288 : SparsePolynomial.Poly := [([0,3,13], 1)]
theorem eval_atom0288 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0288 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0288, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0288_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189921761568000 : Int) atom0288) := by
  rw [SparsePolynomial.eval_scale, eval_atom0288]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0288Coded : CoefficientMerge.Poly := [(85, 1)]
theorem atom0288Coded_decode : atom0288 = SparsePolynomial.decodeCubic 24 atom0288Coded := by decide +kernel
theorem atom0288Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (189921761568000 : Int) atom0288Coded) := by
  have h := atom0288_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0288Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block005 : CoefficientMerge.Poly := [(11, 2323663382304), (12, 27162605029824), (13, 15418433923200), (18, 11502930700800), (19, 8419890124800), (20, 5336849548800), (21, 2253808972800), (25, 2338858368000), (26, 60480751161600), (27, 59959823616000), (28, 59438896070400), (29, 62359415395200), (30, 58397040979200), (31, 57876113433600), (32, 57355185888000), (33, 59840148865464), (34, 68140969836984), (35, 79108072262208), (36, 129806548299648), (37, 107338798828800), (38, 77522523724800), (39, 78227402803200), (40, 73021026758400), (41, 72781019942400), (42, 102984186412800), (43, 40961914963200), (44, 12512892268800), (45, 5205731731200), (46, 4086988550400), (50, 65275410816000), (51, 132592007116800), (52, 134633192601600), (53, 136674378086400), (54, 138715563571200), (55, 140756749056000), (56, 142797934540800), (57, 144839120025600), (58, 146880305510400), (59, 153568817759808), (60, 205287886539648), (61, 183840729811200), (62, 155045047449600), (63, 157086232934400), (64, 159127418419200), (65, 161168603904000), (66, 183818320963200), (67, 104477866416000), (68, 90763651440000), (69, 11423196892800), (70, 20816644867200), (75, 64233555724800), (76, 131528889676800), (77, 134590667904000), (78, 137652446131200), (79, 140714224358400), (80, 143776002585600), (81, 146837780812800), (82, 149899559040000), (83, 157608664031808), (84, 210348325554048), (85, 189921761568000), (252, -4473274189824), (275, -20576091305088), (276, -56738800521216), (277, -13409545171968), (300, -49750818213888), (301, -51341575431168), (302, -4500641870208), (325, -56668745548800), (326, -61665751889280), (327, -5424680862720), (350, -60074994672000), (351, -59078112670080), (352, -1609463157120), (375, -54081106329600), (376, -45862757498880), (400, -46859639500800), (401, -18606058598400), (425, -30787881062400), (475, -4898845163520), (828, -6709911284736), (851, -30864136957632), (852, -85108200781824), (853, -20114317757952), (876, -74626227320832), (877, -77012363146752), (878, -6750962805312), (901, -85003118323200), (902, -92498627833920), (903, -8137021294080), (926, -90112492008000), (927, -88617169005120), (928, -2414194735680), (951, -81121659494400), (952, -68794136248320), (976, -70289459251200), (977, -27909087897600), (1001, -46181821593600), (1051, -7348267745280), (1404, -8946548379648), (1427, -41152182610176), (1428, -113477601042432), (1429, -26819090343936), (1452, -99501636427776), (1453, -102683150862336), (1454, -9001283740416), (1477, -113337491097600), (1478, -123331503778560), (1479, -10849361725440), (1502, -120149989344000), (1503, -118156225340160), (1504, -3218926314240), (1527, -108162212659200), (1528, -91725514997760), (1552, -93719279001600), (1553, -37212117196800), (1577, -61575762124800), (1627, -9797690327040), (1980, -8946548379648), (2003, -41152182610176), (2004, -113477601042432), (2005, -26819090343936), (2028, -99501636427776), (2029, -102683150862336), (2030, -9001283740416), (2053, -113337491097600), (2054, -123331503778560), (2055, -10849361725440), (2078, -120149989344000), (2079, -118156225340160), (2080, -3218926314240), (2103, -108162212659200), (2104, -91725514997760), (2128, -93719279001600), (2129, -37212117196800), (2153, -61575762124800), (2203, -9797690327040), (2556, -8946548379648), (2579, -41152182610176), (2580, -113477601042432), (2581, -26819090343936), (2604, -99501636427776), (2605, -102683150862336), (2606, -9001283740416), (2629, -113337491097600), (2630, -123331503778560), (2631, -10849361725440), (2654, -120149989344000), (2655, -118156225340160), (2656, -3218926314240), (2679, -108162212659200), (2680, -91725514997760), (2704, -93719279001600), (2705, -37212117196800), (2729, -61575762124800), (2779, -9797690327040), (3132, -8946548379648), (3155, -41152182610176), (3156, -113477601042432), (3157, -26819090343936), (3180, -99501636427776), (3181, -102683150862336), (3182, -9001283740416), (3205, -113337491097600), (3206, -123331503778560), (3207, -10849361725440), (3230, -120149989344000), (3231, -118156225340160), (3232, -3218926314240), (3255, -108162212659200), (3256, -91725514997760), (3280, -93719279001600), (3281, -37212117196800), (3305, -61575762124800), (3355, -9797690327040), (3708, -8946548379648), (3731, -41152182610176), (3732, -113477601042432), (3733, -26819090343936), (3756, -99501636427776), (3757, -102683150862336), (3758, -9001283740416), (3781, -113337491097600), (3782, -123331503778560), (3783, -10849361725440), (3806, -120149989344000), (3807, -118156225340160), (3808, -3218926314240), (3831, -108162212659200), (3832, -91725514997760), (3856, -93719279001600), (3857, -37212117196800), (3881, -61575762124800), (3931, -9797690327040), (4284, -8946548379648), (4307, -41152182610176), (4308, -113477601042432), (4309, -26819090343936), (4332, -99501636427776), (4333, -102683150862336), (4334, -9001283740416), (4357, -113337491097600), (4358, -123331503778560), (4359, -10849361725440), (4382, -120149989344000), (4383, -118156225340160), (4384, -3218926314240), (4407, -108162212659200), (4408, -91725514997760), (4432, -93719279001600), (4433, -37212117196800), (4457, -61575762124800), (4507, -9797690327040), (4860, -8946548379648), (4883, -41152182610176), (4884, -113477601042432), (4885, -26819090343936), (4908, -99501636427776), (4909, -102683150862336), (4910, -9001283740416), (4933, -113337491097600), (4934, -123331503778560), (4935, -10849361725440), (4958, -120149989344000), (4959, -118156225340160), (4960, -3218926314240), (4983, -108162212659200), (4984, -91725514997760), (5008, -93719279001600), (5009, -37212117196800), (5033, -61575762124800), (5083, -9797690327040), (5436, -8946548379648), (5459, -41152182610176), (5460, -113477601042432), (5461, -26819090343936), (5484, -99501636427776), (5485, -102683150862336), (5486, -9001283740416), (5509, -113337491097600), (5510, -123331503778560), (5511, -10849361725440), (5534, -120149989344000), (5535, -118156225340160), (5536, -3218926314240), (5559, -108162212659200), (5560, -91725514997760), (5584, -93719279001600), (5585, -37212117196800), (5609, -61575762124800), (5659, -9797690327040), (6012, -8946548379648), (6035, -41152182610176), (6036, -122424149422080), (6037, -26819090343936), (6060, -108448184807424), (6061, -111629699241984), (6062, -17947832120064), (6063, -8946548379648), (6064, -8946548379648), (6065, -8946548379648), (6066, -7828229832192), (6067, -5591592737280), (6068, -1118318547456), (6069, 1118318547456), (6070, 5591592737280), (6071, 10064866927104), (6085, -113337491097600), (6086, -123331503778560), (6087, -10849361725440), (6110, -120149989344000), (6111, -118156225340160), (6112, -3218926314240), (6135, -108162212659200), (6136, -91725514997760), (6160, -93719279001600), (6161, -37212117196800), (6185, -61575762124800), (6235, -9797690327040), (6611, -41152182610176), (6612, -154629783652608), (6613, -67971272954112), (6614, -41152182610176), (6615, -41152182610176), (6616, -41152182610176), (6617, -41152182610176), (6618, -36008159783904), (6619, -25720114131360), (6620, -5144022826272), (6621, 5144022826272), (6622, 25720114131360), (6623, 46296205436448), (6636, -212979237470208), (6637, -242979842248704), (6638, -122478884782848), (6639, -113477601042432), (6640, -113477601042432), (6641, -113477601042432), (6642, -99292900912128), (6643, -70923500651520), (6644, -14184700130304), (6645, 14184700130304), (6646, 70923500651520), (6647, 127662301172736), (6661, -140156581441536), (6662, -150150594122496), (6663, -37668452069376), (6664, -26819090343936), (6665, -26819090343936), (6666, -23466704050944), (6667, -16761931464960), (6668, -3352386292992), (6669, 3352386292992), (6670, 16761931464960), (6671, 30171476636928), (6686, -120149989344000), (6687, -118156225340160), (6688, -3218926314240), (6711, -108162212659200), (6712, -91725514997760), (6736, -93719279001600), (6737, -37212117196800), (6761, -61575762124800), (6811, -9797690327040), (7212, -99501636427776), (7213, -202184787290112), (7214, -108502920168192), (7215, -99501636427776), (7216, -99501636427776), (7217, -99501636427776), (7218, -87063931874304), (7219, -62188522767360), (7220, -12437704553472), (7221, 12437704553472), (7222, 62188522767360), (7223, 111939340981248), (7237, -216020641959936), (7238, -235015938381312), (7239, -113532512587776), (7240, -102683150862336), (7241, -102683150862336), (7242, -89847757004544), (7243, -64176969288960), (7244, -12835393857792), (7245, 12835393857792), (7246, 64176969288960), (7247, 115518544720128), (7262, -129151273084416), (7263, -127157509080576), (7264, -12220210054656), (7265, -9001283740416), (7266, -7876123272864), (7267, -5625802337760), (7268, -1125160467552), (7269, 1125160467552), (7270, 5625802337760), (7271, 10126444207968), (7287, -108162212659200), (7288, -91725514997760), (7312, -93719279001600), (7313, -37212117196800), (7337, -61575762124800), (7387, -9797690327040), (7813, -113337491097600), (7814, -236668994876160), (7815, -124186852823040), (7816, -113337491097600), (7817, -113337491097600), (7818, -99170304710400), (7819, -70835931936000), (7820, -14167186387200), (7821, 14167186387200), (7822, 70835931936000), (7823, 127504677484800), (7838, -243481493122560), (7839, -252337090844160), (7840, -126550430092800), (7841, -123331503778560), (7842, -107915065806240), (7843, -77082189861600), (7844, -15416437972320), (7845, 15416437972320), (7846, 77082189861600), (7847, 138747941750880), (7863, -119011574384640), (7864, -102574876723200), (7865, -10849361725440), (7866, -9493191509760), (7867, -6780851078400), (7868, -1356170215680), (7869, 1356170215680), (7870, 6780851078400), (7871, 12205531941120), (7888, -93719279001600), (7889, -37212117196800), (7913, -61575762124800), (7963, -9797690327040), (8414, -120149989344000), (8415, -238306214684160), (8416, -123368915658240), (8417, -120149989344000), (8418, -105131240676000), (8419, -75093743340000), (8420, -15018748668000), (8421, 15018748668000), (8422, 75093743340000), (8423, 135168738012000), (8439, -226318437999360), (8440, -213100666652160), (8441, -118156225340160), (8442, -103386697172640), (8443, -73847640837600), (8444, -14769528167520), (8445, 14769528167520), (8446, 73847640837600), (8447, 132925753507680), (8464, -96938205315840), (8465, -40431043511040), (8466, -2816560524960), (8467, -2011828946400), (8468, -402365789280), (8469, 402365789280), (8470, 2011828946400), (8471, 3621292103520), (8489, -61575762124800), (8539, -9797690327040), (9015, -108162212659200), (9016, -199887727656960), (9017, -108162212659200), (9018, -94641936076800), (9019, -67601382912000), (9020, -13520276582400), (9021, 13520276582400), (9022, 67601382912000), (9023, 121682489241600), (9040, -185444793999360), (9041, -128937632194560), (9042, -80259825623040), (9043, -57328446873600), (9044, -11465689374720), (9045, 11465689374720), (9046, 57328446873600), (9047, 103191204372480), (9065, -61575762124800), (9115, -9797690327040), (9616, -93719279001600), (9617, -130931396198400), (9618, -82004369126400), (9619, -58574549376000), (9620, -11714909875200), (9621, 11714909875200), (9622, 58574549376000), (9623, 105434188876800), (9641, -98787879321600), (9642, -32560602547200), (9643, -23257573248000), (9644, -4651514649600), (9645, 4651514649600), (9646, 23257573248000), (9647, 41863631846400), (9691, -9797690327040), (10217, -61575762124800), (10218, -53878791859200), (10219, -38484851328000), (10220, -7696970265600), (10221, 7696970265600), (10222, 38484851328000), (10223, 69272732390400), (10267, -9797690327040), (10843, -8572979036160), (11419, -6123556454400), (11420, -1224711290880), (11421, 1224711290880), (11422, 6123556454400), (11423, 11022401617920)]
theorem block005_data : block005 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (559159273728 : Int) atom0209Coded) (CoefficientMerge.scale (2572011413136 : Int) atom0210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7092350065152 : Int) atom0211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1676193146496 : Int) atom0212Coded) (CoefficientMerge.scale (6218852276736 : Int) atom0213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6417696928896 : Int) atom0214Coded) (CoefficientMerge.scale (562580233776 : Int) atom0215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7083593193600 : Int) atom0216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7708218986160 : Int) atom0217Coded) (CoefficientMerge.scale (678085107840 : Int) atom0218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7509374334000 : Int) atom0219Coded) (CoefficientMerge.scale (7384764083760 : Int) atom0220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (201182894640 : Int) atom0221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6760138291200 : Int) atom0222Coded) (CoefficientMerge.scale (5732844687360 : Int) atom0223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5857454937600 : Int) atom0224Coded) (CoefficientMerge.scale (2325757324800 : Int) atom0225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3848485132800 : Int) atom0226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (612355645440 : Int) atom0227Coded) (CoefficientMerge.scale (2323663382304 : Int) atom0228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27162605029824 : Int) atom0229Coded) (CoefficientMerge.scale (15418433923200 : Int) atom0230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11502930700800 : Int) atom0231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8419890124800 : Int) atom0232Coded) (CoefficientMerge.scale (5336849548800 : Int) atom0233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2253808972800 : Int) atom0234Coded) (CoefficientMerge.scale (2338858368000 : Int) atom0235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480751161600 : Int) atom0236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59959823616000 : Int) atom0237Coded) (CoefficientMerge.scale (59438896070400 : Int) atom0238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62359415395200 : Int) atom0239Coded) (CoefficientMerge.scale (58397040979200 : Int) atom0240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57876113433600 : Int) atom0241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57355185888000 : Int) atom0242Coded) (CoefficientMerge.scale (59840148865464 : Int) atom0243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68140969836984 : Int) atom0244Coded) (CoefficientMerge.scale (79108072262208 : Int) atom0245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (129806548299648 : Int) atom0246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107338798828800 : Int) atom0247Coded) (CoefficientMerge.scale (77522523724800 : Int) atom0248Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (78227402803200 : Int) atom0249Coded) (CoefficientMerge.scale (73021026758400 : Int) atom0250Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (72781019942400 : Int) atom0251Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102984186412800 : Int) atom0252Coded) (CoefficientMerge.scale (40961914963200 : Int) atom0253Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12512892268800 : Int) atom0254Coded) (CoefficientMerge.scale (5205731731200 : Int) atom0255Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4086988550400 : Int) atom0256Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65275410816000 : Int) atom0257Coded) (CoefficientMerge.scale (132592007116800 : Int) atom0258Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (134633192601600 : Int) atom0259Coded) (CoefficientMerge.scale (136674378086400 : Int) atom0260Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (138715563571200 : Int) atom0261Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140756749056000 : Int) atom0262Coded) (CoefficientMerge.scale (142797934540800 : Int) atom0263Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (144839120025600 : Int) atom0264Coded) (CoefficientMerge.scale (146880305510400 : Int) atom0265Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153568817759808 : Int) atom0266Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (205287886539648 : Int) atom0267Coded) (CoefficientMerge.scale (183840729811200 : Int) atom0268Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155045047449600 : Int) atom0269Coded) (CoefficientMerge.scale (157086232934400 : Int) atom0270Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159127418419200 : Int) atom0271Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161168603904000 : Int) atom0272Coded) (CoefficientMerge.scale (183818320963200 : Int) atom0273Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (104477866416000 : Int) atom0274Coded) (CoefficientMerge.scale (90763651440000 : Int) atom0275Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11423196892800 : Int) atom0276Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20816644867200 : Int) atom0277Coded) (CoefficientMerge.scale (64233555724800 : Int) atom0278Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (131528889676800 : Int) atom0279Coded) (CoefficientMerge.scale (134590667904000 : Int) atom0280Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (137652446131200 : Int) atom0281Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140714224358400 : Int) atom0282Coded) (CoefficientMerge.scale (143776002585600 : Int) atom0283Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146837780812800 : Int) atom0284Coded) (CoefficientMerge.scale (149899559040000 : Int) atom0285Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608664031808 : Int) atom0286Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210348325554048 : Int) atom0287Coded) (CoefficientMerge.scale (189921761568000 : Int) atom0288Coded)))))))) := by decide +kernel
theorem block005_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block005 := by
  rw [block005_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0209Coded_nonneg g hg hA hB) (atom0210Coded_nonneg g hg hA hB)) (add_nonneg (atom0211Coded_nonneg g hg hA hB) (add_nonneg (atom0212Coded_nonneg g hg hA hB) (atom0213Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0214Coded_nonneg g hg hA hB) (atom0215Coded_nonneg g hg hA hB)) (add_nonneg (atom0216Coded_nonneg g hg hA hB) (add_nonneg (atom0217Coded_nonneg g hg hA hB) (atom0218Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0219Coded_nonneg g hg hA hB) (atom0220Coded_nonneg g hg hA hB)) (add_nonneg (atom0221Coded_nonneg g hg hA hB) (add_nonneg (atom0222Coded_nonneg g hg hA hB) (atom0223Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0224Coded_nonneg g hg hA hB) (atom0225Coded_nonneg g hg hA hB)) (add_nonneg (atom0226Coded_nonneg g hg hA hB) (add_nonneg (atom0227Coded_nonneg g hg hA hB) (atom0228Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0229Coded_nonneg g hg hA hB) (atom0230Coded_nonneg g hg hA hB)) (add_nonneg (atom0231Coded_nonneg g hg hA hB) (add_nonneg (atom0232Coded_nonneg g hg hA hB) (atom0233Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0234Coded_nonneg g hg hA hB) (atom0235Coded_nonneg g hg hA hB)) (add_nonneg (atom0236Coded_nonneg g hg hA hB) (add_nonneg (atom0237Coded_nonneg g hg hA hB) (atom0238Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0239Coded_nonneg g hg hA hB) (atom0240Coded_nonneg g hg hA hB)) (add_nonneg (atom0241Coded_nonneg g hg hA hB) (add_nonneg (atom0242Coded_nonneg g hg hA hB) (atom0243Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0244Coded_nonneg g hg hA hB) (atom0245Coded_nonneg g hg hA hB)) (add_nonneg (atom0246Coded_nonneg g hg hA hB) (add_nonneg (atom0247Coded_nonneg g hg hA hB) (atom0248Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0249Coded_nonneg g hg hA hB) (atom0250Coded_nonneg g hg hA hB)) (add_nonneg (atom0251Coded_nonneg g hg hA hB) (add_nonneg (atom0252Coded_nonneg g hg hA hB) (atom0253Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0254Coded_nonneg g hg hA hB) (atom0255Coded_nonneg g hg hA hB)) (add_nonneg (atom0256Coded_nonneg g hg hA hB) (add_nonneg (atom0257Coded_nonneg g hg hA hB) (atom0258Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0259Coded_nonneg g hg hA hB) (atom0260Coded_nonneg g hg hA hB)) (add_nonneg (atom0261Coded_nonneg g hg hA hB) (add_nonneg (atom0262Coded_nonneg g hg hA hB) (atom0263Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0264Coded_nonneg g hg hA hB) (atom0265Coded_nonneg g hg hA hB)) (add_nonneg (atom0266Coded_nonneg g hg hA hB) (add_nonneg (atom0267Coded_nonneg g hg hA hB) (atom0268Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0269Coded_nonneg g hg hA hB) (atom0270Coded_nonneg g hg hA hB)) (add_nonneg (atom0271Coded_nonneg g hg hA hB) (add_nonneg (atom0272Coded_nonneg g hg hA hB) (atom0273Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0274Coded_nonneg g hg hA hB) (atom0275Coded_nonneg g hg hA hB)) (add_nonneg (atom0276Coded_nonneg g hg hA hB) (add_nonneg (atom0277Coded_nonneg g hg hA hB) (atom0278Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0279Coded_nonneg g hg hA hB) (atom0280Coded_nonneg g hg hA hB)) (add_nonneg (atom0281Coded_nonneg g hg hA hB) (add_nonneg (atom0282Coded_nonneg g hg hA hB) (atom0283Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0284Coded_nonneg g hg hA hB) (atom0285Coded_nonneg g hg hA hB)) (add_nonneg (atom0286Coded_nonneg g hg hA hB) (add_nonneg (atom0287Coded_nonneg g hg hA hB) (atom0288Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
