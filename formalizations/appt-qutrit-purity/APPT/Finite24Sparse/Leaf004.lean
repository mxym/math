import APPT.Finite24Sparse.Base07
import APPT.Finite24Sparse.Base08
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0129 : SparsePolynomial.Poly := [([0,9,16], -4), ([1,9,16], -8), ([2,9,16], -16), ([3,9,16], -16), ([4,9,16], -16), ([5,9,16], -16), ([6,9,16], -16), ([7,9,16], -16), ([8,9,16], -16), ([9,9,16], -16), ([9,10,16], -16), ([9,11,16], -16), ([9,12,16], -16), ([9,13,16], -16), ([9,14,16], -16), ([9,15,16], -16), ([9,16,16], -16), ([9,16,17], -16), ([9,16,18], -8), ([9,16,20], 8), ([9,16,21], 12), ([9,16,22], 16), ([9,16,23], 18)]
theorem atom0129_data : atom0129 = SparsePolynomial.monoTimes [9,16] 1 base07 := by decide +kernel
theorem eval_atom0129 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0129 = (quadB (outer g) ![1,2,2] * g 9 * g 16) := by
  rw [atom0129_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0129_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4302807205842 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129Coded : CoefficientMerge.Poly := [(232, -4), (808, -8), (1384, -16), (1960, -16), (2536, -16), (3112, -16), (3688, -16), (4264, -16), (4840, -16), (5416, -16), (5440, -16), (5464, -16), (5488, -16), (5512, -16), (5536, -16), (5560, -16), (5584, -16), (5585, -16), (5586, -8), (5588, 8), (5589, 12), (5590, 16), (5591, 18)]
theorem atom0129Coded_decode : atom0129 = SparsePolynomial.decodeCubic 24 atom0129Coded := by decide +kernel
theorem atom0129Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4302807205842 : Int) atom0129Coded) := by
  have h := atom0129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0130 : SparsePolynomial.Poly := [([0,9,17], -4), ([1,9,17], -8), ([2,9,17], -16), ([3,9,17], -16), ([4,9,17], -16), ([5,9,17], -16), ([6,9,17], -16), ([7,9,17], -16), ([8,9,17], -16), ([9,9,17], -16), ([9,10,17], -16), ([9,11,17], -16), ([9,12,17], -16), ([9,13,17], -16), ([9,14,17], -16), ([9,15,17], -16), ([9,16,17], -16), ([9,17,17], -16), ([9,17,18], -8), ([9,17,20], 8), ([9,17,21], 12), ([9,17,22], 16), ([9,17,23], 18)]
theorem atom0130_data : atom0130 = SparsePolynomial.monoTimes [9,17] 1 base07 := by decide +kernel
theorem eval_atom0130 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0130 = (quadB (outer g) ![1,2,2] * g 9 * g 17) := by
  rw [atom0130_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0130_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3324175386642 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130Coded : CoefficientMerge.Poly := [(233, -4), (809, -8), (1385, -16), (1961, -16), (2537, -16), (3113, -16), (3689, -16), (4265, -16), (4841, -16), (5417, -16), (5441, -16), (5465, -16), (5489, -16), (5513, -16), (5537, -16), (5561, -16), (5585, -16), (5609, -16), (5610, -8), (5612, 8), (5613, 12), (5614, 16), (5615, 18)]
theorem atom0130Coded_decode : atom0130 = SparsePolynomial.decodeCubic 24 atom0130Coded := by decide +kernel
theorem atom0130Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3324175386642 : Int) atom0130Coded) := by
  have h := atom0130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0131 : SparsePolynomial.Poly := [([0,9,18], -4), ([1,9,18], -8), ([2,9,18], -16), ([3,9,18], -16), ([4,9,18], -16), ([5,9,18], -16), ([6,9,18], -16), ([7,9,18], -16), ([8,9,18], -16), ([9,9,18], -16), ([9,10,18], -16), ([9,11,18], -16), ([9,12,18], -16), ([9,13,18], -16), ([9,14,18], -16), ([9,15,18], -16), ([9,16,18], -16), ([9,17,18], -16), ([9,18,18], -8), ([9,18,20], 8), ([9,18,21], 12), ([9,18,22], 16), ([9,18,23], 18)]
theorem atom0131_data : atom0131 = SparsePolynomial.monoTimes [9,18] 1 base07 := by decide +kernel
theorem eval_atom0131 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0131 = (quadB (outer g) ![1,2,2] * g 9 * g 18) := by
  rw [atom0131_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0131_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1511071623666 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 18) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131Coded : CoefficientMerge.Poly := [(234, -4), (810, -8), (1386, -16), (1962, -16), (2538, -16), (3114, -16), (3690, -16), (4266, -16), (4842, -16), (5418, -16), (5442, -16), (5466, -16), (5490, -16), (5514, -16), (5538, -16), (5562, -16), (5586, -16), (5610, -16), (5634, -8), (5636, 8), (5637, 12), (5638, 16), (5639, 18)]
theorem atom0131Coded_decode : atom0131 = SparsePolynomial.decodeCubic 24 atom0131Coded := by decide +kernel
theorem atom0131Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1511071623666 : Int) atom0131Coded) := by
  have h := atom0131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0132 : SparsePolynomial.Poly := [([0,9,19], -4), ([1,9,19], -8), ([2,9,19], -16), ([3,9,19], -16), ([4,9,19], -16), ([5,9,19], -16), ([6,9,19], -16), ([7,9,19], -16), ([8,9,19], -16), ([9,9,19], -16), ([9,10,19], -16), ([9,11,19], -16), ([9,12,19], -16), ([9,13,19], -16), ([9,14,19], -16), ([9,15,19], -16), ([9,16,19], -16), ([9,17,19], -16), ([9,18,19], -8), ([9,19,20], 8), ([9,19,21], 12), ([9,19,22], 16), ([9,19,23], 18)]
theorem atom0132_data : atom0132 = SparsePolynomial.monoTimes [9,19] 1 base07 := by decide +kernel
theorem eval_atom0132 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0132 = (quadB (outer g) ![1,2,2] * g 9 * g 19) := by
  rw [atom0132_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0132_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7003753939314 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132Coded : CoefficientMerge.Poly := [(235, -4), (811, -8), (1387, -16), (1963, -16), (2539, -16), (3115, -16), (3691, -16), (4267, -16), (4843, -16), (5419, -16), (5443, -16), (5467, -16), (5491, -16), (5515, -16), (5539, -16), (5563, -16), (5587, -16), (5611, -16), (5635, -8), (5660, 8), (5661, 12), (5662, 16), (5663, 18)]
theorem atom0132Coded_decode : atom0132 = SparsePolynomial.decodeCubic 24 atom0132Coded := by decide +kernel
theorem atom0132Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7003753939314 : Int) atom0132Coded) := by
  have h := atom0132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0133 : SparsePolynomial.Poly := [([0,9,20], -4), ([1,9,20], -8), ([2,9,20], -16), ([3,9,20], -16), ([4,9,20], -16), ([5,9,20], -16), ([6,9,20], -16), ([7,9,20], -16), ([8,9,20], -16), ([9,9,20], -16), ([9,10,20], -16), ([9,11,20], -16), ([9,12,20], -16), ([9,13,20], -16), ([9,14,20], -16), ([9,15,20], -16), ([9,16,20], -16), ([9,17,20], -16), ([9,18,20], -8), ([9,20,20], 8), ([9,20,21], 12), ([9,20,22], 16), ([9,20,23], 18)]
theorem atom0133_data : atom0133 = SparsePolynomial.monoTimes [9,20] 1 base07 := by decide +kernel
theorem eval_atom0133 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0133 = (quadB (outer g) ![1,2,2] * g 9 * g 20) := by
  rw [atom0133_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0133_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3693823851762 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133Coded : CoefficientMerge.Poly := [(236, -4), (812, -8), (1388, -16), (1964, -16), (2540, -16), (3116, -16), (3692, -16), (4268, -16), (4844, -16), (5420, -16), (5444, -16), (5468, -16), (5492, -16), (5516, -16), (5540, -16), (5564, -16), (5588, -16), (5612, -16), (5636, -8), (5684, 8), (5685, 12), (5686, 16), (5687, 18)]
theorem atom0133Coded_decode : atom0133 = SparsePolynomial.decodeCubic 24 atom0133Coded := by decide +kernel
theorem atom0133Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3693823851762 : Int) atom0133Coded) := by
  have h := atom0133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0134 : SparsePolynomial.Poly := [([0,9,21], -4), ([1,9,21], -8), ([2,9,21], -16), ([3,9,21], -16), ([4,9,21], -16), ([5,9,21], -16), ([6,9,21], -16), ([7,9,21], -16), ([8,9,21], -16), ([9,9,21], -16), ([9,10,21], -16), ([9,11,21], -16), ([9,12,21], -16), ([9,13,21], -16), ([9,14,21], -16), ([9,15,21], -16), ([9,16,21], -16), ([9,17,21], -16), ([9,18,21], -8), ([9,20,21], 8), ([9,21,21], 12), ([9,21,22], 16), ([9,21,23], 18)]
theorem atom0134_data : atom0134 = SparsePolynomial.monoTimes [9,21] 1 base07 := by decide +kernel
theorem eval_atom0134 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0134 = (quadB (outer g) ![1,2,2] * g 9 * g 21) := by
  rw [atom0134_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0134_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11221399009458 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134Coded : CoefficientMerge.Poly := [(237, -4), (813, -8), (1389, -16), (1965, -16), (2541, -16), (3117, -16), (3693, -16), (4269, -16), (4845, -16), (5421, -16), (5445, -16), (5469, -16), (5493, -16), (5517, -16), (5541, -16), (5565, -16), (5589, -16), (5613, -16), (5637, -8), (5685, 8), (5709, 12), (5710, 16), (5711, 18)]
theorem atom0134Coded_decode : atom0134 = SparsePolynomial.decodeCubic 24 atom0134Coded := by decide +kernel
theorem atom0134Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11221399009458 : Int) atom0134Coded) := by
  have h := atom0134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0135 : SparsePolynomial.Poly := [([0,9,22], -4), ([1,9,22], -8), ([2,9,22], -16), ([3,9,22], -16), ([4,9,22], -16), ([5,9,22], -16), ([6,9,22], -16), ([7,9,22], -16), ([8,9,22], -16), ([9,9,22], -16), ([9,10,22], -16), ([9,11,22], -16), ([9,12,22], -16), ([9,13,22], -16), ([9,14,22], -16), ([9,15,22], -16), ([9,16,22], -16), ([9,17,22], -16), ([9,18,22], -8), ([9,20,22], 8), ([9,21,22], 12), ([9,22,22], 16), ([9,22,23], 18)]
theorem atom0135_data : atom0135 = SparsePolynomial.monoTimes [9,22] 1 base07 := by decide +kernel
theorem eval_atom0135 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0135 = (quadB (outer g) ![1,2,2] * g 9 * g 22) := by
  rw [atom0135_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0135_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5188983412800 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135Coded : CoefficientMerge.Poly := [(238, -4), (814, -8), (1390, -16), (1966, -16), (2542, -16), (3118, -16), (3694, -16), (4270, -16), (4846, -16), (5422, -16), (5446, -16), (5470, -16), (5494, -16), (5518, -16), (5542, -16), (5566, -16), (5590, -16), (5614, -16), (5638, -8), (5686, 8), (5710, 12), (5734, 16), (5735, 18)]
theorem atom0135Coded_decode : atom0135 = SparsePolynomial.decodeCubic 24 atom0135Coded := by decide +kernel
theorem atom0135Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5188983412800 : Int) atom0135Coded) := by
  have h := atom0135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0136 : SparsePolynomial.Poly := [([0,9,23], -4), ([1,9,23], -8), ([2,9,23], -16), ([3,9,23], -16), ([4,9,23], -16), ([5,9,23], -16), ([6,9,23], -16), ([7,9,23], -16), ([8,9,23], -16), ([9,9,23], -16), ([9,10,23], -16), ([9,11,23], -16), ([9,12,23], -16), ([9,13,23], -16), ([9,14,23], -16), ([9,15,23], -16), ([9,16,23], -16), ([9,17,23], -16), ([9,18,23], -8), ([9,20,23], 8), ([9,21,23], 12), ([9,22,23], 16), ([9,23,23], 18)]
theorem atom0136_data : atom0136 = SparsePolynomial.monoTimes [9,23] 1 base07 := by decide +kernel
theorem eval_atom0136 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0136 = (quadB (outer g) ![1,2,2] * g 9 * g 23) := by
  rw [atom0136_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0136_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9065709577728 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136Coded : CoefficientMerge.Poly := [(239, -4), (815, -8), (1391, -16), (1967, -16), (2543, -16), (3119, -16), (3695, -16), (4271, -16), (4847, -16), (5423, -16), (5447, -16), (5471, -16), (5495, -16), (5519, -16), (5543, -16), (5567, -16), (5591, -16), (5615, -16), (5639, -8), (5687, 8), (5711, 12), (5735, 16), (5759, 18)]
theorem atom0136Coded_decode : atom0136 = SparsePolynomial.decodeCubic 24 atom0136Coded := by decide +kernel
theorem atom0136Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9065709577728 : Int) atom0136Coded) := by
  have h := atom0136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0137 : SparsePolynomial.Poly := [([0,10,11], -4), ([1,10,11], -8), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -16), ([10,11,13], -16), ([10,11,14], -16), ([10,11,15], -16), ([10,11,16], -16), ([10,11,17], -16), ([10,11,18], -8), ([10,11,20], 8), ([10,11,21], 12), ([10,11,22], 16), ([10,11,23], 18)]
theorem atom0137_data : atom0137 = SparsePolynomial.monoTimes [10,11] 1 base07 := by decide +kernel
theorem eval_atom0137 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0137 = (quadB (outer g) ![1,2,2] * g 10 * g 11) := by
  rw [atom0137_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0137_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3352540847040 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137Coded : CoefficientMerge.Poly := [(251, -4), (827, -8), (1403, -16), (1979, -16), (2555, -16), (3131, -16), (3707, -16), (4283, -16), (4859, -16), (5435, -16), (6011, -16), (6035, -16), (6036, -16), (6037, -16), (6038, -16), (6039, -16), (6040, -16), (6041, -16), (6042, -8), (6044, 8), (6045, 12), (6046, 16), (6047, 18)]
theorem atom0137Coded_decode : atom0137 = SparsePolynomial.decodeCubic 24 atom0137Coded := by decide +kernel
theorem atom0137Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3352540847040 : Int) atom0137Coded) := by
  have h := atom0137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0138 : SparsePolynomial.Poly := [([0,10,12], -4), ([1,10,12], -8), ([2,10,12], -16), ([3,10,12], -16), ([4,10,12], -16), ([5,10,12], -16), ([6,10,12], -16), ([7,10,12], -16), ([8,10,12], -16), ([9,10,12], -16), ([10,10,12], -16), ([10,11,12], -16), ([10,12,12], -16), ([10,12,13], -16), ([10,12,14], -16), ([10,12,15], -16), ([10,12,16], -16), ([10,12,17], -16), ([10,12,18], -8), ([10,12,20], 8), ([10,12,21], 12), ([10,12,22], 16), ([10,12,23], 18)]
theorem atom0138_data : atom0138 = SparsePolynomial.monoTimes [10,12] 1 base07 := by decide +kernel
theorem eval_atom0138 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0138 = (quadB (outer g) ![1,2,2] * g 10 * g 12) := by
  rw [atom0138_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0138_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7846321654710 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138Coded : CoefficientMerge.Poly := [(252, -4), (828, -8), (1404, -16), (1980, -16), (2556, -16), (3132, -16), (3708, -16), (4284, -16), (4860, -16), (5436, -16), (6012, -16), (6036, -16), (6060, -16), (6061, -16), (6062, -16), (6063, -16), (6064, -16), (6065, -16), (6066, -8), (6068, 8), (6069, 12), (6070, 16), (6071, 18)]
theorem atom0138Coded_decode : atom0138 = SparsePolynomial.decodeCubic 24 atom0138Coded := by decide +kernel
theorem atom0138Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7846321654710 : Int) atom0138Coded) := by
  have h := atom0138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0139 : SparsePolynomial.Poly := [([0,10,13], -4), ([1,10,13], -8), ([2,10,13], -16), ([3,10,13], -16), ([4,10,13], -16), ([5,10,13], -16), ([6,10,13], -16), ([7,10,13], -16), ([8,10,13], -16), ([9,10,13], -16), ([10,10,13], -16), ([10,11,13], -16), ([10,12,13], -16), ([10,13,13], -16), ([10,13,14], -16), ([10,13,15], -16), ([10,13,16], -16), ([10,13,17], -16), ([10,13,18], -8), ([10,13,20], 8), ([10,13,21], 12), ([10,13,22], 16), ([10,13,23], 18)]
theorem atom0139_data : atom0139 = SparsePolynomial.monoTimes [10,13] 1 base07 := by decide +kernel
theorem eval_atom0139 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0139 = (quadB (outer g) ![1,2,2] * g 10 * g 13) := by
  rw [atom0139_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0139_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7558104430602 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139Coded : CoefficientMerge.Poly := [(253, -4), (829, -8), (1405, -16), (1981, -16), (2557, -16), (3133, -16), (3709, -16), (4285, -16), (4861, -16), (5437, -16), (6013, -16), (6037, -16), (6061, -16), (6085, -16), (6086, -16), (6087, -16), (6088, -16), (6089, -16), (6090, -8), (6092, 8), (6093, 12), (6094, 16), (6095, 18)]
theorem atom0139Coded_decode : atom0139 = SparsePolynomial.decodeCubic 24 atom0139Coded := by decide +kernel
theorem atom0139Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7558104430602 : Int) atom0139Coded) := by
  have h := atom0139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0140 : SparsePolynomial.Poly := [([0,10,14], -4), ([1,10,14], -8), ([2,10,14], -16), ([3,10,14], -16), ([4,10,14], -16), ([5,10,14], -16), ([6,10,14], -16), ([7,10,14], -16), ([8,10,14], -16), ([9,10,14], -16), ([10,10,14], -16), ([10,11,14], -16), ([10,12,14], -16), ([10,13,14], -16), ([10,14,14], -16), ([10,14,15], -16), ([10,14,16], -16), ([10,14,17], -16), ([10,14,18], -8), ([10,14,20], 8), ([10,14,21], 12), ([10,14,22], 16), ([10,14,23], 18)]
theorem atom0140_data : atom0140 = SparsePolynomial.monoTimes [10,14] 1 base07 := by decide +kernel
theorem eval_atom0140 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0140 = (quadB (outer g) ![1,2,2] * g 10 * g 14) := by
  rw [atom0140_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0140_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6940369358802 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140Coded : CoefficientMerge.Poly := [(254, -4), (830, -8), (1406, -16), (1982, -16), (2558, -16), (3134, -16), (3710, -16), (4286, -16), (4862, -16), (5438, -16), (6014, -16), (6038, -16), (6062, -16), (6086, -16), (6110, -16), (6111, -16), (6112, -16), (6113, -16), (6114, -8), (6116, 8), (6117, 12), (6118, 16), (6119, 18)]
theorem atom0140Coded_decode : atom0140 = SparsePolynomial.decodeCubic 24 atom0140Coded := by decide +kernel
theorem atom0140Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6940369358802 : Int) atom0140Coded) := by
  have h := atom0140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0141 : SparsePolynomial.Poly := [([0,10,15], -4), ([1,10,15], -8), ([2,10,15], -16), ([3,10,15], -16), ([4,10,15], -16), ([5,10,15], -16), ([6,10,15], -16), ([7,10,15], -16), ([8,10,15], -16), ([9,10,15], -16), ([10,10,15], -16), ([10,11,15], -16), ([10,12,15], -16), ([10,13,15], -16), ([10,14,15], -16), ([10,15,15], -16), ([10,15,16], -16), ([10,15,17], -16), ([10,15,18], -8), ([10,15,20], 8), ([10,15,21], 12), ([10,15,22], 16), ([10,15,23], 18)]
theorem atom0141_data : atom0141 = SparsePolynomial.monoTimes [10,15] 1 base07 := by decide +kernel
theorem eval_atom0141 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0141 = (quadB (outer g) ![1,2,2] * g 10 * g 15) := by
  rw [atom0141_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0141_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5398446374802 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141Coded : CoefficientMerge.Poly := [(255, -4), (831, -8), (1407, -16), (1983, -16), (2559, -16), (3135, -16), (3711, -16), (4287, -16), (4863, -16), (5439, -16), (6015, -16), (6039, -16), (6063, -16), (6087, -16), (6111, -16), (6135, -16), (6136, -16), (6137, -16), (6138, -8), (6140, 8), (6141, 12), (6142, 16), (6143, 18)]
theorem atom0141Coded_decode : atom0141 = SparsePolynomial.decodeCubic 24 atom0141Coded := by decide +kernel
theorem atom0141Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5398446374802 : Int) atom0141Coded) := by
  have h := atom0141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0142 : SparsePolynomial.Poly := [([0,10,16], -4), ([1,10,16], -8), ([2,10,16], -16), ([3,10,16], -16), ([4,10,16], -16), ([5,10,16], -16), ([6,10,16], -16), ([7,10,16], -16), ([8,10,16], -16), ([9,10,16], -16), ([10,10,16], -16), ([10,11,16], -16), ([10,12,16], -16), ([10,13,16], -16), ([10,14,16], -16), ([10,15,16], -16), ([10,16,16], -16), ([10,16,17], -16), ([10,16,18], -8), ([10,16,20], 8), ([10,16,21], 12), ([10,16,22], 16), ([10,16,23], 18)]
theorem atom0142_data : atom0142 = SparsePolynomial.monoTimes [10,16] 1 base07 := by decide +kernel
theorem eval_atom0142 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0142 = (quadB (outer g) ![1,2,2] * g 10 * g 16) := by
  rw [atom0142_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0142_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4595430281202 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142Coded : CoefficientMerge.Poly := [(256, -4), (832, -8), (1408, -16), (1984, -16), (2560, -16), (3136, -16), (3712, -16), (4288, -16), (4864, -16), (5440, -16), (6016, -16), (6040, -16), (6064, -16), (6088, -16), (6112, -16), (6136, -16), (6160, -16), (6161, -16), (6162, -8), (6164, 8), (6165, 12), (6166, 16), (6167, 18)]
theorem atom0142Coded_decode : atom0142 = SparsePolynomial.decodeCubic 24 atom0142Coded := by decide +kernel
theorem atom0142Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4595430281202 : Int) atom0142Coded) := by
  have h := atom0142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0143 : SparsePolynomial.Poly := [([0,10,17], -4), ([1,10,17], -8), ([2,10,17], -16), ([3,10,17], -16), ([4,10,17], -16), ([5,10,17], -16), ([6,10,17], -16), ([7,10,17], -16), ([8,10,17], -16), ([9,10,17], -16), ([10,10,17], -16), ([10,11,17], -16), ([10,12,17], -16), ([10,13,17], -16), ([10,14,17], -16), ([10,15,17], -16), ([10,16,17], -16), ([10,17,17], -16), ([10,17,18], -8), ([10,17,20], 8), ([10,17,21], 12), ([10,17,22], 16), ([10,17,23], 18)]
theorem atom0143_data : atom0143 = SparsePolynomial.monoTimes [10,17] 1 base07 := by decide +kernel
theorem eval_atom0143 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0143 = (quadB (outer g) ![1,2,2] * g 10 * g 17) := by
  rw [atom0143_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0143_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3171618034002 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143Coded : CoefficientMerge.Poly := [(257, -4), (833, -8), (1409, -16), (1985, -16), (2561, -16), (3137, -16), (3713, -16), (4289, -16), (4865, -16), (5441, -16), (6017, -16), (6041, -16), (6065, -16), (6089, -16), (6113, -16), (6137, -16), (6161, -16), (6185, -16), (6186, -8), (6188, 8), (6189, 12), (6190, 16), (6191, 18)]
theorem atom0143Coded_decode : atom0143 = SparsePolynomial.decodeCubic 24 atom0143Coded := by decide +kernel
theorem atom0143Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3171618034002 : Int) atom0143Coded) := by
  have h := atom0143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0144 : SparsePolynomial.Poly := [([0,10,18], -4), ([1,10,18], -8), ([2,10,18], -16), ([3,10,18], -16), ([4,10,18], -16), ([5,10,18], -16), ([6,10,18], -16), ([7,10,18], -16), ([8,10,18], -16), ([9,10,18], -16), ([10,10,18], -16), ([10,11,18], -16), ([10,12,18], -16), ([10,13,18], -16), ([10,14,18], -16), ([10,15,18], -16), ([10,16,18], -16), ([10,17,18], -16), ([10,18,18], -8), ([10,18,20], 8), ([10,18,21], 12), ([10,18,22], 16), ([10,18,23], 18)]
theorem atom0144_data : atom0144 = SparsePolynomial.monoTimes [10,18] 1 base07 := by decide +kernel
theorem eval_atom0144 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0144 = (quadB (outer g) ![1,2,2] * g 10 * g 18) := by
  rw [atom0144_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0144_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (834131593746 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 18) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144Coded : CoefficientMerge.Poly := [(258, -4), (834, -8), (1410, -16), (1986, -16), (2562, -16), (3138, -16), (3714, -16), (4290, -16), (4866, -16), (5442, -16), (6018, -16), (6042, -16), (6066, -16), (6090, -16), (6114, -16), (6138, -16), (6162, -16), (6186, -16), (6210, -8), (6212, 8), (6213, 12), (6214, 16), (6215, 18)]
theorem atom0144Coded_decode : atom0144 = SparsePolynomial.decodeCubic 24 atom0144Coded := by decide +kernel
theorem atom0144Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (834131593746 : Int) atom0144Coded) := by
  have h := atom0144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0145 : SparsePolynomial.Poly := [([0,10,19], -4), ([1,10,19], -8), ([2,10,19], -16), ([3,10,19], -16), ([4,10,19], -16), ([5,10,19], -16), ([6,10,19], -16), ([7,10,19], -16), ([8,10,19], -16), ([9,10,19], -16), ([10,10,19], -16), ([10,11,19], -16), ([10,12,19], -16), ([10,13,19], -16), ([10,14,19], -16), ([10,15,19], -16), ([10,16,19], -16), ([10,17,19], -16), ([10,18,19], -8), ([10,19,20], 8), ([10,19,21], 12), ([10,19,22], 16), ([10,19,23], 18)]
theorem atom0145_data : atom0145 = SparsePolynomial.monoTimes [10,19] 1 base07 := by decide +kernel
theorem eval_atom0145 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0145 = (quadB (outer g) ![1,2,2] * g 10 * g 19) := by
  rw [atom0145_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0145_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5723228982834 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145Coded : CoefficientMerge.Poly := [(259, -4), (835, -8), (1411, -16), (1987, -16), (2563, -16), (3139, -16), (3715, -16), (4291, -16), (4867, -16), (5443, -16), (6019, -16), (6043, -16), (6067, -16), (6091, -16), (6115, -16), (6139, -16), (6163, -16), (6187, -16), (6211, -8), (6236, 8), (6237, 12), (6238, 16), (6239, 18)]
theorem atom0145Coded_decode : atom0145 = SparsePolynomial.decodeCubic 24 atom0145Coded := by decide +kernel
theorem atom0145Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5723228982834 : Int) atom0145Coded) := by
  have h := atom0145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0146 : SparsePolynomial.Poly := [([0,10,20], -4), ([1,10,20], -8), ([2,10,20], -16), ([3,10,20], -16), ([4,10,20], -16), ([5,10,20], -16), ([6,10,20], -16), ([7,10,20], -16), ([8,10,20], -16), ([9,10,20], -16), ([10,10,20], -16), ([10,11,20], -16), ([10,12,20], -16), ([10,13,20], -16), ([10,14,20], -16), ([10,15,20], -16), ([10,16,20], -16), ([10,17,20], -16), ([10,18,20], -8), ([10,20,20], 8), ([10,20,21], 12), ([10,20,22], 16), ([10,20,23], 18)]
theorem atom0146_data : atom0146 = SparsePolynomial.monoTimes [10,20] 1 base07 := by decide +kernel
theorem eval_atom0146 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0146 = (quadB (outer g) ![1,2,2] * g 10 * g 20) := by
  rw [atom0146_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0146_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1809713968722 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146Coded : CoefficientMerge.Poly := [(260, -4), (836, -8), (1412, -16), (1988, -16), (2564, -16), (3140, -16), (3716, -16), (4292, -16), (4868, -16), (5444, -16), (6020, -16), (6044, -16), (6068, -16), (6092, -16), (6116, -16), (6140, -16), (6164, -16), (6188, -16), (6212, -8), (6260, 8), (6261, 12), (6262, 16), (6263, 18)]
theorem atom0146Coded_decode : atom0146 = SparsePolynomial.decodeCubic 24 atom0146Coded := by decide +kernel
theorem atom0146Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1809713968722 : Int) atom0146Coded) := by
  have h := atom0146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0147 : SparsePolynomial.Poly := [([0,10,21], -4), ([1,10,21], -8), ([2,10,21], -16), ([3,10,21], -16), ([4,10,21], -16), ([5,10,21], -16), ([6,10,21], -16), ([7,10,21], -16), ([8,10,21], -16), ([9,10,21], -16), ([10,10,21], -16), ([10,11,21], -16), ([10,12,21], -16), ([10,13,21], -16), ([10,14,21], -16), ([10,15,21], -16), ([10,16,21], -16), ([10,17,21], -16), ([10,18,21], -8), ([10,20,21], 8), ([10,21,21], 12), ([10,21,22], 16), ([10,21,23], 18)]
theorem atom0147_data : atom0147 = SparsePolynomial.monoTimes [10,21] 1 base07 := by decide +kernel
theorem eval_atom0147 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0147 = (quadB (outer g) ![1,2,2] * g 10 * g 21) := by
  rw [atom0147_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0147_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8575299701298 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147Coded : CoefficientMerge.Poly := [(261, -4), (837, -8), (1413, -16), (1989, -16), (2565, -16), (3141, -16), (3717, -16), (4293, -16), (4869, -16), (5445, -16), (6021, -16), (6045, -16), (6069, -16), (6093, -16), (6117, -16), (6141, -16), (6165, -16), (6189, -16), (6213, -8), (6261, 8), (6285, 12), (6286, 16), (6287, 18)]
theorem atom0147Coded_decode : atom0147 = SparsePolynomial.decodeCubic 24 atom0147Coded := by decide +kernel
theorem atom0147Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8575299701298 : Int) atom0147Coded) := by
  have h := atom0147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0148 : SparsePolynomial.Poly := [([0,10,22], -4), ([1,10,22], -8), ([2,10,22], -16), ([3,10,22], -16), ([4,10,22], -16), ([5,10,22], -16), ([6,10,22], -16), ([7,10,22], -16), ([8,10,22], -16), ([9,10,22], -16), ([10,10,22], -16), ([10,11,22], -16), ([10,12,22], -16), ([10,13,22], -16), ([10,14,22], -16), ([10,15,22], -16), ([10,16,22], -16), ([10,17,22], -16), ([10,18,22], -8), ([10,20,22], 8), ([10,21,22], 12), ([10,22,22], 16), ([10,22,23], 18)]
theorem atom0148_data : atom0148 = SparsePolynomial.monoTimes [10,22] 1 base07 := by decide +kernel
theorem eval_atom0148 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0148 = (quadB (outer g) ![1,2,2] * g 10 * g 22) := by
  rw [atom0148_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0148_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10861157920800 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148Coded : CoefficientMerge.Poly := [(262, -4), (838, -8), (1414, -16), (1990, -16), (2566, -16), (3142, -16), (3718, -16), (4294, -16), (4870, -16), (5446, -16), (6022, -16), (6046, -16), (6070, -16), (6094, -16), (6118, -16), (6142, -16), (6166, -16), (6190, -16), (6214, -8), (6262, 8), (6286, 12), (6310, 16), (6311, 18)]
theorem atom0148Coded_decode : atom0148 = SparsePolynomial.decodeCubic 24 atom0148Coded := by decide +kernel
theorem atom0148Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10861157920800 : Int) atom0148Coded) := by
  have h := atom0148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0149 : SparsePolynomial.Poly := [([0,10,23], -4), ([1,10,23], -8), ([2,10,23], -16), ([3,10,23], -16), ([4,10,23], -16), ([5,10,23], -16), ([6,10,23], -16), ([7,10,23], -16), ([8,10,23], -16), ([9,10,23], -16), ([10,10,23], -16), ([10,11,23], -16), ([10,12,23], -16), ([10,13,23], -16), ([10,14,23], -16), ([10,15,23], -16), ([10,16,23], -16), ([10,17,23], -16), ([10,18,23], -8), ([10,20,23], 8), ([10,21,23], 12), ([10,22,23], 16), ([10,23,23], 18)]
theorem atom0149_data : atom0149 = SparsePolynomial.monoTimes [10,23] 1 base07 := by decide +kernel
theorem eval_atom0149 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0149 = (quadB (outer g) ![1,2,2] * g 10 * g 23) := by
  rw [atom0149_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0149_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14235738281568 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149Coded : CoefficientMerge.Poly := [(263, -4), (839, -8), (1415, -16), (1991, -16), (2567, -16), (3143, -16), (3719, -16), (4295, -16), (4871, -16), (5447, -16), (6023, -16), (6047, -16), (6071, -16), (6095, -16), (6119, -16), (6143, -16), (6167, -16), (6191, -16), (6215, -8), (6263, 8), (6287, 12), (6311, 16), (6335, 18)]
theorem atom0149Coded_decode : atom0149 = SparsePolynomial.decodeCubic 24 atom0149Coded := by decide +kernel
theorem atom0149Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (14235738281568 : Int) atom0149Coded) := by
  have h := atom0149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0150 : SparsePolynomial.Poly := [([0,11,12], -4), ([1,11,12], -8), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -16), ([11,12,13], -16), ([11,12,14], -16), ([11,12,15], -16), ([11,12,16], -16), ([11,12,17], -16), ([11,12,18], -8), ([11,12,20], 8), ([11,12,21], 12), ([11,12,22], 16), ([11,12,23], 18)]
theorem atom0150_data : atom0150 = SparsePolynomial.monoTimes [11,12] 1 base07 := by decide +kernel
theorem eval_atom0150 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0150 = (quadB (outer g) ![1,2,2] * g 11 * g 12) := by
  rw [atom0150_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0150_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3352540847040 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150Coded : CoefficientMerge.Poly := [(276, -4), (852, -8), (1428, -16), (2004, -16), (2580, -16), (3156, -16), (3732, -16), (4308, -16), (4884, -16), (5460, -16), (6036, -16), (6612, -16), (6636, -16), (6637, -16), (6638, -16), (6639, -16), (6640, -16), (6641, -16), (6642, -8), (6644, 8), (6645, 12), (6646, 16), (6647, 18)]
theorem atom0150Coded_decode : atom0150 = SparsePolynomial.decodeCubic 24 atom0150Coded := by decide +kernel
theorem atom0150Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3352540847040 : Int) atom0150Coded) := by
  have h := atom0150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0151 : SparsePolynomial.Poly := [([0,11,13], -4), ([1,11,13], -8), ([2,11,13], -16), ([3,11,13], -16), ([4,11,13], -16), ([5,11,13], -16), ([6,11,13], -16), ([7,11,13], -16), ([8,11,13], -16), ([9,11,13], -16), ([10,11,13], -16), ([11,11,13], -16), ([11,12,13], -16), ([11,13,13], -16), ([11,13,14], -16), ([11,13,15], -16), ([11,13,16], -16), ([11,13,17], -16), ([11,13,18], -8), ([11,13,20], 8), ([11,13,21], 12), ([11,13,22], 16), ([11,13,23], 18)]
theorem atom0151_data : atom0151 = SparsePolynomial.monoTimes [11,13] 1 base07 := by decide +kernel
theorem eval_atom0151 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0151 = (quadB (outer g) ![1,2,2] * g 11 * g 13) := by
  rw [atom0151_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0151_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7219663757460 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151Coded : CoefficientMerge.Poly := [(277, -4), (853, -8), (1429, -16), (2005, -16), (2581, -16), (3157, -16), (3733, -16), (4309, -16), (4885, -16), (5461, -16), (6037, -16), (6613, -16), (6637, -16), (6661, -16), (6662, -16), (6663, -16), (6664, -16), (6665, -16), (6666, -8), (6668, 8), (6669, 12), (6670, 16), (6671, 18)]
theorem atom0151Coded_decode : atom0151 = SparsePolynomial.decodeCubic 24 atom0151Coded := by decide +kernel
theorem atom0151Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7219663757460 : Int) atom0151Coded) := by
  have h := atom0151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0152 : SparsePolynomial.Poly := [([0,11,14], -4), ([1,11,14], -8), ([2,11,14], -16), ([3,11,14], -16), ([4,11,14], -16), ([5,11,14], -16), ([6,11,14], -16), ([7,11,14], -16), ([8,11,14], -16), ([9,11,14], -16), ([10,11,14], -16), ([11,11,14], -16), ([11,12,14], -16), ([11,13,14], -16), ([11,14,14], -16), ([11,14,15], -16), ([11,14,16], -16), ([11,14,17], -16), ([11,14,18], -8), ([11,14,20], 8), ([11,14,21], 12), ([11,14,22], 16), ([11,14,23], 18)]
theorem atom0152_data : atom0152 = SparsePolynomial.monoTimes [11,14] 1 base07 := by decide +kernel
theorem eval_atom0152 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0152 = (quadB (outer g) ![1,2,2] * g 11 * g 14) := by
  rw [atom0152_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0152_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7576464321756 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152Coded : CoefficientMerge.Poly := [(278, -4), (854, -8), (1430, -16), (2006, -16), (2582, -16), (3158, -16), (3734, -16), (4310, -16), (4886, -16), (5462, -16), (6038, -16), (6614, -16), (6638, -16), (6662, -16), (6686, -16), (6687, -16), (6688, -16), (6689, -16), (6690, -8), (6692, 8), (6693, 12), (6694, 16), (6695, 18)]
theorem atom0152Coded_decode : atom0152 = SparsePolynomial.decodeCubic 24 atom0152Coded := by decide +kernel
theorem atom0152Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7576464321756 : Int) atom0152Coded) := by
  have h := atom0152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0153 : SparsePolynomial.Poly := [([0,11,15], -4), ([1,11,15], -8), ([2,11,15], -16), ([3,11,15], -16), ([4,11,15], -16), ([5,11,15], -16), ([6,11,15], -16), ([7,11,15], -16), ([8,11,15], -16), ([9,11,15], -16), ([10,11,15], -16), ([11,11,15], -16), ([11,12,15], -16), ([11,13,15], -16), ([11,14,15], -16), ([11,15,15], -16), ([11,15,16], -16), ([11,15,17], -16), ([11,15,18], -8), ([11,15,20], 8), ([11,15,21], 12), ([11,15,22], 16), ([11,15,23], 18)]
theorem atom0153_data : atom0153 = SparsePolynomial.monoTimes [11,15] 1 base07 := by decide +kernel
theorem eval_atom0153 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0153 = (quadB (outer g) ![1,2,2] * g 11 * g 15) := by
  rw [atom0153_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0153_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5332883827356 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153Coded : CoefficientMerge.Poly := [(279, -4), (855, -8), (1431, -16), (2007, -16), (2583, -16), (3159, -16), (3735, -16), (4311, -16), (4887, -16), (5463, -16), (6039, -16), (6615, -16), (6639, -16), (6663, -16), (6687, -16), (6711, -16), (6712, -16), (6713, -16), (6714, -8), (6716, 8), (6717, 12), (6718, 16), (6719, 18)]
theorem atom0153Coded_decode : atom0153 = SparsePolynomial.decodeCubic 24 atom0153Coded := by decide +kernel
theorem atom0153Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5332883827356 : Int) atom0153Coded) := by
  have h := atom0153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0154 : SparsePolynomial.Poly := [([0,11,16], -4), ([1,11,16], -8), ([2,11,16], -16), ([3,11,16], -16), ([4,11,16], -16), ([5,11,16], -16), ([6,11,16], -16), ([7,11,16], -16), ([8,11,16], -16), ([9,11,16], -16), ([10,11,16], -16), ([11,11,16], -16), ([11,12,16], -16), ([11,13,16], -16), ([11,14,16], -16), ([11,15,16], -16), ([11,16,16], -16), ([11,16,17], -16), ([11,16,18], -8), ([11,16,20], 8), ([11,16,21], 12), ([11,16,22], 16), ([11,16,23], 18)]
theorem atom0154_data : atom0154 = SparsePolynomial.monoTimes [11,16] 1 base07 := by decide +kernel
theorem eval_atom0154 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0154 = (quadB (outer g) ![1,2,2] * g 11 * g 16) := by
  rw [atom0154_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0154_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4020900259356 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154Coded : CoefficientMerge.Poly := [(280, -4), (856, -8), (1432, -16), (2008, -16), (2584, -16), (3160, -16), (3736, -16), (4312, -16), (4888, -16), (5464, -16), (6040, -16), (6616, -16), (6640, -16), (6664, -16), (6688, -16), (6712, -16), (6736, -16), (6737, -16), (6738, -8), (6740, 8), (6741, 12), (6742, 16), (6743, 18)]
theorem atom0154Coded_decode : atom0154 = SparsePolynomial.decodeCubic 24 atom0154Coded := by decide +kernel
theorem atom0154Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4020900259356 : Int) atom0154Coded) := by
  have h := atom0154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0155 : SparsePolynomial.Poly := [([0,11,17], -4), ([1,11,17], -8), ([2,11,17], -16), ([3,11,17], -16), ([4,11,17], -16), ([5,11,17], -16), ([6,11,17], -16), ([7,11,17], -16), ([8,11,17], -16), ([9,11,17], -16), ([10,11,17], -16), ([11,11,17], -16), ([11,12,17], -16), ([11,13,17], -16), ([11,14,17], -16), ([11,15,17], -16), ([11,16,17], -16), ([11,17,17], -16), ([11,17,18], -8), ([11,17,20], 8), ([11,17,21], 12), ([11,17,22], 16), ([11,17,23], 18)]
theorem atom0155_data : atom0155 = SparsePolynomial.monoTimes [11,17] 1 base07 := by decide +kernel
theorem eval_atom0155 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0155 = (quadB (outer g) ![1,2,2] * g 11 * g 17) := by
  rw [atom0155_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0155_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2088120537756 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155Coded : CoefficientMerge.Poly := [(281, -4), (857, -8), (1433, -16), (2009, -16), (2585, -16), (3161, -16), (3737, -16), (4313, -16), (4889, -16), (5465, -16), (6041, -16), (6617, -16), (6641, -16), (6665, -16), (6689, -16), (6713, -16), (6737, -16), (6761, -16), (6762, -8), (6764, 8), (6765, 12), (6766, 16), (6767, 18)]
theorem atom0155Coded_decode : atom0155 = SparsePolynomial.decodeCubic 24 atom0155Coded := by decide +kernel
theorem atom0155Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2088120537756 : Int) atom0155Coded) := by
  have h := atom0155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0156 : SparsePolynomial.Poly := [([0,11,19], -4), ([1,11,19], -8), ([2,11,19], -16), ([3,11,19], -16), ([4,11,19], -16), ([5,11,19], -16), ([6,11,19], -16), ([7,11,19], -16), ([8,11,19], -16), ([9,11,19], -16), ([10,11,19], -16), ([11,11,19], -16), ([11,12,19], -16), ([11,13,19], -16), ([11,14,19], -16), ([11,15,19], -16), ([11,16,19], -16), ([11,17,19], -16), ([11,18,19], -8), ([11,19,20], 8), ([11,19,21], 12), ([11,19,22], 16), ([11,19,23], 18)]
theorem atom0156_data : atom0156 = SparsePolynomial.monoTimes [11,19] 1 base07 := by decide +kernel
theorem eval_atom0156 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0156 = (quadB (outer g) ![1,2,2] * g 11 * g 19) := by
  rw [atom0156_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0156_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3716406396252 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156Coded : CoefficientMerge.Poly := [(283, -4), (859, -8), (1435, -16), (2011, -16), (2587, -16), (3163, -16), (3739, -16), (4315, -16), (4891, -16), (5467, -16), (6043, -16), (6619, -16), (6643, -16), (6667, -16), (6691, -16), (6715, -16), (6739, -16), (6763, -16), (6787, -8), (6812, 8), (6813, 12), (6814, 16), (6815, 18)]
theorem atom0156Coded_decode : atom0156 = SparsePolynomial.decodeCubic 24 atom0156Coded := by decide +kernel
theorem atom0156Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3716406396252 : Int) atom0156Coded) := by
  have h := atom0156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0157 : SparsePolynomial.Poly := [([0,11,21], -4), ([1,11,21], -8), ([2,11,21], -16), ([3,11,21], -16), ([4,11,21], -16), ([5,11,21], -16), ([6,11,21], -16), ([7,11,21], -16), ([8,11,21], -16), ([9,11,21], -16), ([10,11,21], -16), ([11,11,21], -16), ([11,12,21], -16), ([11,13,21], -16), ([11,14,21], -16), ([11,15,21], -16), ([11,16,21], -16), ([11,17,21], -16), ([11,18,21], -8), ([11,20,21], 8), ([11,21,21], 12), ([11,21,22], 16), ([11,21,23], 18)]
theorem atom0157_data : atom0157 = SparsePolynomial.monoTimes [11,21] 1 base07 := by decide +kernel
theorem eval_atom0157 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0157 = (quadB (outer g) ![1,2,2] * g 11 * g 21) := by
  rw [atom0157_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0157_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5739761882844 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157Coded : CoefficientMerge.Poly := [(285, -4), (861, -8), (1437, -16), (2013, -16), (2589, -16), (3165, -16), (3741, -16), (4317, -16), (4893, -16), (5469, -16), (6045, -16), (6621, -16), (6645, -16), (6669, -16), (6693, -16), (6717, -16), (6741, -16), (6765, -16), (6789, -8), (6837, 8), (6861, 12), (6862, 16), (6863, 18)]
theorem atom0157Coded_decode : atom0157 = SparsePolynomial.decodeCubic 24 atom0157Coded := by decide +kernel
theorem atom0157Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5739761882844 : Int) atom0157Coded) := by
  have h := atom0157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0158 : SparsePolynomial.Poly := [([0,11,22], -4), ([1,11,22], -8), ([2,11,22], -16), ([3,11,22], -16), ([4,11,22], -16), ([5,11,22], -16), ([6,11,22], -16), ([7,11,22], -16), ([8,11,22], -16), ([9,11,22], -16), ([10,11,22], -16), ([11,11,22], -16), ([11,12,22], -16), ([11,13,22], -16), ([11,14,22], -16), ([11,15,22], -16), ([11,16,22], -16), ([11,17,22], -16), ([11,18,22], -8), ([11,20,22], 8), ([11,21,22], 12), ([11,22,22], 16), ([11,22,23], 18)]
theorem atom0158_data : atom0158 = SparsePolynomial.monoTimes [11,22] 1 base07 := by decide +kernel
theorem eval_atom0158 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0158 = (quadB (outer g) ![1,2,2] * g 11 * g 22) := by
  rw [atom0158_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0158_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16558454906400 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158Coded : CoefficientMerge.Poly := [(286, -4), (862, -8), (1438, -16), (2014, -16), (2590, -16), (3166, -16), (3742, -16), (4318, -16), (4894, -16), (5470, -16), (6046, -16), (6622, -16), (6646, -16), (6670, -16), (6694, -16), (6718, -16), (6742, -16), (6766, -16), (6790, -8), (6838, 8), (6862, 12), (6886, 16), (6887, 18)]
theorem atom0158Coded_decode : atom0158 = SparsePolynomial.decodeCubic 24 atom0158Coded := by decide +kernel
theorem atom0158Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16558454906400 : Int) atom0158Coded) := by
  have h := atom0158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0159 : SparsePolynomial.Poly := [([0,11,23], -4), ([1,11,23], -8), ([2,11,23], -16), ([3,11,23], -16), ([4,11,23], -16), ([5,11,23], -16), ([6,11,23], -16), ([7,11,23], -16), ([8,11,23], -16), ([9,11,23], -16), ([10,11,23], -16), ([11,11,23], -16), ([11,12,23], -16), ([11,13,23], -16), ([11,14,23], -16), ([11,15,23], -16), ([11,16,23], -16), ([11,17,23], -16), ([11,18,23], -8), ([11,20,23], 8), ([11,21,23], 12), ([11,22,23], 16), ([11,23,23], 18)]
theorem atom0159_data : atom0159 = SparsePolynomial.monoTimes [11,23] 1 base07 := by decide +kernel
theorem eval_atom0159 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0159 = (quadB (outer g) ![1,2,2] * g 11 * g 23) := by
  rw [atom0159_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0159_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14660222436288 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159Coded : CoefficientMerge.Poly := [(287, -4), (863, -8), (1439, -16), (2015, -16), (2591, -16), (3167, -16), (3743, -16), (4319, -16), (4895, -16), (5471, -16), (6047, -16), (6623, -16), (6647, -16), (6671, -16), (6695, -16), (6719, -16), (6743, -16), (6767, -16), (6791, -8), (6839, 8), (6863, 12), (6887, 16), (6911, 18)]
theorem atom0159Coded_decode : atom0159 = SparsePolynomial.decodeCubic 24 atom0159Coded := by decide +kernel
theorem atom0159Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (14660222436288 : Int) atom0159Coded) := by
  have h := atom0159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0160 : SparsePolynomial.Poly := [([0,12,13], -4), ([1,12,13], -8), ([2,12,13], -16), ([3,12,13], -16), ([4,12,13], -16), ([5,12,13], -16), ([6,12,13], -16), ([7,12,13], -16), ([8,12,13], -16), ([9,12,13], -16), ([10,12,13], -16), ([11,12,13], -16), ([12,12,13], -16), ([12,13,13], -16), ([12,13,14], -16), ([12,13,15], -16), ([12,13,16], -16), ([12,13,17], -16), ([12,13,18], -8), ([12,13,20], 8), ([12,13,21], 12), ([12,13,22], 16), ([12,13,23], 18)]
theorem atom0160_data : atom0160 = SparsePolynomial.monoTimes [12,13] 1 base07 := by decide +kernel
theorem eval_atom0160 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0160 = (quadB (outer g) ![1,2,2] * g 12 * g 13) := by
  rw [atom0160_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0160_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3352540847040 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160Coded : CoefficientMerge.Poly := [(301, -4), (877, -8), (1453, -16), (2029, -16), (2605, -16), (3181, -16), (3757, -16), (4333, -16), (4909, -16), (5485, -16), (6061, -16), (6637, -16), (7213, -16), (7237, -16), (7238, -16), (7239, -16), (7240, -16), (7241, -16), (7242, -8), (7244, 8), (7245, 12), (7246, 16), (7247, 18)]
theorem atom0160Coded_decode : atom0160 = SparsePolynomial.decodeCubic 24 atom0160Coded := by decide +kernel
theorem atom0160Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3352540847040 : Int) atom0160Coded) := by
  have h := atom0160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0161 : SparsePolynomial.Poly := [([0,12,14], -4), ([1,12,14], -8), ([2,12,14], -16), ([3,12,14], -16), ([4,12,14], -16), ([5,12,14], -16), ([6,12,14], -16), ([7,12,14], -16), ([8,12,14], -16), ([9,12,14], -16), ([10,12,14], -16), ([11,12,14], -16), ([12,12,14], -16), ([12,13,14], -16), ([12,14,14], -16), ([12,14,15], -16), ([12,14,16], -16), ([12,14,17], -16), ([12,14,18], -8), ([12,14,20], 8), ([12,14,21], 12), ([12,14,22], 16), ([12,14,23], 18)]
theorem atom0161_data : atom0161 = SparsePolynomial.monoTimes [12,14] 1 base07 := by decide +kernel
theorem eval_atom0161 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0161 = (quadB (outer g) ![1,2,2] * g 12 * g 14) := by
  rw [atom0161_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0161_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7508200475160 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161Coded : CoefficientMerge.Poly := [(302, -4), (878, -8), (1454, -16), (2030, -16), (2606, -16), (3182, -16), (3758, -16), (4334, -16), (4910, -16), (5486, -16), (6062, -16), (6638, -16), (7214, -16), (7238, -16), (7262, -16), (7263, -16), (7264, -16), (7265, -16), (7266, -8), (7268, 8), (7269, 12), (7270, 16), (7271, 18)]
theorem atom0161Coded_decode : atom0161 = SparsePolynomial.decodeCubic 24 atom0161Coded := by decide +kernel
theorem atom0161Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7508200475160 : Int) atom0161Coded) := by
  have h := atom0161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0162 : SparsePolynomial.Poly := [([0,12,15], -4), ([1,12,15], -8), ([2,12,15], -16), ([3,12,15], -16), ([4,12,15], -16), ([5,12,15], -16), ([6,12,15], -16), ([7,12,15], -16), ([8,12,15], -16), ([9,12,15], -16), ([10,12,15], -16), ([11,12,15], -16), ([12,12,15], -16), ([12,13,15], -16), ([12,14,15], -16), ([12,15,15], -16), ([12,15,16], -16), ([12,15,17], -16), ([12,15,18], -8), ([12,15,20], 8), ([12,15,21], 12), ([12,15,22], 16), ([12,15,23], 18)]
theorem atom0162_data : atom0162 = SparsePolynomial.monoTimes [12,15] 1 base07 := by decide +kernel
theorem eval_atom0162 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0162 = (quadB (outer g) ![1,2,2] * g 12 * g 15) := by
  rw [atom0162_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0162_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5447135729736 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162Coded : CoefficientMerge.Poly := [(303, -4), (879, -8), (1455, -16), (2031, -16), (2607, -16), (3183, -16), (3759, -16), (4335, -16), (4911, -16), (5487, -16), (6063, -16), (6639, -16), (7215, -16), (7239, -16), (7263, -16), (7287, -16), (7288, -16), (7289, -16), (7290, -8), (7292, 8), (7293, 12), (7294, 16), (7295, 18)]
theorem atom0162Coded_decode : atom0162 = SparsePolynomial.decodeCubic 24 atom0162Coded := by decide +kernel
theorem atom0162Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5447135729736 : Int) atom0162Coded) := by
  have h := atom0162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0163 : SparsePolynomial.Poly := [([0,12,16], -4), ([1,12,16], -8), ([2,12,16], -16), ([3,12,16], -16), ([4,12,16], -16), ([5,12,16], -16), ([6,12,16], -16), ([7,12,16], -16), ([8,12,16], -16), ([9,12,16], -16), ([10,12,16], -16), ([11,12,16], -16), ([12,12,16], -16), ([12,13,16], -16), ([12,14,16], -16), ([12,15,16], -16), ([12,16,16], -16), ([12,16,17], -16), ([12,16,18], -8), ([12,16,20], 8), ([12,16,21], 12), ([12,16,22], 16), ([12,16,23], 18)]
theorem atom0163_data : atom0163 = SparsePolynomial.monoTimes [12,16] 1 base07 := by decide +kernel
theorem eval_atom0163 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0163 = (quadB (outer g) ![1,2,2] * g 12 * g 16) := by
  rw [atom0163_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0163_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3562397640936 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163Coded : CoefficientMerge.Poly := [(304, -4), (880, -8), (1456, -16), (2032, -16), (2608, -16), (3184, -16), (3760, -16), (4336, -16), (4912, -16), (5488, -16), (6064, -16), (6640, -16), (7216, -16), (7240, -16), (7264, -16), (7288, -16), (7312, -16), (7313, -16), (7314, -8), (7316, 8), (7317, 12), (7318, 16), (7319, 18)]
theorem atom0163Coded_decode : atom0163 = SparsePolynomial.decodeCubic 24 atom0163Coded := by decide +kernel
theorem atom0163Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3562397640936 : Int) atom0163Coded) := by
  have h := atom0163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0164 : SparsePolynomial.Poly := [([0,12,17], -4), ([1,12,17], -8), ([2,12,17], -16), ([3,12,17], -16), ([4,12,17], -16), ([5,12,17], -16), ([6,12,17], -16), ([7,12,17], -16), ([8,12,17], -16), ([9,12,17], -16), ([10,12,17], -16), ([11,12,17], -16), ([12,12,17], -16), ([12,13,17], -16), ([12,14,17], -16), ([12,15,17], -16), ([12,16,17], -16), ([12,17,17], -16), ([12,17,18], -8), ([12,17,20], 8), ([12,17,21], 12), ([12,17,22], 16), ([12,17,23], 18)]
theorem atom0164_data : atom0164 = SparsePolynomial.monoTimes [12,17] 1 base07 := by decide +kernel
theorem eval_atom0164 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0164 = (quadB (outer g) ![1,2,2] * g 12 * g 17) := by
  rw [atom0164_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0164_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1056863398536 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164Coded : CoefficientMerge.Poly := [(305, -4), (881, -8), (1457, -16), (2033, -16), (2609, -16), (3185, -16), (3761, -16), (4337, -16), (4913, -16), (5489, -16), (6065, -16), (6641, -16), (7217, -16), (7241, -16), (7265, -16), (7289, -16), (7313, -16), (7337, -16), (7338, -8), (7340, 8), (7341, 12), (7342, 16), (7343, 18)]
theorem atom0164Coded_decode : atom0164 = SparsePolynomial.decodeCubic 24 atom0164Coded := by decide +kernel
theorem atom0164Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1056863398536 : Int) atom0164Coded) := by
  have h := atom0164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0165 : SparsePolynomial.Poly := [([0,12,19], -4), ([1,12,19], -8), ([2,12,19], -16), ([3,12,19], -16), ([4,12,19], -16), ([5,12,19], -16), ([6,12,19], -16), ([7,12,19], -16), ([8,12,19], -16), ([9,12,19], -16), ([10,12,19], -16), ([11,12,19], -16), ([12,12,19], -16), ([12,13,19], -16), ([12,14,19], -16), ([12,15,19], -16), ([12,16,19], -16), ([12,17,19], -16), ([12,18,19], -8), ([12,19,20], 8), ([12,19,21], 12), ([12,19,22], 16), ([12,19,23], 18)]
theorem atom0165_data : atom0165 = SparsePolynomial.monoTimes [12,19] 1 base07 := by decide +kernel
theorem eval_atom0165 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0165 = (quadB (outer g) ![1,2,2] * g 12 * g 19) := by
  rw [atom0165_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0165_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (962367445512 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165Coded : CoefficientMerge.Poly := [(307, -4), (883, -8), (1459, -16), (2035, -16), (2611, -16), (3187, -16), (3763, -16), (4339, -16), (4915, -16), (5491, -16), (6067, -16), (6643, -16), (7219, -16), (7243, -16), (7267, -16), (7291, -16), (7315, -16), (7339, -16), (7363, -8), (7388, 8), (7389, 12), (7390, 16), (7391, 18)]
theorem atom0165Coded_decode : atom0165 = SparsePolynomial.decodeCubic 24 atom0165Coded := by decide +kernel
theorem atom0165Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (962367445512 : Int) atom0165Coded) := by
  have h := atom0165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0166 : SparsePolynomial.Poly := [([0,12,21], -4), ([1,12,21], -8), ([2,12,21], -16), ([3,12,21], -16), ([4,12,21], -16), ([5,12,21], -16), ([6,12,21], -16), ([7,12,21], -16), ([8,12,21], -16), ([9,12,21], -16), ([10,12,21], -16), ([11,12,21], -16), ([12,12,21], -16), ([12,13,21], -16), ([12,14,21], -16), ([12,15,21], -16), ([12,16,21], -16), ([12,17,21], -16), ([12,18,21], -8), ([12,20,21], 8), ([12,21,21], 12), ([12,21,22], 16), ([12,21,23], 18)]
theorem atom0166_data : atom0166 = SparsePolynomial.monoTimes [12,21] 1 base07 := by decide +kernel
theorem eval_atom0166 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0166 = (quadB (outer g) ![1,2,2] * g 12 * g 21) := by
  rw [atom0166_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0166_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (685668350664 : Int) atom0166) := by
  rw [SparsePolynomial.eval_scale, eval_atom0166]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0166Coded : CoefficientMerge.Poly := [(309, -4), (885, -8), (1461, -16), (2037, -16), (2613, -16), (3189, -16), (3765, -16), (4341, -16), (4917, -16), (5493, -16), (6069, -16), (6645, -16), (7221, -16), (7245, -16), (7269, -16), (7293, -16), (7317, -16), (7341, -16), (7365, -8), (7413, 8), (7437, 12), (7438, 16), (7439, 18)]
theorem atom0166Coded_decode : atom0166 = SparsePolynomial.decodeCubic 24 atom0166Coded := by decide +kernel
theorem atom0166Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (685668350664 : Int) atom0166Coded) := by
  have h := atom0166_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0166Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0167 : SparsePolynomial.Poly := [([0,12,22], -4), ([1,12,22], -8), ([2,12,22], -16), ([3,12,22], -16), ([4,12,22], -16), ([5,12,22], -16), ([6,12,22], -16), ([7,12,22], -16), ([8,12,22], -16), ([9,12,22], -16), ([10,12,22], -16), ([11,12,22], -16), ([12,12,22], -16), ([12,13,22], -16), ([12,14,22], -16), ([12,15,22], -16), ([12,16,22], -16), ([12,17,22], -16), ([12,18,22], -8), ([12,20,22], 8), ([12,21,22], 12), ([12,22,22], 16), ([12,22,23], 18)]
theorem atom0167_data : atom0167 = SparsePolynomial.monoTimes [12,22] 1 base07 := by decide +kernel
theorem eval_atom0167 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0167 = (quadB (outer g) ![1,2,2] * g 12 * g 22) := by
  rw [atom0167_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0167_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13690255714560 : Int) atom0167) := by
  rw [SparsePolynomial.eval_scale, eval_atom0167]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0167Coded : CoefficientMerge.Poly := [(310, -4), (886, -8), (1462, -16), (2038, -16), (2614, -16), (3190, -16), (3766, -16), (4342, -16), (4918, -16), (5494, -16), (6070, -16), (6646, -16), (7222, -16), (7246, -16), (7270, -16), (7294, -16), (7318, -16), (7342, -16), (7366, -8), (7414, 8), (7438, 12), (7462, 16), (7463, 18)]
theorem atom0167Coded_decode : atom0167 = SparsePolynomial.decodeCubic 24 atom0167Coded := by decide +kernel
theorem atom0167Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (13690255714560 : Int) atom0167Coded) := by
  have h := atom0167_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0167Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0168 : SparsePolynomial.Poly := [([0,12,23], -4), ([1,12,23], -8), ([2,12,23], -16), ([3,12,23], -16), ([4,12,23], -16), ([5,12,23], -16), ([6,12,23], -16), ([7,12,23], -16), ([8,12,23], -16), ([9,12,23], -16), ([10,12,23], -16), ([11,12,23], -16), ([12,12,23], -16), ([12,13,23], -16), ([12,14,23], -16), ([12,15,23], -16), ([12,16,23], -16), ([12,17,23], -16), ([12,18,23], -8), ([12,20,23], 8), ([12,21,23], 12), ([12,22,23], 16), ([12,23,23], 18)]
theorem atom0168_data : atom0168 = SparsePolynomial.monoTimes [12,23] 1 base07 := by decide +kernel
theorem eval_atom0168 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0168 = (quadB (outer g) ![1,2,2] * g 12 * g 23) := by
  rw [atom0168_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0168_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10411473587328 : Int) atom0168) := by
  rw [SparsePolynomial.eval_scale, eval_atom0168]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0168Coded : CoefficientMerge.Poly := [(311, -4), (887, -8), (1463, -16), (2039, -16), (2615, -16), (3191, -16), (3767, -16), (4343, -16), (4919, -16), (5495, -16), (6071, -16), (6647, -16), (7223, -16), (7247, -16), (7271, -16), (7295, -16), (7319, -16), (7343, -16), (7367, -8), (7415, 8), (7439, 12), (7463, 16), (7487, 18)]
theorem atom0168Coded_decode : atom0168 = SparsePolynomial.decodeCubic 24 atom0168Coded := by decide +kernel
theorem atom0168Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10411473587328 : Int) atom0168Coded) := by
  have h := atom0168_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0168Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0169 : SparsePolynomial.Poly := [([0,13,14], -4), ([1,13,14], -8), ([2,13,14], -16), ([3,13,14], -16), ([4,13,14], -16), ([5,13,14], -16), ([6,13,14], -16), ([7,13,14], -16), ([8,13,14], -16), ([9,13,14], -16), ([10,13,14], -16), ([11,13,14], -16), ([12,13,14], -16), ([13,13,14], -16), ([13,14,14], -16), ([13,14,15], -16), ([13,14,16], -16), ([13,14,17], -16), ([13,14,18], -8), ([13,14,20], 8), ([13,14,21], 12), ([13,14,22], 16), ([13,14,23], 18)]
theorem atom0169_data : atom0169 = SparsePolynomial.monoTimes [13,14] 1 base07 := by decide +kernel
theorem eval_atom0169 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0169 = (quadB (outer g) ![1,2,2] * g 13 * g 14) := by
  rw [atom0169_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0169_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3352540847040 : Int) atom0169) := by
  rw [SparsePolynomial.eval_scale, eval_atom0169]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0169Coded : CoefficientMerge.Poly := [(326, -4), (902, -8), (1478, -16), (2054, -16), (2630, -16), (3206, -16), (3782, -16), (4358, -16), (4934, -16), (5510, -16), (6086, -16), (6662, -16), (7238, -16), (7814, -16), (7838, -16), (7839, -16), (7840, -16), (7841, -16), (7842, -8), (7844, 8), (7845, 12), (7846, 16), (7847, 18)]
theorem atom0169Coded_decode : atom0169 = SparsePolynomial.decodeCubic 24 atom0169Coded := by decide +kernel
theorem atom0169Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3352540847040 : Int) atom0169Coded) := by
  have h := atom0169_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0169Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0170 : SparsePolynomial.Poly := [([0,13,15], -4), ([1,13,15], -8), ([2,13,15], -16), ([3,13,15], -16), ([4,13,15], -16), ([5,13,15], -16), ([6,13,15], -16), ([7,13,15], -16), ([8,13,15], -16), ([9,13,15], -16), ([10,13,15], -16), ([11,13,15], -16), ([12,13,15], -16), ([13,13,15], -16), ([13,14,15], -16), ([13,15,15], -16), ([13,15,16], -16), ([13,15,17], -16), ([13,15,18], -8), ([13,15,20], 8), ([13,15,21], 12), ([13,15,22], 16), ([13,15,23], 18)]
theorem atom0170_data : atom0170 = SparsePolynomial.monoTimes [13,15] 1 base07 := by decide +kernel
theorem eval_atom0170 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0170 = (quadB (outer g) ![1,2,2] * g 13 * g 15) := by
  rw [atom0170_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0170_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6929798142960 : Int) atom0170) := by
  rw [SparsePolynomial.eval_scale, eval_atom0170]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0170Coded : CoefficientMerge.Poly := [(327, -4), (903, -8), (1479, -16), (2055, -16), (2631, -16), (3207, -16), (3783, -16), (4359, -16), (4935, -16), (5511, -16), (6087, -16), (6663, -16), (7239, -16), (7815, -16), (7839, -16), (7863, -16), (7864, -16), (7865, -16), (7866, -8), (7868, 8), (7869, 12), (7870, 16), (7871, 18)]
theorem atom0170Coded_decode : atom0170 = SparsePolynomial.decodeCubic 24 atom0170Coded := by decide +kernel
theorem atom0170Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6929798142960 : Int) atom0170Coded) := by
  have h := atom0170_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0170Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0171 : SparsePolynomial.Poly := [([0,13,16], -4), ([1,13,16], -8), ([2,13,16], -16), ([3,13,16], -16), ([4,13,16], -16), ([5,13,16], -16), ([6,13,16], -16), ([7,13,16], -16), ([8,13,16], -16), ([9,13,16], -16), ([10,13,16], -16), ([11,13,16], -16), ([12,13,16], -16), ([13,13,16], -16), ([13,14,16], -16), ([13,15,16], -16), ([13,16,16], -16), ([13,16,17], -16), ([13,16,18], -8), ([13,16,20], 8), ([13,16,21], 12), ([13,16,22], 16), ([13,16,23], 18)]
theorem atom0171_data : atom0171 = SparsePolynomial.monoTimes [13,16] 1 base07 := by decide +kernel
theorem eval_atom0171 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0171 = (quadB (outer g) ![1,2,2] * g 13 * g 16) := by
  rw [atom0171_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0171_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5086603594800 : Int) atom0171) := by
  rw [SparsePolynomial.eval_scale, eval_atom0171]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0171Coded : CoefficientMerge.Poly := [(328, -4), (904, -8), (1480, -16), (2056, -16), (2632, -16), (3208, -16), (3784, -16), (4360, -16), (4936, -16), (5512, -16), (6088, -16), (6664, -16), (7240, -16), (7816, -16), (7840, -16), (7864, -16), (7888, -16), (7889, -16), (7890, -8), (7892, 8), (7893, 12), (7894, 16), (7895, 18)]
theorem atom0171Coded_decode : atom0171 = SparsePolynomial.decodeCubic 24 atom0171Coded := by decide +kernel
theorem atom0171Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5086603594800 : Int) atom0171Coded) := by
  have h := atom0171_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0171Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0172 : SparsePolynomial.Poly := [([0,13,17], -4), ([1,13,17], -8), ([2,13,17], -16), ([3,13,17], -16), ([4,13,17], -16), ([5,13,17], -16), ([6,13,17], -16), ([7,13,17], -16), ([8,13,17], -16), ([9,13,17], -16), ([10,13,17], -16), ([11,13,17], -16), ([12,13,17], -16), ([13,13,17], -16), ([13,14,17], -16), ([13,15,17], -16), ([13,16,17], -16), ([13,17,17], -16), ([13,17,18], -8), ([13,17,20], 8), ([13,17,21], 12), ([13,17,22], 16), ([13,17,23], 18)]
theorem atom0172_data : atom0172 = SparsePolynomial.monoTimes [13,17] 1 base07 := by decide +kernel
theorem eval_atom0172 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0172 = (quadB (outer g) ![1,2,2] * g 13 * g 17) := by
  rw [atom0172_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0172_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1944527785200 : Int) atom0172) := by
  rw [SparsePolynomial.eval_scale, eval_atom0172]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0172Coded : CoefficientMerge.Poly := [(329, -4), (905, -8), (1481, -16), (2057, -16), (2633, -16), (3209, -16), (3785, -16), (4361, -16), (4937, -16), (5513, -16), (6089, -16), (6665, -16), (7241, -16), (7817, -16), (7841, -16), (7865, -16), (7889, -16), (7913, -16), (7914, -8), (7916, 8), (7917, 12), (7918, 16), (7919, 18)]
theorem atom0172Coded_decode : atom0172 = SparsePolynomial.decodeCubic 24 atom0172Coded := by decide +kernel
theorem atom0172Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1944527785200 : Int) atom0172Coded) := by
  have h := atom0172_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0172Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0173 : SparsePolynomial.Poly := [([0,13,19], -4), ([1,13,19], -8), ([2,13,19], -16), ([3,13,19], -16), ([4,13,19], -16), ([5,13,19], -16), ([6,13,19], -16), ([7,13,19], -16), ([8,13,19], -16), ([9,13,19], -16), ([10,13,19], -16), ([11,13,19], -16), ([12,13,19], -16), ([13,13,19], -16), ([13,14,19], -16), ([13,15,19], -16), ([13,16,19], -16), ([13,17,19], -16), ([13,18,19], -8), ([13,19,20], 8), ([13,19,21], 12), ([13,19,22], 16), ([13,19,23], 18)]
theorem atom0173_data : atom0173 = SparsePolynomial.monoTimes [13,19] 1 base07 := by decide +kernel
theorem eval_atom0173 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0173 = (quadB (outer g) ![1,2,2] * g 13 * g 19) := by
  rw [atom0173_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0173_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (901226541600 : Int) atom0173) := by
  rw [SparsePolynomial.eval_scale, eval_atom0173]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0173Coded : CoefficientMerge.Poly := [(331, -4), (907, -8), (1483, -16), (2059, -16), (2635, -16), (3211, -16), (3787, -16), (4363, -16), (4939, -16), (5515, -16), (6091, -16), (6667, -16), (7243, -16), (7819, -16), (7843, -16), (7867, -16), (7891, -16), (7915, -16), (7939, -8), (7964, 8), (7965, 12), (7966, 16), (7967, 18)]
theorem atom0173Coded_decode : atom0173 = SparsePolynomial.decodeCubic 24 atom0173Coded := by decide +kernel
theorem atom0173Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (901226541600 : Int) atom0173Coded) := by
  have h := atom0173_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0173Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0174 : SparsePolynomial.Poly := [([0,13,22], -4), ([1,13,22], -8), ([2,13,22], -16), ([3,13,22], -16), ([4,13,22], -16), ([5,13,22], -16), ([6,13,22], -16), ([7,13,22], -16), ([8,13,22], -16), ([9,13,22], -16), ([10,13,22], -16), ([11,13,22], -16), ([12,13,22], -16), ([13,13,22], -16), ([13,14,22], -16), ([13,15,22], -16), ([13,16,22], -16), ([13,17,22], -16), ([13,18,22], -8), ([13,20,22], 8), ([13,21,22], 12), ([13,22,22], 16), ([13,22,23], 18)]
theorem atom0174_data : atom0174 = SparsePolynomial.monoTimes [13,22] 1 base07 := by decide +kernel
theorem eval_atom0174 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0174 = (quadB (outer g) ![1,2,2] * g 13 * g 22) := by
  rw [atom0174_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0174_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11717774938800 : Int) atom0174) := by
  rw [SparsePolynomial.eval_scale, eval_atom0174]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0174Coded : CoefficientMerge.Poly := [(334, -4), (910, -8), (1486, -16), (2062, -16), (2638, -16), (3214, -16), (3790, -16), (4366, -16), (4942, -16), (5518, -16), (6094, -16), (6670, -16), (7246, -16), (7822, -16), (7846, -16), (7870, -16), (7894, -16), (7918, -16), (7942, -8), (7990, 8), (8014, 12), (8038, 16), (8039, 18)]
theorem atom0174Coded_decode : atom0174 = SparsePolynomial.decodeCubic 24 atom0174Coded := by decide +kernel
theorem atom0174Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11717774938800 : Int) atom0174Coded) := by
  have h := atom0174_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0174Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0175 : SparsePolynomial.Poly := [([0,13,23], -4), ([1,13,23], -8), ([2,13,23], -16), ([3,13,23], -16), ([4,13,23], -16), ([5,13,23], -16), ([6,13,23], -16), ([7,13,23], -16), ([8,13,23], -16), ([9,13,23], -16), ([10,13,23], -16), ([11,13,23], -16), ([12,13,23], -16), ([13,13,23], -16), ([13,14,23], -16), ([13,15,23], -16), ([13,16,23], -16), ([13,17,23], -16), ([13,18,23], -8), ([13,20,23], 8), ([13,21,23], 12), ([13,22,23], 16), ([13,23,23], 18)]
theorem atom0175_data : atom0175 = SparsePolynomial.monoTimes [13,23] 1 base07 := by decide +kernel
theorem eval_atom0175 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0175 = (quadB (outer g) ![1,2,2] * g 13 * g 23) := by
  rw [atom0175_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0175_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8234821702800 : Int) atom0175) := by
  rw [SparsePolynomial.eval_scale, eval_atom0175]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0175Coded : CoefficientMerge.Poly := [(335, -4), (911, -8), (1487, -16), (2063, -16), (2639, -16), (3215, -16), (3791, -16), (4367, -16), (4943, -16), (5519, -16), (6095, -16), (6671, -16), (7247, -16), (7823, -16), (7847, -16), (7871, -16), (7895, -16), (7919, -16), (7943, -8), (7991, 8), (8015, 12), (8039, 16), (8063, 18)]
theorem atom0175Coded_decode : atom0175 = SparsePolynomial.decodeCubic 24 atom0175Coded := by decide +kernel
theorem atom0175Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8234821702800 : Int) atom0175Coded) := by
  have h := atom0175_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0175Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0176 : SparsePolynomial.Poly := [([0,14,15], -4), ([1,14,15], -8), ([2,14,15], -16), ([3,14,15], -16), ([4,14,15], -16), ([5,14,15], -16), ([6,14,15], -16), ([7,14,15], -16), ([8,14,15], -16), ([9,14,15], -16), ([10,14,15], -16), ([11,14,15], -16), ([12,14,15], -16), ([13,14,15], -16), ([14,14,15], -16), ([14,15,15], -16), ([14,15,16], -16), ([14,15,17], -16), ([14,15,18], -8), ([14,15,20], 8), ([14,15,21], 12), ([14,15,22], 16), ([14,15,23], 18)]
theorem atom0176_data : atom0176 = SparsePolynomial.monoTimes [14,15] 1 base07 := by decide +kernel
theorem eval_atom0176 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0176 = (quadB (outer g) ![1,2,2] * g 14 * g 15) := by
  rw [atom0176_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0176_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3159850811040 : Int) atom0176) := by
  rw [SparsePolynomial.eval_scale, eval_atom0176]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0176Coded : CoefficientMerge.Poly := [(351, -4), (927, -8), (1503, -16), (2079, -16), (2655, -16), (3231, -16), (3807, -16), (4383, -16), (4959, -16), (5535, -16), (6111, -16), (6687, -16), (7263, -16), (7839, -16), (8415, -16), (8439, -16), (8440, -16), (8441, -16), (8442, -8), (8444, 8), (8445, 12), (8446, 16), (8447, 18)]
theorem atom0176Coded_decode : atom0176 = SparsePolynomial.decodeCubic 24 atom0176Coded := by decide +kernel
theorem atom0176Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3159850811040 : Int) atom0176Coded) := by
  have h := atom0176_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0176Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0177 : SparsePolynomial.Poly := [([0,14,16], -4), ([1,14,16], -8), ([2,14,16], -16), ([3,14,16], -16), ([4,14,16], -16), ([5,14,16], -16), ([6,14,16], -16), ([7,14,16], -16), ([8,14,16], -16), ([9,14,16], -16), ([10,14,16], -16), ([11,14,16], -16), ([12,14,16], -16), ([13,14,16], -16), ([14,14,16], -16), ([14,15,16], -16), ([14,16,16], -16), ([14,16,17], -16), ([14,16,18], -8), ([14,16,20], 8), ([14,16,21], 12), ([14,16,22], 16), ([14,16,23], 18)]
theorem atom0177_data : atom0177 = SparsePolynomial.monoTimes [14,16] 1 base07 := by decide +kernel
theorem eval_atom0177 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0177 = (quadB (outer g) ![1,2,2] * g 14 * g 16) := by
  rw [atom0177_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0177_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7121823730560 : Int) atom0177) := by
  rw [SparsePolynomial.eval_scale, eval_atom0177]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0177Coded : CoefficientMerge.Poly := [(352, -4), (928, -8), (1504, -16), (2080, -16), (2656, -16), (3232, -16), (3808, -16), (4384, -16), (4960, -16), (5536, -16), (6112, -16), (6688, -16), (7264, -16), (7840, -16), (8416, -16), (8440, -16), (8464, -16), (8465, -16), (8466, -8), (8468, 8), (8469, 12), (8470, 16), (8471, 18)]
theorem atom0177Coded_decode : atom0177 = SparsePolynomial.decodeCubic 24 atom0177Coded := by decide +kernel
theorem atom0177Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7121823730560 : Int) atom0177Coded) := by
  have h := atom0177_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0177Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0178 : SparsePolynomial.Poly := [([0,14,17], -4), ([1,14,17], -8), ([2,14,17], -16), ([3,14,17], -16), ([4,14,17], -16), ([5,14,17], -16), ([6,14,17], -16), ([7,14,17], -16), ([8,14,17], -16), ([9,14,17], -16), ([10,14,17], -16), ([11,14,17], -16), ([12,14,17], -16), ([13,14,17], -16), ([14,14,17], -16), ([14,15,17], -16), ([14,16,17], -16), ([14,17,17], -16), ([14,17,18], -8), ([14,17,20], 8), ([14,17,21], 12), ([14,17,22], 16), ([14,17,23], 18)]
theorem atom0178_data : atom0178 = SparsePolynomial.monoTimes [14,17] 1 base07 := by decide +kernel
theorem eval_atom0178 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0178 = (quadB (outer g) ![1,2,2] * g 14 * g 17) := by
  rw [atom0178_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0178_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3480602202000 : Int) atom0178) := by
  rw [SparsePolynomial.eval_scale, eval_atom0178]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0178Coded : CoefficientMerge.Poly := [(353, -4), (929, -8), (1505, -16), (2081, -16), (2657, -16), (3233, -16), (3809, -16), (4385, -16), (4961, -16), (5537, -16), (6113, -16), (6689, -16), (7265, -16), (7841, -16), (8417, -16), (8441, -16), (8465, -16), (8489, -16), (8490, -8), (8492, 8), (8493, 12), (8494, 16), (8495, 18)]
theorem atom0178Coded_decode : atom0178 = SparsePolynomial.decodeCubic 24 atom0178Coded := by decide +kernel
theorem atom0178Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3480602202000 : Int) atom0178Coded) := by
  have h := atom0178_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0178Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0179 : SparsePolynomial.Poly := [([0,14,19], -4), ([1,14,19], -8), ([2,14,19], -16), ([3,14,19], -16), ([4,14,19], -16), ([5,14,19], -16), ([6,14,19], -16), ([7,14,19], -16), ([8,14,19], -16), ([9,14,19], -16), ([10,14,19], -16), ([11,14,19], -16), ([12,14,19], -16), ([13,14,19], -16), ([14,14,19], -16), ([14,15,19], -16), ([14,16,19], -16), ([14,17,19], -16), ([14,18,19], -8), ([14,19,20], 8), ([14,19,21], 12), ([14,19,22], 16), ([14,19,23], 18)]
theorem atom0179_data : atom0179 = SparsePolynomial.monoTimes [14,19] 1 base07 := by decide +kernel
theorem eval_atom0179 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0179 = (quadB (outer g) ![1,2,2] * g 14 * g 19) := by
  rw [atom0179_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0179_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1196311658850 : Int) atom0179) := by
  rw [SparsePolynomial.eval_scale, eval_atom0179]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0179Coded : CoefficientMerge.Poly := [(355, -4), (931, -8), (1507, -16), (2083, -16), (2659, -16), (3235, -16), (3811, -16), (4387, -16), (4963, -16), (5539, -16), (6115, -16), (6691, -16), (7267, -16), (7843, -16), (8419, -16), (8443, -16), (8467, -16), (8491, -16), (8515, -8), (8540, 8), (8541, 12), (8542, 16), (8543, 18)]
theorem atom0179Coded_decode : atom0179 = SparsePolynomial.decodeCubic 24 atom0179Coded := by decide +kernel
theorem atom0179Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1196311658850 : Int) atom0179Coded) := by
  have h := atom0179_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0179Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0180 : SparsePolynomial.Poly := [([0,14,22], -4), ([1,14,22], -8), ([2,14,22], -16), ([3,14,22], -16), ([4,14,22], -16), ([5,14,22], -16), ([6,14,22], -16), ([7,14,22], -16), ([8,14,22], -16), ([9,14,22], -16), ([10,14,22], -16), ([11,14,22], -16), ([12,14,22], -16), ([13,14,22], -16), ([14,14,22], -16), ([14,15,22], -16), ([14,16,22], -16), ([14,17,22], -16), ([14,18,22], -8), ([14,20,22], 8), ([14,21,22], 12), ([14,22,22], 16), ([14,22,23], 18)]
theorem atom0180_data : atom0180 = SparsePolynomial.monoTimes [14,22] 1 base07 := by decide +kernel
theorem eval_atom0180 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0180 = (quadB (outer g) ![1,2,2] * g 14 * g 22) := by
  rw [atom0180_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0180_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8902176472350 : Int) atom0180) := by
  rw [SparsePolynomial.eval_scale, eval_atom0180]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0180Coded : CoefficientMerge.Poly := [(358, -4), (934, -8), (1510, -16), (2086, -16), (2662, -16), (3238, -16), (3814, -16), (4390, -16), (4966, -16), (5542, -16), (6118, -16), (6694, -16), (7270, -16), (7846, -16), (8422, -16), (8446, -16), (8470, -16), (8494, -16), (8518, -8), (8566, 8), (8590, 12), (8614, 16), (8615, 18)]
theorem atom0180Coded_decode : atom0180 = SparsePolynomial.decodeCubic 24 atom0180Coded := by decide +kernel
theorem atom0180Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8902176472350 : Int) atom0180Coded) := by
  have h := atom0180_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0180Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0181 : SparsePolynomial.Poly := [([0,14,23], -4), ([1,14,23], -8), ([2,14,23], -16), ([3,14,23], -16), ([4,14,23], -16), ([5,14,23], -16), ([6,14,23], -16), ([7,14,23], -16), ([8,14,23], -16), ([9,14,23], -16), ([10,14,23], -16), ([11,14,23], -16), ([12,14,23], -16), ([13,14,23], -16), ([14,14,23], -16), ([14,15,23], -16), ([14,16,23], -16), ([14,17,23], -16), ([14,18,23], -8), ([14,20,23], 8), ([14,21,23], 12), ([14,22,23], 16), ([14,23,23], 18)]
theorem atom0181_data : atom0181 = SparsePolynomial.monoTimes [14,23] 1 base07 := by decide +kernel
theorem eval_atom0181 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0181 = (quadB (outer g) ![1,2,2] * g 14 * g 23) := by
  rw [atom0181_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0181_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4931785192950 : Int) atom0181) := by
  rw [SparsePolynomial.eval_scale, eval_atom0181]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0181Coded : CoefficientMerge.Poly := [(359, -4), (935, -8), (1511, -16), (2087, -16), (2663, -16), (3239, -16), (3815, -16), (4391, -16), (4967, -16), (5543, -16), (6119, -16), (6695, -16), (7271, -16), (7847, -16), (8423, -16), (8447, -16), (8471, -16), (8495, -16), (8519, -8), (8567, 8), (8591, 12), (8615, 16), (8639, 18)]
theorem atom0181Coded_decode : atom0181 = SparsePolynomial.decodeCubic 24 atom0181Coded := by decide +kernel
theorem atom0181Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4931785192950 : Int) atom0181Coded) := by
  have h := atom0181_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0181Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0182 : SparsePolynomial.Poly := [([0,15,16], -4), ([1,15,16], -8), ([2,15,16], -16), ([3,15,16], -16), ([4,15,16], -16), ([5,15,16], -16), ([6,15,16], -16), ([7,15,16], -16), ([8,15,16], -16), ([9,15,16], -16), ([10,15,16], -16), ([11,15,16], -16), ([12,15,16], -16), ([13,15,16], -16), ([14,15,16], -16), ([15,15,16], -16), ([15,16,16], -16), ([15,16,17], -16), ([15,16,18], -8), ([15,16,20], 8), ([15,16,21], 12), ([15,16,22], 16), ([15,16,23], 18)]
theorem atom0182_data : atom0182 = SparsePolynomial.monoTimes [15,16] 1 base07 := by decide +kernel
theorem eval_atom0182 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0182 = (quadB (outer g) ![1,2,2] * g 15 * g 16) := by
  rw [atom0182_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0182_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2967160775040 : Int) atom0182) := by
  rw [SparsePolynomial.eval_scale, eval_atom0182]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 15 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0182Coded : CoefficientMerge.Poly := [(376, -4), (952, -8), (1528, -16), (2104, -16), (2680, -16), (3256, -16), (3832, -16), (4408, -16), (4984, -16), (5560, -16), (6136, -16), (6712, -16), (7288, -16), (7864, -16), (8440, -16), (9016, -16), (9040, -16), (9041, -16), (9042, -8), (9044, 8), (9045, 12), (9046, 16), (9047, 18)]
theorem atom0182Coded_decode : atom0182 = SparsePolynomial.decodeCubic 24 atom0182Coded := by decide +kernel
theorem atom0182Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2967160775040 : Int) atom0182Coded) := by
  have h := atom0182_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0182Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0183 : SparsePolynomial.Poly := [([0,15,17], -4), ([1,15,17], -8), ([2,15,17], -16), ([3,15,17], -16), ([4,15,17], -16), ([5,15,17], -16), ([6,15,17], -16), ([7,15,17], -16), ([8,15,17], -16), ([9,15,17], -16), ([10,15,17], -16), ([11,15,17], -16), ([12,15,17], -16), ([13,15,17], -16), ([14,15,17], -16), ([15,15,17], -16), ([15,16,17], -16), ([15,17,17], -16), ([15,17,18], -8), ([15,17,20], 8), ([15,17,21], 12), ([15,17,22], 16), ([15,17,23], 18)]
theorem atom0183_data : atom0183 = SparsePolynomial.monoTimes [15,17] 1 base07 := by decide +kernel
theorem eval_atom0183 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0183 = (quadB (outer g) ![1,2,2] * g 15 * g 17) := by
  rw [atom0183_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0183_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4093485379200 : Int) atom0183) := by
  rw [SparsePolynomial.eval_scale, eval_atom0183]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 15 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0183Coded : CoefficientMerge.Poly := [(377, -4), (953, -8), (1529, -16), (2105, -16), (2681, -16), (3257, -16), (3833, -16), (4409, -16), (4985, -16), (5561, -16), (6137, -16), (6713, -16), (7289, -16), (7865, -16), (8441, -16), (9017, -16), (9041, -16), (9065, -16), (9066, -8), (9068, 8), (9069, 12), (9070, 16), (9071, 18)]
theorem atom0183Coded_decode : atom0183 = SparsePolynomial.decodeCubic 24 atom0183Coded := by decide +kernel
theorem atom0183Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4093485379200 : Int) atom0183Coded) := by
  have h := atom0183_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0183Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0184 : SparsePolynomial.Poly := [([0,15,22], -4), ([1,15,22], -8), ([2,15,22], -16), ([3,15,22], -16), ([4,15,22], -16), ([5,15,22], -16), ([6,15,22], -16), ([7,15,22], -16), ([8,15,22], -16), ([9,15,22], -16), ([10,15,22], -16), ([11,15,22], -16), ([12,15,22], -16), ([13,15,22], -16), ([14,15,22], -16), ([15,15,22], -16), ([15,16,22], -16), ([15,17,22], -16), ([15,18,22], -8), ([15,20,22], 8), ([15,21,22], 12), ([15,22,22], 16), ([15,22,23], 18)]
theorem atom0184_data : atom0184 = SparsePolynomial.monoTimes [15,22] 1 base07 := by decide +kernel
theorem eval_atom0184 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0184 = (quadB (outer g) ![1,2,2] * g 15 * g 22) := by
  rw [atom0184_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0184_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4783424436000 : Int) atom0184) := by
  rw [SparsePolynomial.eval_scale, eval_atom0184]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 15 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0184Coded : CoefficientMerge.Poly := [(382, -4), (958, -8), (1534, -16), (2110, -16), (2686, -16), (3262, -16), (3838, -16), (4414, -16), (4990, -16), (5566, -16), (6142, -16), (6718, -16), (7294, -16), (7870, -16), (8446, -16), (9022, -16), (9046, -16), (9070, -16), (9094, -8), (9142, 8), (9166, 12), (9190, 16), (9191, 18)]
theorem atom0184Coded_decode : atom0184 = SparsePolynomial.decodeCubic 24 atom0184Coded := by decide +kernel
theorem atom0184Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4783424436000 : Int) atom0184Coded) := by
  have h := atom0184_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0184Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0185 : SparsePolynomial.Poly := [([0,16,17], -4), ([1,16,17], -8), ([2,16,17], -16), ([3,16,17], -16), ([4,16,17], -16), ([5,16,17], -16), ([6,16,17], -16), ([7,16,17], -16), ([8,16,17], -16), ([9,16,17], -16), ([10,16,17], -16), ([11,16,17], -16), ([12,16,17], -16), ([13,16,17], -16), ([14,16,17], -16), ([15,16,17], -16), ([16,16,17], -16), ([16,17,17], -16), ([16,17,18], -8), ([16,17,20], 8), ([16,17,21], 12), ([16,17,22], 16), ([16,17,23], 18)]
theorem atom0185_data : atom0185 = SparsePolynomial.monoTimes [16,17] 1 base07 := by decide +kernel
theorem eval_atom0185 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0185 = (quadB (outer g) ![1,2,2] * g 16 * g 17) := by
  rw [atom0185_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0185_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3762039724800 : Int) atom0185) := by
  rw [SparsePolynomial.eval_scale, eval_atom0185]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 16 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0185Coded : CoefficientMerge.Poly := [(401, -4), (977, -8), (1553, -16), (2129, -16), (2705, -16), (3281, -16), (3857, -16), (4433, -16), (5009, -16), (5585, -16), (6161, -16), (6737, -16), (7313, -16), (7889, -16), (8465, -16), (9041, -16), (9617, -16), (9641, -16), (9642, -8), (9644, 8), (9645, 12), (9646, 16), (9647, 18)]
theorem atom0185Coded_decode : atom0185 = SparsePolynomial.decodeCubic 24 atom0185Coded := by decide +kernel
theorem atom0185Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3762039724800 : Int) atom0185Coded) := by
  have h := atom0185_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0185Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0186 : SparsePolynomial.Poly := [([0,22,22], -4), ([1,22,22], -8), ([2,22,22], -16), ([3,22,22], -16), ([4,22,22], -16), ([5,22,22], -16), ([6,22,22], -16), ([7,22,22], -16), ([8,22,22], -16), ([9,22,22], -16), ([10,22,22], -16), ([11,22,22], -16), ([12,22,22], -16), ([13,22,22], -16), ([14,22,22], -16), ([15,22,22], -16), ([16,22,22], -16), ([17,22,22], -16), ([18,22,22], -8), ([20,22,22], 8), ([21,22,22], 12), ([22,22,22], 16), ([22,22,23], 18)]
theorem atom0186_data : atom0186 = SparsePolynomial.monoTimes [22,22] 1 base07 := by decide +kernel
theorem eval_atom0186 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0186 = (quadB (outer g) ![1,2,2] * g 22 * g 22) := by
  rw [atom0186_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0186_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77367969000 : Int) atom0186) := by
  rw [SparsePolynomial.eval_scale, eval_atom0186]
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 22 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0186Coded : CoefficientMerge.Poly := [(550, -4), (1126, -8), (1702, -16), (2278, -16), (2854, -16), (3430, -16), (4006, -16), (4582, -16), (5158, -16), (5734, -16), (6310, -16), (6886, -16), (7462, -16), (8038, -16), (8614, -16), (9190, -16), (9766, -16), (10342, -16), (10918, -8), (12070, 8), (12646, 12), (13222, 16), (13223, 18)]
theorem atom0186Coded_decode : atom0186 = SparsePolynomial.decodeCubic 24 atom0186Coded := by decide +kernel
theorem atom0186Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (77367969000 : Int) atom0186Coded) := by
  have h := atom0186_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0186Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0187 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -16), ([0,1,4], -16), ([0,1,5], -16), ([0,1,6], -16), ([0,1,7], -16), ([0,1,8], -16), ([0,1,9], -16), ([0,1,10], -16), ([0,1,11], -16), ([0,1,12], -16), ([0,1,13], -16), ([0,1,14], -16), ([0,1,15], -16), ([0,1,16], -16), ([0,1,17], -16), ([0,1,18], -14), ([0,1,19], -10), ([0,1,20], -2), ([0,1,21], 2), ([0,1,22], 10), ([0,1,23], 18)]
theorem atom0187_data : atom0187 = SparsePolynomial.monoTimes [0,1] 1 base08 := by decide +kernel
theorem eval_atom0187 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0187 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0187_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0187_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (813284841600 : Int) atom0187) := by
  rw [SparsePolynomial.eval_scale, eval_atom0187]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0187Coded : CoefficientMerge.Poly := [(1, -8), (25, -12), (26, -16), (27, -16), (28, -16), (29, -16), (30, -16), (31, -16), (32, -16), (33, -16), (34, -16), (35, -16), (36, -16), (37, -16), (38, -16), (39, -16), (40, -16), (41, -16), (42, -14), (43, -10), (44, -2), (45, 2), (46, 10), (47, 18)]
theorem atom0187Coded_decode : atom0187 = SparsePolynomial.decodeCubic 24 atom0187Coded := by decide +kernel
theorem atom0187Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (813284841600 : Int) atom0187Coded) := by
  have h := atom0187_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0187Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0188 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -16), ([0,2,4], -16), ([0,2,5], -16), ([0,2,6], -16), ([0,2,7], -16), ([0,2,8], -16), ([0,2,9], -16), ([0,2,10], -16), ([0,2,11], -16), ([0,2,12], -16), ([0,2,13], -16), ([0,2,14], -16), ([0,2,15], -16), ([0,2,16], -16), ([0,2,17], -16), ([0,2,18], -14), ([0,2,19], -10), ([0,2,20], -2), ([0,2,21], 2), ([0,2,22], 10), ([0,2,23], 18)]
theorem atom0188_data : atom0188 = SparsePolynomial.monoTimes [0,2] 1 base08 := by decide +kernel
theorem eval_atom0188 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0188 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0188_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0188_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1198664913600 : Int) atom0188) := by
  rw [SparsePolynomial.eval_scale, eval_atom0188]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0188Coded : CoefficientMerge.Poly := [(2, -8), (26, -12), (50, -16), (51, -16), (52, -16), (53, -16), (54, -16), (55, -16), (56, -16), (57, -16), (58, -16), (59, -16), (60, -16), (61, -16), (62, -16), (63, -16), (64, -16), (65, -16), (66, -14), (67, -10), (68, -2), (69, 2), (70, 10), (71, 18)]
theorem atom0188Coded_decode : atom0188 = SparsePolynomial.decodeCubic 24 atom0188Coded := by decide +kernel
theorem atom0188Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1198664913600 : Int) atom0188Coded) := by
  have h := atom0188_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0188Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0189 : SparsePolynomial.Poly := [([0,0,3], -8), ([0,1,3], -12), ([0,2,3], -16), ([0,3,3], -16), ([0,3,4], -16), ([0,3,5], -16), ([0,3,6], -16), ([0,3,7], -16), ([0,3,8], -16), ([0,3,9], -16), ([0,3,10], -16), ([0,3,11], -16), ([0,3,12], -16), ([0,3,13], -16), ([0,3,14], -16), ([0,3,15], -16), ([0,3,16], -16), ([0,3,17], -16), ([0,3,18], -14), ([0,3,19], -10), ([0,3,20], -2), ([0,3,21], 2), ([0,3,22], 10), ([0,3,23], 18)]
theorem atom0189_data : atom0189 = SparsePolynomial.monoTimes [0,3] 1 base08 := by decide +kernel
theorem eval_atom0189 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0189 = (quadB (outer g) ![2,2,1] * g 0 * g 3) := by
  rw [atom0189_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0189_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1584044985600 : Int) atom0189) := by
  rw [SparsePolynomial.eval_scale, eval_atom0189]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0189Coded : CoefficientMerge.Poly := [(3, -8), (27, -12), (51, -16), (75, -16), (76, -16), (77, -16), (78, -16), (79, -16), (80, -16), (81, -16), (82, -16), (83, -16), (84, -16), (85, -16), (86, -16), (87, -16), (88, -16), (89, -16), (90, -14), (91, -10), (92, -2), (93, 2), (94, 10), (95, 18)]
theorem atom0189Coded_decode : atom0189 = SparsePolynomial.decodeCubic 24 atom0189Coded := by decide +kernel
theorem atom0189Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1584044985600 : Int) atom0189Coded) := by
  have h := atom0189_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0189Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0190 : SparsePolynomial.Poly := [([0,0,4], -8), ([0,1,4], -12), ([0,2,4], -16), ([0,3,4], -16), ([0,4,4], -16), ([0,4,5], -16), ([0,4,6], -16), ([0,4,7], -16), ([0,4,8], -16), ([0,4,9], -16), ([0,4,10], -16), ([0,4,11], -16), ([0,4,12], -16), ([0,4,13], -16), ([0,4,14], -16), ([0,4,15], -16), ([0,4,16], -16), ([0,4,17], -16), ([0,4,18], -14), ([0,4,19], -10), ([0,4,20], -2), ([0,4,21], 2), ([0,4,22], 10), ([0,4,23], 18)]
theorem atom0190_data : atom0190 = SparsePolynomial.monoTimes [0,4] 1 base08 := by decide +kernel
theorem eval_atom0190 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0190 = (quadB (outer g) ![2,2,1] * g 0 * g 4) := by
  rw [atom0190_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0190_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1969425057600 : Int) atom0190) := by
  rw [SparsePolynomial.eval_scale, eval_atom0190]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0190Coded : CoefficientMerge.Poly := [(4, -8), (28, -12), (52, -16), (76, -16), (100, -16), (101, -16), (102, -16), (103, -16), (104, -16), (105, -16), (106, -16), (107, -16), (108, -16), (109, -16), (110, -16), (111, -16), (112, -16), (113, -16), (114, -14), (115, -10), (116, -2), (117, 2), (118, 10), (119, 18)]
theorem atom0190Coded_decode : atom0190 = SparsePolynomial.decodeCubic 24 atom0190Coded := by decide +kernel
theorem atom0190Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1969425057600 : Int) atom0190Coded) := by
  have h := atom0190_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0190Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0191 : SparsePolynomial.Poly := [([0,0,5], -8), ([0,1,5], -12), ([0,2,5], -16), ([0,3,5], -16), ([0,4,5], -16), ([0,5,5], -16), ([0,5,6], -16), ([0,5,7], -16), ([0,5,8], -16), ([0,5,9], -16), ([0,5,10], -16), ([0,5,11], -16), ([0,5,12], -16), ([0,5,13], -16), ([0,5,14], -16), ([0,5,15], -16), ([0,5,16], -16), ([0,5,17], -16), ([0,5,18], -14), ([0,5,19], -10), ([0,5,20], -2), ([0,5,21], 2), ([0,5,22], 10), ([0,5,23], 18)]
theorem atom0191_data : atom0191 = SparsePolynomial.monoTimes [0,5] 1 base08 := by decide +kernel
theorem eval_atom0191 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0191 = (quadB (outer g) ![2,2,1] * g 0 * g 5) := by
  rw [atom0191_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0191_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1494443412000 : Int) atom0191) := by
  rw [SparsePolynomial.eval_scale, eval_atom0191]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0191Coded : CoefficientMerge.Poly := [(5, -8), (29, -12), (53, -16), (77, -16), (101, -16), (125, -16), (126, -16), (127, -16), (128, -16), (129, -16), (130, -16), (131, -16), (132, -16), (133, -16), (134, -16), (135, -16), (136, -16), (137, -16), (138, -14), (139, -10), (140, -2), (141, 2), (142, 10), (143, 18)]
theorem atom0191Coded_decode : atom0191 = SparsePolynomial.decodeCubic 24 atom0191Coded := by decide +kernel
theorem atom0191Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1494443412000 : Int) atom0191Coded) := by
  have h := atom0191_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0191Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0192 : SparsePolynomial.Poly := [([0,0,6], -8), ([0,1,6], -12), ([0,2,6], -16), ([0,3,6], -16), ([0,4,6], -16), ([0,5,6], -16), ([0,6,6], -16), ([0,6,7], -16), ([0,6,8], -16), ([0,6,9], -16), ([0,6,10], -16), ([0,6,11], -16), ([0,6,12], -16), ([0,6,13], -16), ([0,6,14], -16), ([0,6,15], -16), ([0,6,16], -16), ([0,6,17], -16), ([0,6,18], -14), ([0,6,19], -10), ([0,6,20], -2), ([0,6,21], 2), ([0,6,22], 10), ([0,6,23], 18)]
theorem atom0192_data : atom0192 = SparsePolynomial.monoTimes [0,6] 1 base08 := by decide +kernel
theorem eval_atom0192 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0192 = (quadB (outer g) ![2,2,1] * g 0 * g 6) := by
  rw [atom0192_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0192_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2740185201600 : Int) atom0192) := by
  rw [SparsePolynomial.eval_scale, eval_atom0192]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0192Coded : CoefficientMerge.Poly := [(6, -8), (30, -12), (54, -16), (78, -16), (102, -16), (126, -16), (150, -16), (151, -16), (152, -16), (153, -16), (154, -16), (155, -16), (156, -16), (157, -16), (158, -16), (159, -16), (160, -16), (161, -16), (162, -14), (163, -10), (164, -2), (165, 2), (166, 10), (167, 18)]
theorem atom0192Coded_decode : atom0192 = SparsePolynomial.decodeCubic 24 atom0192Coded := by decide +kernel
theorem atom0192Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2740185201600 : Int) atom0192Coded) := by
  have h := atom0192_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0192Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0193 : SparsePolynomial.Poly := [([0,0,7], -8), ([0,1,7], -12), ([0,2,7], -16), ([0,3,7], -16), ([0,4,7], -16), ([0,5,7], -16), ([0,6,7], -16), ([0,7,7], -16), ([0,7,8], -16), ([0,7,9], -16), ([0,7,10], -16), ([0,7,11], -16), ([0,7,12], -16), ([0,7,13], -16), ([0,7,14], -16), ([0,7,15], -16), ([0,7,16], -16), ([0,7,17], -16), ([0,7,18], -14), ([0,7,19], -10), ([0,7,20], -2), ([0,7,21], 2), ([0,7,22], 10), ([0,7,23], 18)]
theorem atom0193_data : atom0193 = SparsePolynomial.monoTimes [0,7] 1 base08 := by decide +kernel
theorem eval_atom0193 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0193 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0193_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0193_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3125565273600 : Int) atom0193) := by
  rw [SparsePolynomial.eval_scale, eval_atom0193]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0193Coded : CoefficientMerge.Poly := [(7, -8), (31, -12), (55, -16), (79, -16), (103, -16), (127, -16), (151, -16), (175, -16), (176, -16), (177, -16), (178, -16), (179, -16), (180, -16), (181, -16), (182, -16), (183, -16), (184, -16), (185, -16), (186, -14), (187, -10), (188, -2), (189, 2), (190, 10), (191, 18)]
theorem atom0193Coded_decode : atom0193 = SparsePolynomial.decodeCubic 24 atom0193Coded := by decide +kernel
theorem atom0193Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3125565273600 : Int) atom0193Coded) := by
  have h := atom0193_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0193Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0194 : SparsePolynomial.Poly := [([0,0,8], -8), ([0,1,8], -12), ([0,2,8], -16), ([0,3,8], -16), ([0,4,8], -16), ([0,5,8], -16), ([0,6,8], -16), ([0,7,8], -16), ([0,8,8], -16), ([0,8,9], -16), ([0,8,10], -16), ([0,8,11], -16), ([0,8,12], -16), ([0,8,13], -16), ([0,8,14], -16), ([0,8,15], -16), ([0,8,16], -16), ([0,8,17], -16), ([0,8,18], -14), ([0,8,19], -10), ([0,8,20], -2), ([0,8,21], 2), ([0,8,22], 10), ([0,8,23], 18)]
theorem atom0194_data : atom0194 = SparsePolynomial.monoTimes [0,8] 1 base08 := by decide +kernel
theorem eval_atom0194 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0194 = (quadB (outer g) ![2,2,1] * g 0 * g 8) := by
  rw [atom0194_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0194_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3510945345600 : Int) atom0194) := by
  rw [SparsePolynomial.eval_scale, eval_atom0194]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0194Coded : CoefficientMerge.Poly := [(8, -8), (32, -12), (56, -16), (80, -16), (104, -16), (128, -16), (152, -16), (176, -16), (200, -16), (201, -16), (202, -16), (203, -16), (204, -16), (205, -16), (206, -16), (207, -16), (208, -16), (209, -16), (210, -14), (211, -10), (212, -2), (213, 2), (214, 10), (215, 18)]
theorem atom0194Coded_decode : atom0194 = SparsePolynomial.decodeCubic 24 atom0194Coded := by decide +kernel
theorem atom0194Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3510945345600 : Int) atom0194Coded) := by
  have h := atom0194_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0194Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0195 : SparsePolynomial.Poly := [([0,0,9], -8), ([0,1,9], -12), ([0,2,9], -16), ([0,3,9], -16), ([0,4,9], -16), ([0,5,9], -16), ([0,6,9], -16), ([0,7,9], -16), ([0,8,9], -16), ([0,9,9], -16), ([0,9,10], -16), ([0,9,11], -16), ([0,9,12], -16), ([0,9,13], -16), ([0,9,14], -16), ([0,9,15], -16), ([0,9,16], -16), ([0,9,17], -16), ([0,9,18], -14), ([0,9,19], -10), ([0,9,20], -2), ([0,9,21], 2), ([0,9,22], 10), ([0,9,23], 18)]
theorem atom0195_data : atom0195 = SparsePolynomial.monoTimes [0,9] 1 base08 := by decide +kernel
theorem eval_atom0195 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0195 = (quadB (outer g) ![2,2,1] * g 0 * g 9) := by
  rw [atom0195_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0195_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3144852786834 : Int) atom0195) := by
  rw [SparsePolynomial.eval_scale, eval_atom0195]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0195Coded : CoefficientMerge.Poly := [(9, -8), (33, -12), (57, -16), (81, -16), (105, -16), (129, -16), (153, -16), (177, -16), (201, -16), (225, -16), (226, -16), (227, -16), (228, -16), (229, -16), (230, -16), (231, -16), (232, -16), (233, -16), (234, -14), (235, -10), (236, -2), (237, 2), (238, 10), (239, 18)]
theorem atom0195Coded_decode : atom0195 = SparsePolynomial.decodeCubic 24 atom0195Coded := by decide +kernel
theorem atom0195Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3144852786834 : Int) atom0195Coded) := by
  have h := atom0195_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0195Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0196 : SparsePolynomial.Poly := [([0,0,10], -8), ([0,1,10], -12), ([0,2,10], -16), ([0,3,10], -16), ([0,4,10], -16), ([0,5,10], -16), ([0,6,10], -16), ([0,7,10], -16), ([0,8,10], -16), ([0,9,10], -16), ([0,10,10], -16), ([0,10,11], -16), ([0,10,12], -16), ([0,10,13], -16), ([0,10,14], -16), ([0,10,15], -16), ([0,10,16], -16), ([0,10,17], -16), ([0,10,18], -14), ([0,10,19], -10), ([0,10,20], -2), ([0,10,21], 2), ([0,10,22], 10), ([0,10,23], 18)]
theorem atom0196_data : atom0196 = SparsePolynomial.monoTimes [0,10] 1 base08 := by decide +kernel
theorem eval_atom0196 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0196 = (quadB (outer g) ![2,2,1] * g 0 * g 10) := by
  rw [atom0196_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0196_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1324795729554 : Int) atom0196) := by
  rw [SparsePolynomial.eval_scale, eval_atom0196]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0196Coded : CoefficientMerge.Poly := [(10, -8), (34, -12), (58, -16), (82, -16), (106, -16), (130, -16), (154, -16), (178, -16), (202, -16), (226, -16), (250, -16), (251, -16), (252, -16), (253, -16), (254, -16), (255, -16), (256, -16), (257, -16), (258, -14), (259, -10), (260, -2), (261, 2), (262, 10), (263, 18)]
theorem atom0196Coded_decode : atom0196 = SparsePolynomial.decodeCubic 24 atom0196Coded := by decide +kernel
theorem atom0196Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1324795729554 : Int) atom0196Coded) := by
  have h := atom0196_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0196Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0197 : SparsePolynomial.Poly := [([0,0,15], -8), ([0,1,15], -12), ([0,2,15], -16), ([0,3,15], -16), ([0,4,15], -16), ([0,5,15], -16), ([0,6,15], -16), ([0,7,15], -16), ([0,8,15], -16), ([0,9,15], -16), ([0,10,15], -16), ([0,11,15], -16), ([0,12,15], -16), ([0,13,15], -16), ([0,14,15], -16), ([0,15,15], -16), ([0,15,16], -16), ([0,15,17], -16), ([0,15,18], -14), ([0,15,19], -10), ([0,15,20], -2), ([0,15,21], 2), ([0,15,22], 10), ([0,15,23], 18)]
theorem atom0197_data : atom0197 = SparsePolynomial.monoTimes [0,15] 1 base08 := by decide +kernel
theorem eval_atom0197 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0197 = (quadB (outer g) ![2,2,1] * g 0 * g 15) := by
  rw [atom0197_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0197_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78928416000 : Int) atom0197) := by
  rw [SparsePolynomial.eval_scale, eval_atom0197]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0197Coded : CoefficientMerge.Poly := [(15, -8), (39, -12), (63, -16), (87, -16), (111, -16), (135, -16), (159, -16), (183, -16), (207, -16), (231, -16), (255, -16), (279, -16), (303, -16), (327, -16), (351, -16), (375, -16), (376, -16), (377, -16), (378, -14), (379, -10), (380, -2), (381, 2), (382, 10), (383, 18)]
theorem atom0197Coded_decode : atom0197 = SparsePolynomial.decodeCubic 24 atom0197Coded := by decide +kernel
theorem atom0197Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (78928416000 : Int) atom0197Coded) := by
  have h := atom0197_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0197Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0198 : SparsePolynomial.Poly := [([0,0,16], -8), ([0,1,16], -12), ([0,2,16], -16), ([0,3,16], -16), ([0,4,16], -16), ([0,5,16], -16), ([0,6,16], -16), ([0,7,16], -16), ([0,8,16], -16), ([0,9,16], -16), ([0,10,16], -16), ([0,11,16], -16), ([0,12,16], -16), ([0,13,16], -16), ([0,14,16], -16), ([0,15,16], -16), ([0,16,16], -16), ([0,16,17], -16), ([0,16,18], -14), ([0,16,19], -10), ([0,16,20], -2), ([0,16,21], 2), ([0,16,22], 10), ([0,16,23], 18)]
theorem atom0198_data : atom0198 = SparsePolynomial.monoTimes [0,16] 1 base08 := by decide +kernel
theorem eval_atom0198 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0198 = (quadB (outer g) ![2,2,1] * g 0 * g 16) := by
  rw [atom0198_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0198_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1635670612800 : Int) atom0198) := by
  rw [SparsePolynomial.eval_scale, eval_atom0198]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0198Coded : CoefficientMerge.Poly := [(16, -8), (40, -12), (64, -16), (88, -16), (112, -16), (136, -16), (160, -16), (184, -16), (208, -16), (232, -16), (256, -16), (280, -16), (304, -16), (328, -16), (352, -16), (376, -16), (400, -16), (401, -16), (402, -14), (403, -10), (404, -2), (405, 2), (406, 10), (407, 18)]
theorem atom0198Coded_decode : atom0198 = SparsePolynomial.decodeCubic 24 atom0198Coded := by decide +kernel
theorem atom0198Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1635670612800 : Int) atom0198Coded) := by
  have h := atom0198_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0198Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0199 : SparsePolynomial.Poly := [([0,0,17], -8), ([0,1,17], -12), ([0,2,17], -16), ([0,3,17], -16), ([0,4,17], -16), ([0,5,17], -16), ([0,6,17], -16), ([0,7,17], -16), ([0,8,17], -16), ([0,9,17], -16), ([0,10,17], -16), ([0,11,17], -16), ([0,12,17], -16), ([0,13,17], -16), ([0,14,17], -16), ([0,15,17], -16), ([0,16,17], -16), ([0,17,17], -16), ([0,17,18], -14), ([0,17,19], -10), ([0,17,20], -2), ([0,17,21], 2), ([0,17,22], 10), ([0,17,23], 18)]
theorem atom0199_data : atom0199 = SparsePolynomial.monoTimes [0,17] 1 base08 := by decide +kernel
theorem eval_atom0199 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0199 = (quadB (outer g) ![2,2,1] * g 0 * g 17) := by
  rw [atom0199_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0199_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1950820502400 : Int) atom0199) := by
  rw [SparsePolynomial.eval_scale, eval_atom0199]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0199Coded : CoefficientMerge.Poly := [(17, -8), (41, -12), (65, -16), (89, -16), (113, -16), (137, -16), (161, -16), (185, -16), (209, -16), (233, -16), (257, -16), (281, -16), (305, -16), (329, -16), (353, -16), (377, -16), (401, -16), (425, -16), (426, -14), (427, -10), (428, -2), (429, 2), (430, 10), (431, 18)]
theorem atom0199Coded_decode : atom0199 = SparsePolynomial.decodeCubic 24 atom0199Coded := by decide +kernel
theorem atom0199Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1950820502400 : Int) atom0199Coded) := by
  have h := atom0199_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0199Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0200 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -16), ([1,1,7], -16), ([1,1,8], -16), ([1,1,9], -16), ([1,1,10], -16), ([1,1,11], -16), ([1,1,12], -16), ([1,1,13], -16), ([1,1,14], -16), ([1,1,15], -16), ([1,1,16], -16), ([1,1,17], -16), ([1,1,18], -14), ([1,1,19], -10), ([1,1,20], -2), ([1,1,21], 2), ([1,1,22], 10), ([1,1,23], 18)]
theorem atom0200_data : atom0200 = SparsePolynomial.monoTimes [1,1] 1 base08 := by decide +kernel
theorem eval_atom0200 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0200 = (quadB (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0200_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0200_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1084379788800 : Int) atom0200) := by
  rw [SparsePolynomial.eval_scale, eval_atom0200]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0200Coded : CoefficientMerge.Poly := [(25, -8), (601, -12), (602, -16), (603, -16), (604, -16), (605, -16), (606, -16), (607, -16), (608, -16), (609, -16), (610, -16), (611, -16), (612, -16), (613, -16), (614, -16), (615, -16), (616, -16), (617, -16), (618, -14), (619, -10), (620, -2), (621, 2), (622, 10), (623, 18)]
theorem atom0200Coded_decode : atom0200 = SparsePolynomial.decodeCubic 24 atom0200Coded := by decide +kernel
theorem atom0200Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1084379788800 : Int) atom0200Coded) := by
  have h := atom0200_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0200Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0201 : SparsePolynomial.Poly := [([0,1,23], -8), ([1,1,23], -12), ([1,2,23], -16), ([1,3,23], -16), ([1,4,23], -16), ([1,5,23], -16), ([1,6,23], -16), ([1,7,23], -16), ([1,8,23], -16), ([1,9,23], -16), ([1,10,23], -16), ([1,11,23], -16), ([1,12,23], -16), ([1,13,23], -16), ([1,14,23], -16), ([1,15,23], -16), ([1,16,23], -16), ([1,17,23], -16), ([1,18,23], -14), ([1,19,23], -10), ([1,20,23], -2), ([1,21,23], 2), ([1,22,23], 10), ([1,23,23], 18)]
theorem atom0201_data : atom0201 = SparsePolynomial.monoTimes [1,23] 1 base08 := by decide +kernel
theorem eval_atom0201 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0201 = (quadB (outer g) ![2,2,1] * g 1 * g 23) := by
  rw [atom0201_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0201_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1242961473600 : Int) atom0201) := by
  rw [SparsePolynomial.eval_scale, eval_atom0201]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0201Coded : CoefficientMerge.Poly := [(47, -8), (623, -12), (647, -16), (671, -16), (695, -16), (719, -16), (743, -16), (767, -16), (791, -16), (815, -16), (839, -16), (863, -16), (887, -16), (911, -16), (935, -16), (959, -16), (983, -16), (1007, -16), (1031, -14), (1055, -10), (1079, -2), (1103, 2), (1127, 10), (1151, 18)]
theorem atom0201Coded_decode : atom0201 = SparsePolynomial.decodeCubic 24 atom0201Coded := by decide +kernel
theorem atom0201Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1242961473600 : Int) atom0201Coded) := by
  have h := atom0201_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0201Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0202 : SparsePolynomial.Poly := [([0,2,23], -8), ([1,2,23], -12), ([2,2,23], -16), ([2,3,23], -16), ([2,4,23], -16), ([2,5,23], -16), ([2,6,23], -16), ([2,7,23], -16), ([2,8,23], -16), ([2,9,23], -16), ([2,10,23], -16), ([2,11,23], -16), ([2,12,23], -16), ([2,13,23], -16), ([2,14,23], -16), ([2,15,23], -16), ([2,16,23], -16), ([2,17,23], -16), ([2,18,23], -14), ([2,19,23], -10), ([2,20,23], -2), ([2,21,23], 2), ([2,22,23], 10), ([2,23,23], 18)]
theorem atom0202_data : atom0202 = SparsePolynomial.monoTimes [2,23] 1 base08 := by decide +kernel
theorem eval_atom0202 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0202 = (quadB (outer g) ![2,2,1] * g 2 * g 23) := by
  rw [atom0202_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0202_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1511620110000 : Int) atom0202) := by
  rw [SparsePolynomial.eval_scale, eval_atom0202]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 2 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0202Coded : CoefficientMerge.Poly := [(71, -8), (647, -12), (1223, -16), (1247, -16), (1271, -16), (1295, -16), (1319, -16), (1343, -16), (1367, -16), (1391, -16), (1415, -16), (1439, -16), (1463, -16), (1487, -16), (1511, -16), (1535, -16), (1559, -16), (1583, -16), (1607, -14), (1631, -10), (1655, -2), (1679, 2), (1703, 10), (1727, 18)]
theorem atom0202Coded_decode : atom0202 = SparsePolynomial.decodeCubic 24 atom0202Coded := by decide +kernel
theorem atom0202Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1511620110000 : Int) atom0202Coded) := by
  have h := atom0202_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0202Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0203 : SparsePolynomial.Poly := [([0,7,8], -8), ([1,7,8], -12), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -16), ([7,8,13], -16), ([7,8,14], -16), ([7,8,15], -16), ([7,8,16], -16), ([7,8,17], -16), ([7,8,18], -14), ([7,8,19], -10), ([7,8,20], -2), ([7,8,21], 2), ([7,8,22], 10), ([7,8,23], 18)]
theorem atom0203_data : atom0203 = SparsePolynomial.monoTimes [7,8] 1 base08 := by decide +kernel
theorem eval_atom0203 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0203 = (quadB (outer g) ![2,2,1] * g 7 * g 8) := by
  rw [atom0203_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0203_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3724897730400 : Int) atom0203) := by
  rw [SparsePolynomial.eval_scale, eval_atom0203]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0203Coded : CoefficientMerge.Poly := [(176, -8), (752, -12), (1328, -16), (1904, -16), (2480, -16), (3056, -16), (3632, -16), (4208, -16), (4232, -16), (4233, -16), (4234, -16), (4235, -16), (4236, -16), (4237, -16), (4238, -16), (4239, -16), (4240, -16), (4241, -16), (4242, -14), (4243, -10), (4244, -2), (4245, 2), (4246, 10), (4247, 18)]
theorem atom0203Coded_decode : atom0203 = SparsePolynomial.decodeCubic 24 atom0203Coded := by decide +kernel
theorem atom0203Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3724897730400 : Int) atom0203Coded) := by
  have h := atom0203_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0203Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0204 : SparsePolynomial.Poly := [([0,7,9], -8), ([1,7,9], -12), ([2,7,9], -16), ([3,7,9], -16), ([4,7,9], -16), ([5,7,9], -16), ([6,7,9], -16), ([7,7,9], -16), ([7,8,9], -16), ([7,9,9], -16), ([7,9,10], -16), ([7,9,11], -16), ([7,9,12], -16), ([7,9,13], -16), ([7,9,14], -16), ([7,9,15], -16), ([7,9,16], -16), ([7,9,17], -16), ([7,9,18], -14), ([7,9,19], -10), ([7,9,20], -2), ([7,9,21], 2), ([7,9,22], 10), ([7,9,23], 18)]
theorem atom0204_data : atom0204 = SparsePolynomial.monoTimes [7,9] 1 base08 := by decide +kernel
theorem eval_atom0204 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0204 = (quadB (outer g) ![2,2,1] * g 7 * g 9) := by
  rw [atom0204_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0204_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (284787224832 : Int) atom0204) := by
  rw [SparsePolynomial.eval_scale, eval_atom0204]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0204Coded : CoefficientMerge.Poly := [(177, -8), (753, -12), (1329, -16), (1905, -16), (2481, -16), (3057, -16), (3633, -16), (4209, -16), (4233, -16), (4257, -16), (4258, -16), (4259, -16), (4260, -16), (4261, -16), (4262, -16), (4263, -16), (4264, -16), (4265, -16), (4266, -14), (4267, -10), (4268, -2), (4269, 2), (4270, 10), (4271, 18)]
theorem atom0204Coded_decode : atom0204 = SparsePolynomial.decodeCubic 24 atom0204Coded := by decide +kernel
theorem atom0204Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (284787224832 : Int) atom0204Coded) := by
  have h := atom0204_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0204Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0205 : SparsePolynomial.Poly := [([0,8,9], -8), ([1,8,9], -12), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -16), ([8,9,13], -16), ([8,9,14], -16), ([8,9,15], -16), ([8,9,16], -16), ([8,9,17], -16), ([8,9,18], -14), ([8,9,19], -10), ([8,9,20], -2), ([8,9,21], 2), ([8,9,22], 10), ([8,9,23], 18)]
theorem atom0205_data : atom0205 = SparsePolynomial.monoTimes [8,9] 1 base08 := by decide +kernel
theorem eval_atom0205 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0205 = (quadB (outer g) ![2,2,1] * g 8 * g 9) := by
  rw [atom0205_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0205_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4217032512000 : Int) atom0205) := by
  rw [SparsePolynomial.eval_scale, eval_atom0205]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0205Coded : CoefficientMerge.Poly := [(201, -8), (777, -12), (1353, -16), (1929, -16), (2505, -16), (3081, -16), (3657, -16), (4233, -16), (4809, -16), (4833, -16), (4834, -16), (4835, -16), (4836, -16), (4837, -16), (4838, -16), (4839, -16), (4840, -16), (4841, -16), (4842, -14), (4843, -10), (4844, -2), (4845, 2), (4846, 10), (4847, 18)]
theorem atom0205Coded_decode : atom0205 = SparsePolynomial.decodeCubic 24 atom0205Coded := by decide +kernel
theorem atom0205Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4217032512000 : Int) atom0205Coded) := by
  have h := atom0205_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0205Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0206 : SparsePolynomial.Poly := [([0,9,10], -8), ([1,9,10], -12), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -16), ([9,10,13], -16), ([9,10,14], -16), ([9,10,15], -16), ([9,10,16], -16), ([9,10,17], -16), ([9,10,18], -14), ([9,10,19], -10), ([9,10,20], -2), ([9,10,21], 2), ([9,10,22], 10), ([9,10,23], 18)]
theorem atom0206_data : atom0206 = SparsePolynomial.monoTimes [9,10] 1 base08 := by decide +kernel
theorem eval_atom0206 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0206 = (quadB (outer g) ![2,2,1] * g 9 * g 10) := by
  rw [atom0206_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0206_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (598889491200 : Int) atom0206) := by
  rw [SparsePolynomial.eval_scale, eval_atom0206]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0206Coded : CoefficientMerge.Poly := [(226, -8), (802, -12), (1378, -16), (1954, -16), (2530, -16), (3106, -16), (3682, -16), (4258, -16), (4834, -16), (5410, -16), (5434, -16), (5435, -16), (5436, -16), (5437, -16), (5438, -16), (5439, -16), (5440, -16), (5441, -16), (5442, -14), (5443, -10), (5444, -2), (5445, 2), (5446, 10), (5447, 18)]
theorem atom0206Coded_decode : atom0206 = SparsePolynomial.decodeCubic 24 atom0206Coded := by decide +kernel
theorem atom0206Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (598889491200 : Int) atom0206Coded) := by
  have h := atom0206_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0206Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0207 : SparsePolynomial.Poly := [([0,9,11], -8), ([1,9,11], -12), ([2,9,11], -16), ([3,9,11], -16), ([4,9,11], -16), ([5,9,11], -16), ([6,9,11], -16), ([7,9,11], -16), ([8,9,11], -16), ([9,9,11], -16), ([9,10,11], -16), ([9,11,11], -16), ([9,11,12], -16), ([9,11,13], -16), ([9,11,14], -16), ([9,11,15], -16), ([9,11,16], -16), ([9,11,17], -16), ([9,11,18], -14), ([9,11,19], -10), ([9,11,20], -2), ([9,11,21], 2), ([9,11,22], 10), ([9,11,23], 18)]
theorem atom0207_data : atom0207 = SparsePolynomial.monoTimes [9,11] 1 base08 := by decide +kernel
theorem eval_atom0207 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0207 = (quadB (outer g) ![2,2,1] * g 9 * g 11) := by
  rw [atom0207_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0207_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2732171321088 : Int) atom0207) := by
  rw [SparsePolynomial.eval_scale, eval_atom0207]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0207Coded : CoefficientMerge.Poly := [(227, -8), (803, -12), (1379, -16), (1955, -16), (2531, -16), (3107, -16), (3683, -16), (4259, -16), (4835, -16), (5411, -16), (5435, -16), (5459, -16), (5460, -16), (5461, -16), (5462, -16), (5463, -16), (5464, -16), (5465, -16), (5466, -14), (5467, -10), (5468, -2), (5469, 2), (5470, 10), (5471, 18)]
theorem atom0207Coded_decode : atom0207 = SparsePolynomial.decodeCubic 24 atom0207Coded := by decide +kernel
theorem atom0207Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2732171321088 : Int) atom0207Coded) := by
  have h := atom0207_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0207Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0208 : SparsePolynomial.Poly := [([0,10,11], -8), ([1,10,11], -12), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -16), ([10,11,13], -16), ([10,11,14], -16), ([10,11,15], -16), ([10,11,16], -16), ([10,11,17], -16), ([10,11,18], -14), ([10,11,19], -10), ([10,11,20], -2), ([10,11,21], 2), ([10,11,22], 10), ([10,11,23], 18)]
theorem atom0208_data : atom0208 = SparsePolynomial.monoTimes [10,11] 1 base08 := by decide +kernel
theorem eval_atom0208 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0208 = (quadB (outer g) ![2,2,1] * g 10 * g 11) := by
  rw [atom0208_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0208_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3522438404496 : Int) atom0208) := by
  rw [SparsePolynomial.eval_scale, eval_atom0208]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0208Coded : CoefficientMerge.Poly := [(251, -8), (827, -12), (1403, -16), (1979, -16), (2555, -16), (3131, -16), (3707, -16), (4283, -16), (4859, -16), (5435, -16), (6011, -16), (6035, -16), (6036, -16), (6037, -16), (6038, -16), (6039, -16), (6040, -16), (6041, -16), (6042, -14), (6043, -10), (6044, -2), (6045, 2), (6046, 10), (6047, 18)]
theorem atom0208Coded_decode : atom0208 = SparsePolynomial.decodeCubic 24 atom0208Coded := by decide +kernel
theorem atom0208Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3522438404496 : Int) atom0208Coded) := by
  have h := atom0208_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0208Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block004 : CoefficientMerge.Poly := [(1, -6506278732800), (2, -9589319308800), (3, -12672359884800), (4, -15755400460800), (5, -11955547296000), (6, -21921481612800), (7, -25004522188800), (8, -28087562764800), (9, -25158822294672), (10, -10598365836432), (15, -631427328000), (16, -13085364902400), (17, -15606564019200), (25, -18434456409600), (26, -27396536428800), (27, -32021097292800), (28, -36645658156800), (29, -30945878409600), (30, -45894779884800), (31, -50519340748800), (32, -55143901612800), (33, -50750790907608), (34, -28910106220248), (35, -13012557465600), (36, -13012557465600), (37, -13012557465600), (38, -13012557465600), (39, -13959698457600), (40, -32640604819200), (41, -36422403494400), (42, -11385987782400), (43, -8132848416000), (44, -1626569683200), (45, 1626569683200), (46, 8132848416000), (47, 4695435360000), (50, -19178638617600), (51, -44523358387200), (52, -50689439539200), (53, -43089733209600), (54, -63021601843200), (55, -69187682995200), (56, -75353764147200), (57, -69496283206944), (58, -40375370290464), (59, -19178638617600), (60, -19178638617600), (61, -19178638617600), (62, -19178638617600), (63, -20441493273600), (64, -45349368422400), (65, -50391766656000), (66, -16781308790400), (67, -11986649136000), (68, -2397329827200), (69, 2397329827200), (70, 11986649136000), (71, 9483007564800), (75, -25344719769600), (76, -56855520691200), (77, -49255814361600), (78, -69187682995200), (79, -75353764147200), (80, -81519845299200), (81, -75662364358944), (82, -46541451442464), (83, -25344719769600), (84, -25344719769600), (85, -25344719769600), (86, -25344719769600), (87, -26607574425600), (88, -51515449574400), (89, -56557847808000), (90, -22176629798400), (91, -15840449856000), (92, -3168089971200), (93, 3168089971200), (94, 15840449856000), (95, 28512809740800), (100, -31510800921600), (101, -55421895513600), (102, -75353764147200), (103, -81519845299200), (104, -87685926451200), (105, -81828445510944), (106, -52707532594464), (107, -31510800921600), (108, -31510800921600), (109, -31510800921600), (110, -31510800921600), (111, -32773655577600), (112, -57681530726400), (113, -62723928960000), (114, -27571950806400), (115, -19694250576000), (116, -3938850115200), (117, 3938850115200), (118, 19694250576000), (119, 35449651036800), (125, -23911094592000), (126, -67754057817600), (127, -73920138969600), (128, -80086220121600), (129, -74228739181344), (130, -45107826264864), (131, -23911094592000), (132, -23911094592000), (133, -23911094592000), (134, -23911094592000), (135, -25173949248000), (136, -50081824396800), (137, -55124222630400), (138, -20922207768000), (139, -14944434120000), (140, -2988886824000), (141, 2988886824000), (142, 14944434120000), (143, 26899981416000), (150, -43842963225600), (151, -93852007603200), (152, -100018088755200), (153, -94160607814944), (154, -65039694898464), (155, -43842963225600), (156, -43842963225600), (157, -43842963225600), (158, -43842963225600), (159, -45105817881600), (160, -70013693030400), (161, -75056091264000), (162, -38362592822400), (163, -27401852016000), (164, -5480370403200), (165, 5480370403200), (166, 27401852016000), (167, 49323333628800), (175, -50009044377600), (176, -135983351750400), (177, -102604986765600), (178, -71205776050464), (179, -50009044377600), (180, -50009044377600), (181, -50009044377600), (182, -50009044377600), (183, -51271899033600), (184, -76179774182400), (185, -81222172416000), (186, -43757913830400), (187, -31255652736000), (188, -6251130547200), (189, 6251130547200), (190, 31255652736000), (191, 56260174924800), (200, -56175125529600), (201, -140229030214944), (202, -77371857202464), (203, -56175125529600), (204, -56175125529600), (205, -56175125529600), (206, -56175125529600), (207, -57437980185600), (208, -82345855334400), (209, -87388253568000), (210, -49153234838400), (211, -35109453456000), (212, -7021890691200), (213, 7021890691200), (214, 35109453456000), (215, 63197016220800), (225, -50317644589344), (226, -76305492191808), (227, -72175015158048), (228, -50317644589344), (229, -50317644589344), (230, -50317644589344), (231, -51580499245344), (232, -93699603217512), (233, -94827474174312), (234, -50072225510340), (235, -59463543625596), (236, -21065000980716), (237, -38595890464164), (238, 10692594217140), (239, 20344511852100), (250, -21196731672864), (251, -62786402296992), (252, -52582018291704), (253, -51429149395272), (254, -48958209108072), (255, -44053371828072), (256, -65749182602472), (257, -65096331847272), (258, -21883666588740), (259, -36140873226876), (260, -9888447333996), (261, -31651607346084), (262, -30196674387660), (263, -33096629994300), (276, -13410163388160), (277, -28878655029840), (278, -30305857287024), (279, -22594389965424), (280, -42254330842224), (281, -39565610189424), (283, -14865625585008), (285, -22959047531376), (286, -66233819625600), (287, -58640889745152), (301, -13410163388160), (302, -30032801900640), (303, -23051397574944), (304, -40420320368544), (305, -35440581632544), (307, -3849469782048), (309, -2742673402656), (310, -54761022858240), (311, -41645894349312), (326, -13410163388160), (327, -28982047227840), (328, -46517144184000), (329, -38991239179200), (331, -3604906166400), (334, -46871099755200), (335, -32939286811200), (351, -13902257900160), (352, -54658024727040), (353, -45135536846400), (355, -4785246635400), (358, -35608705889400), (359, -19727140771800), (375, -1262854656000), (376, -39302227560960), (377, -48849924211200), (378, -1104997824000), (379, -789284160000), (380, -157856832000), (381, 157856832000), (382, -18344413584000), (383, 1420711488000), (400, -26170729804800), (401, -72432016742400), (402, -22899388579200), (403, -16356706128000), (404, -3271341225600), (405, 3271341225600), (406, 16356706128000), (407, 29442071030400), (425, -31213128038400), (426, -27311487033600), (427, -19508205024000), (428, -3901641004800), (429, 3901641004800), (430, 19508205024000), (431, 35114769043200), (550, -309471876000), (601, -13012557465600), (602, -17350076620800), (603, -17350076620800), (604, -17350076620800), (605, -17350076620800), (606, -17350076620800), (607, -17350076620800), (608, -17350076620800), (609, -17350076620800), (610, -17350076620800), (611, -17350076620800), (612, -17350076620800), (613, -17350076620800), (614, -17350076620800), (615, -17350076620800), (616, -17350076620800), (617, -17350076620800), (618, -15181317043200), (619, -10843797888000), (620, -2168759577600), (621, 2168759577600), (622, 10843797888000), (623, 4603298515200), (647, -38026824897600), (671, -19887383577600), (695, -19887383577600), (719, -19887383577600), (743, -19887383577600), (752, -44698772764800), (753, -3417446697984), (767, -19887383577600), (777, -50604390144000), (791, -19887383577600), (802, -7186673894400), (803, -32786055853056), (808, -34422457646736), (809, -26593403093136), (810, -12088572989328), (811, -56030031514512), (812, -29550590814096), (813, -89771192075664), (814, -41511867302400), (815, -92413060199424), (827, -69089587630272), (828, -62770573237680), (829, -60464835444816), (830, -55522954870416), (831, -43187570998416), (832, -36763442249616), (833, -25372944272016), (834, -6673052749968), (835, -45785831862672), (836, -14477711749776), (837, -68602397610384), (838, -86889263366400), (839, -133773289830144), (852, -26820326776320), (853, -57757310059680), (854, -60611714574048), (855, -42663070618848), (856, -32167202074848), (857, -16704964302048), (859, -29731251170016), (861, -45918095062752), (862, -132467639251200), (863, -137169163067904), (877, -26820326776320), (878, -60065603801280), (879, -43577085837888), (880, -28499181127488), (881, -8454907188288), (883, -7698939564096), (885, -5485346805312), (886, -109522045716480), (887, -103179172276224), (902, -26820326776320), (903, -55438385143680), (904, -40692828758400), (905, -15556222281600), (907, -7209812332800), (910, -93742199510400), (911, -85765957200000), (927, -25278806488320), (928, -56974589844480), (929, -27844817616000), (931, -9570493270800), (934, -71217411778800), (935, -59341665121200), (952, -23737286200320), (953, -32747883033600), (958, -38267395488000), (959, -19887383577600), (977, -30096317798400), (983, -19887383577600), (1007, -19887383577600), (1031, -17401460630400), (1055, -12429614736000), (1079, -2485922947200), (1103, 2485922947200), (1126, -618943752000), (1127, 12429614736000), (1151, 22373306524800), (1223, -24185921760000), (1247, -24185921760000), (1271, -24185921760000), (1295, -24185921760000), (1319, -24185921760000), (1328, -59598363686400), (1329, -4556595597312), (1343, -24185921760000), (1353, -67472520192000), (1367, -24185921760000), (1378, -9582231859200), (1379, -43714741137408), (1384, -68844915293472), (1385, -53186806186272), (1386, -24177145978656), (1387, -112060063029024), (1388, -59101181628192), (1389, -179542384151328), (1390, -83023734604800), (1391, -169237275003648), (1403, -109999668024576), (1404, -125541146475360), (1405, -120929670889632), (1406, -111045909740832), (1407, -86375141996832), (1408, -73526884499232), (1409, -50745888544032), (1410, -13346105499936), (1411, -91571663725344), (1412, -28955423499552), (1413, -137204795220768), (1414, -173778526732800), (1415, -251957734265088), (1428, -53640653552640), (1429, -115514620119360), (1430, -121223429148096), (1431, -85326141237696), (1432, -64334404149696), (1433, -33409928604096), (1435, -59462502340032), (1437, -91836190125504), (1438, -264935278502400), (1439, -258749480740608), (1453, -53640653552640), (1454, -120131207602560), (1455, -87154171675776), (1456, -56998362254976), (1457, -16909814376576), (1459, -15397879128192), (1461, -10970693610624), (1462, -219044091432960), (1463, -190769499157248), (1478, -53640653552640), (1479, -110876770287360), (1480, -81385657516800), (1481, -31112444563200), (1483, -14419624665600), (1486, -187484399020800), (1487, -155943069004800), (1503, -50557612976640), (1504, -113949179688960), (1505, -55689635232000), (1507, -19140986541600), (1510, -142434823557600), (1511, -103094484847200), (1528, -47474572400640), (1529, -65495766067200), (1534, -76534790976000), (1535, -24185921760000), (1553, -60192635596800), (1559, -24185921760000), (1583, -24185921760000), (1607, -21162681540000), (1631, -15116201100000), (1655, -3023240220000), (1679, 3023240220000), (1702, -1237887504000), (1703, 15116201100000), (1727, 27209161980000), (1904, -59598363686400), (1905, -4556595597312), (1929, -67472520192000), (1954, -9582231859200), (1955, -43714741137408), (1960, -68844915293472), (1961, -53186806186272), (1962, -24177145978656), (1963, -112060063029024), (1964, -59101181628192), (1965, -179542384151328), (1966, -83023734604800), (1967, -145051353243648), (1979, -109999668024576), (1980, -125541146475360), (1981, -120929670889632), (1982, -111045909740832), (1983, -86375141996832), (1984, -73526884499232), (1985, -50745888544032), (1986, -13346105499936), (1987, -91571663725344), (1988, -28955423499552), (1989, -137204795220768), (1990, -173778526732800), (1991, -227771812505088), (2004, -53640653552640), (2005, -115514620119360), (2006, -121223429148096), (2007, -85326141237696), (2008, -64334404149696), (2009, -33409928604096), (2011, -59462502340032), (2013, -91836190125504), (2014, -264935278502400), (2015, -234563558980608), (2029, -53640653552640), (2030, -120131207602560), (2031, -87154171675776), (2032, -56998362254976), (2033, -16909814376576), (2035, -15397879128192), (2037, -10970693610624), (2038, -219044091432960), (2039, -166583577397248), (2054, -53640653552640), (2055, -110876770287360), (2056, -81385657516800), (2057, -31112444563200), (2059, -14419624665600), (2062, -187484399020800), (2063, -131757147244800), (2079, -50557612976640), (2080, -113949179688960), (2081, -55689635232000), (2083, -19140986541600), (2086, -142434823557600), (2087, -78908563087200), (2104, -47474572400640), (2105, -65495766067200), (2110, -76534790976000), (2129, -60192635596800), (2278, -1237887504000), (2480, -59598363686400), (2481, -4556595597312), (2505, -67472520192000), (2530, -9582231859200), (2531, -43714741137408), (2536, -68844915293472), (2537, -53186806186272), (2538, -24177145978656), (2539, -112060063029024), (2540, -59101181628192), (2541, -179542384151328), (2542, -83023734604800), (2543, -145051353243648), (2555, -109999668024576), (2556, -125541146475360), (2557, -120929670889632), (2558, -111045909740832), (2559, -86375141996832), (2560, -73526884499232), (2561, -50745888544032), (2562, -13346105499936), (2563, -91571663725344), (2564, -28955423499552), (2565, -137204795220768), (2566, -173778526732800), (2567, -227771812505088), (2580, -53640653552640), (2581, -115514620119360), (2582, -121223429148096), (2583, -85326141237696), (2584, -64334404149696), (2585, -33409928604096), (2587, -59462502340032), (2589, -91836190125504), (2590, -264935278502400), (2591, -234563558980608), (2605, -53640653552640), (2606, -120131207602560), (2607, -87154171675776), (2608, -56998362254976), (2609, -16909814376576), (2611, -15397879128192), (2613, -10970693610624), (2614, -219044091432960), (2615, -166583577397248), (2630, -53640653552640), (2631, -110876770287360), (2632, -81385657516800), (2633, -31112444563200), (2635, -14419624665600), (2638, -187484399020800), (2639, -131757147244800), (2655, -50557612976640), (2656, -113949179688960), (2657, -55689635232000), (2659, -19140986541600), (2662, -142434823557600), (2663, -78908563087200), (2680, -47474572400640), (2681, -65495766067200), (2686, -76534790976000), (2705, -60192635596800), (2854, -1237887504000), (3056, -59598363686400), (3057, -4556595597312), (3081, -67472520192000), (3106, -9582231859200), (3107, -43714741137408), (3112, -68844915293472), (3113, -53186806186272), (3114, -24177145978656), (3115, -112060063029024), (3116, -59101181628192), (3117, -179542384151328), (3118, -83023734604800), (3119, -145051353243648), (3131, -109999668024576), (3132, -125541146475360), (3133, -120929670889632), (3134, -111045909740832), (3135, -86375141996832), (3136, -73526884499232), (3137, -50745888544032), (3138, -13346105499936), (3139, -91571663725344), (3140, -28955423499552), (3141, -137204795220768), (3142, -173778526732800), (3143, -227771812505088), (3156, -53640653552640), (3157, -115514620119360), (3158, -121223429148096), (3159, -85326141237696), (3160, -64334404149696), (3161, -33409928604096), (3163, -59462502340032), (3165, -91836190125504), (3166, -264935278502400), (3167, -234563558980608), (3181, -53640653552640), (3182, -120131207602560), (3183, -87154171675776), (3184, -56998362254976), (3185, -16909814376576), (3187, -15397879128192), (3189, -10970693610624), (3190, -219044091432960), (3191, -166583577397248), (3206, -53640653552640), (3207, -110876770287360), (3208, -81385657516800), (3209, -31112444563200), (3211, -14419624665600), (3214, -187484399020800), (3215, -131757147244800), (3231, -50557612976640), (3232, -113949179688960), (3233, -55689635232000), (3235, -19140986541600), (3238, -142434823557600), (3239, -78908563087200), (3256, -47474572400640), (3257, -65495766067200), (3262, -76534790976000), (3281, -60192635596800), (3430, -1237887504000), (3632, -59598363686400), (3633, -4556595597312), (3657, -67472520192000), (3682, -9582231859200), (3683, -43714741137408), (3688, -68844915293472), (3689, -53186806186272), (3690, -24177145978656), (3691, -112060063029024), (3692, -59101181628192), (3693, -179542384151328), (3694, -83023734604800), (3695, -145051353243648), (3707, -109999668024576), (3708, -125541146475360), (3709, -120929670889632), (3710, -111045909740832), (3711, -86375141996832), (3712, -73526884499232), (3713, -50745888544032), (3714, -13346105499936), (3715, -91571663725344), (3716, -28955423499552), (3717, -137204795220768), (3718, -173778526732800), (3719, -227771812505088), (3732, -53640653552640), (3733, -115514620119360), (3734, -121223429148096), (3735, -85326141237696), (3736, -64334404149696), (3737, -33409928604096), (3739, -59462502340032), (3741, -91836190125504), (3742, -264935278502400), (3743, -234563558980608), (3757, -53640653552640), (3758, -120131207602560), (3759, -87154171675776), (3760, -56998362254976), (3761, -16909814376576), (3763, -15397879128192), (3765, -10970693610624), (3766, -219044091432960), (3767, -166583577397248), (3782, -53640653552640), (3783, -110876770287360), (3784, -81385657516800), (3785, -31112444563200), (3787, -14419624665600), (3790, -187484399020800), (3791, -131757147244800), (3807, -50557612976640), (3808, -113949179688960), (3809, -55689635232000), (3811, -19140986541600), (3814, -142434823557600), (3815, -78908563087200), (3832, -47474572400640), (3833, -65495766067200), (3838, -76534790976000), (3857, -60192635596800), (4006, -1237887504000), (4208, -59598363686400), (4209, -4556595597312), (4232, -59598363686400), (4233, -131627479475712), (4234, -59598363686400), (4235, -59598363686400), (4236, -59598363686400), (4237, -59598363686400), (4238, -59598363686400), (4239, -59598363686400), (4240, -59598363686400), (4241, -59598363686400), (4242, -52148568225600), (4243, -37248977304000), (4244, -7449795460800), (4245, 7449795460800), (4246, 37248977304000), (4247, 67048159147200), (4257, -4556595597312), (4258, -14138827456512), (4259, -48271336734720), (4260, -4556595597312), (4261, -4556595597312), (4262, -4556595597312), (4263, -4556595597312), (4264, -73401510890784), (4265, -57743401783584), (4266, -28164167126304), (4267, -114907935277344), (4268, -59670756077856), (4269, -178972809701664), (4270, -80175862356480), (4271, -139925183196672), (4283, -109999668024576), (4284, -125541146475360), (4285, -120929670889632), (4286, -111045909740832), (4287, -86375141996832), (4288, -73526884499232), (4289, -50745888544032), (4290, -13346105499936), (4291, -91571663725344), (4292, -28955423499552), (4293, -137204795220768), (4294, -173778526732800), (4295, -227771812505088), (4308, -53640653552640), (4309, -115514620119360), (4310, -121223429148096), (4311, -85326141237696), (4312, -64334404149696), (4313, -33409928604096), (4315, -59462502340032), (4317, -91836190125504), (4318, -264935278502400), (4319, -234563558980608), (4333, -53640653552640), (4334, -120131207602560), (4335, -87154171675776), (4336, -56998362254976), (4337, -16909814376576), (4339, -15397879128192), (4341, -10970693610624), (4342, -219044091432960), (4343, -166583577397248), (4358, -53640653552640), (4359, -110876770287360), (4360, -81385657516800), (4361, -31112444563200), (4363, -14419624665600), (4366, -187484399020800), (4367, -131757147244800), (4383, -50557612976640), (4384, -113949179688960), (4385, -55689635232000), (4387, -19140986541600), (4390, -142434823557600), (4391, -78908563087200), (4408, -47474572400640), (4409, -65495766067200), (4414, -76534790976000), (4433, -60192635596800), (4582, -1237887504000), (4809, -67472520192000), (4833, -67472520192000), (4834, -77054752051200), (4835, -111187261329408), (4836, -67472520192000), (4837, -67472520192000), (4838, -67472520192000), (4839, -67472520192000), (4840, -136317435485472), (4841, -120659326378272), (4842, -83215601146656), (4843, -154230388149024), (4844, -67535246652192), (4845, -171108319127328), (4846, -40853409484800), (4847, -69144768027648), (4859, -109999668024576), (4860, -125541146475360), (4861, -120929670889632), (4862, -111045909740832), (4863, -86375141996832), (4864, -73526884499232), (4865, -50745888544032), (4866, -13346105499936), (4867, -91571663725344), (4868, -28955423499552), (4869, -137204795220768), (4870, -173778526732800), (4871, -227771812505088), (4884, -53640653552640), (4885, -115514620119360), (4886, -121223429148096), (4887, -85326141237696), (4888, -64334404149696), (4889, -33409928604096), (4891, -59462502340032), (4893, -91836190125504), (4894, -264935278502400), (4895, -234563558980608), (4909, -53640653552640), (4910, -120131207602560), (4911, -87154171675776), (4912, -56998362254976), (4913, -16909814376576), (4915, -15397879128192), (4917, -10970693610624), (4918, -219044091432960), (4919, -166583577397248), (4934, -53640653552640), (4935, -110876770287360), (4936, -81385657516800), (4937, -31112444563200), (4939, -14419624665600), (4942, -187484399020800), (4943, -131757147244800), (4959, -50557612976640), (4960, -113949179688960), (4961, -55689635232000), (4963, -19140986541600), (4966, -142434823557600), (4967, -78908563087200), (4984, -47474572400640), (4985, -65495766067200), (4990, -76534790976000), (5009, -60192635596800), (5158, -1237887504000), (5410, -9582231859200), (5411, -43714741137408), (5416, -68844915293472), (5417, -53186806186272), (5418, -24177145978656), (5419, -112060063029024), (5420, -59101181628192), (5421, -179542384151328), (5422, -83023734604800), (5423, -145051353243648), (5434, -9582231859200), (5435, -163296641021184), (5436, -135123378334560), (5437, -130511902748832), (5438, -120628141600032), (5439, -95957373856032), (5440, -151954031651904), (5441, -113514926589504), (5442, -45907704355392), (5443, -209620621666368), (5444, -89254384110144), (5445, -315549400389696), (5446, -250813366425600), (5447, -362043154907136), (5459, -43714741137408), (5460, -97355394690048), (5461, -159229361256768), (5462, -164938170285504), (5463, -129040882375104), (5464, -176894060580576), (5465, -130311475927776), (5466, -62427544473888), (5467, -198844278579936), (5468, -64565524270368), (5469, -265914231634656), (5470, -320637299896320), (5471, -330435828444672), (5485, -53640653552640), (5486, -120131207602560), (5487, -87154171675776), (5488, -125843277548448), (5489, -70096620562848), (5490, -24177145978656), (5491, -127457942157216), (5492, -59101181628192), (5493, -190513077761952), (5494, -302067826037760), (5495, -311634930640896), (5510, -53640653552640), (5511, -110876770287360), (5512, -150230572810272), (5513, -84299250749472), (5514, -24177145978656), (5515, -126479687694624), (5516, -59101181628192), (5517, -179542384151328), (5518, -270508133625600), (5519, -276808500488448), (5535, -50557612976640), (5536, -182794094982432), (5537, -108876441418272), (5538, -24177145978656), (5539, -131201049570624), (5540, -59101181628192), (5541, -179542384151328), (5542, -225458558162400), (5543, -223959916330848), (5560, -116319487694112), (5561, -118682572253472), (5562, -24177145978656), (5563, -112060063029024), (5564, -59101181628192), (5565, -179542384151328), (5566, -159558525580800), (5567, -145051353243648), (5584, -68844915293472), (5585, -182224357076544), (5586, -58599603625392), (5587, -112060063029024), (5588, -24678723981456), (5589, -127908697681224), (5590, -14178819311328), (5591, -67600823538492), (5609, -53186806186272), (5610, -50770549071792), (5611, -112060063029024), (5612, -32507778535056), (5613, -139652279511624), (5614, -29836928418528), (5615, -85216196284092), (5634, -12088572989328), (5635, -56030031514512), (5636, -17462017824768), (5637, -71638332591672), (5638, -17334721323744), (5639, -45326387395836), (5660, 56030031514512), (5661, 84045047271768), (5662, 112060063029024), (5663, 126067570907652), (5684, 29550590814096), (5685, 134097078296808), (5686, 100613048930592), (5687, 139014505953540), (5709, 134656788113496), (5710, 241810185104928), (5711, 310773697102980), (5734, 81785847100800), (5735, 238453054674048), (5759, 163182772399104), (6011, -109999668024576), (6012, -125541146475360), (6013, -120929670889632), (6014, -111045909740832), (6015, -86375141996832), (6016, -73526884499232), (6017, -50745888544032), (6018, -13346105499936), (6019, -91571663725344), (6020, -28955423499552), (6021, -137204795220768), (6022, -173778526732800), (6023, -227771812505088), (6035, -109999668024576), (6036, -289181468052576), (6037, -346443959033568), (6038, -342269006913504), (6039, -281700951259104), (6040, -247860956673504), (6041, -194155485172704), (6042, -89480569939200), (6043, -186258550110336), (6044, -9179973532224), (6045, -181765618372800), (6046, -349848767637600), (6047, -338585744958048), (6060, -125541146475360), (6061, -300111470917632), (6062, -356718263818752), (6063, -299070460147968), (6064, -256066393229568), (6065, -193196849395968), (6066, -76116678737616), (6067, -106969542853536), (6068, 33815149738128), (6069, -54019628974872), (6070, -267281471690400), (6071, -253121600117556), (6085, -120929670889632), (6086, -285616234183104), (6087, -318181583173824), (6088, -275842212905664), (6089, -202788003996864), (6090, -73810940944752), (6091, -105991288390944), (6092, 31509411945264), (6093, -46507542053544), (6094, -240333254863968), (6095, -223483079999052), (6110, -111045909740832), (6111, -247978664714304), (6112, -298521973929024), (6113, -217481433516864), (6114, -68869060370352), (6115, -110712650266944), (6116, 26567531370864), (6117, -53920362915144), (6118, -205167440549568), (6119, -181753727133852), (6135, -86375141996832), (6136, -207376598896704), (6137, -202616796608064), (6138, -56533676498352), (6139, -91571663725344), (6140, 14232147498864), (6141, -72423438723144), (6142, -163938175711968), (6143, -130599777758652), (6160, -73526884499232), (6161, -184465408640064), (6162, -50109547749552), (6163, -91571663725344), (6164, 7808018750064), (6165, -82059631846344), (6166, -100251642233568), (6167, -145054067443452), (6185, -50745888544032), (6186, -38719049771952), (6187, -91571663725344), (6188, -3582479227536), (6189, -99145378812744), (6190, -123032638188768), (6191, -170682687893052), (6210, -6673052749968), (6211, -45785831862672), (6212, -7804658999808), (6213, -58592818485432), (6214, -73543157866464), (6215, -98871537565116), (6236, 45785831862672), (6237, 68678747794008), (6238, 91571663725344), (6239, 103018121691012), (6260, 14477711749776), (6261, 90318965235048), (6262, 115844686865952), (6263, 146460757689540), (6285, 102903596415576), (6286, 267538690270368), (6287, 325184254002180), (6310, 172540639228800), (6311, 423272655079488), (6335, 256243289068224), (6612, -53640653552640), (6613, -115514620119360), (6614, -121223429148096), (6615, -85326141237696), (6616, -64334404149696), (6617, -33409928604096), (6619, -59462502340032), (6621, -91836190125504), (6622, -264935278502400), (6623, -234563558980608), (6636, -53640653552640), (6637, -222795927224640), (6638, -294995290303296), (6639, -226120966466112), (6640, -174973419957312), (6641, -103960396533312), (6642, -26820326776320), (6643, -74860381468224), (6644, 26820326776320), (6645, -62576393571648), (6646, -430338716382720), (6647, -340801401131136), (6661, -115514620119360), (6662, -290378702820096), (6663, -311717531644416), (6664, -261234681785856), (6665, -180036993286656), (6666, -57757310059680), (6667, -73882127005632), (6668, 57757310059680), (6669, -5200225035984), (6670, -336905057403840), (6671, -236366758591128), (6686, -121223429148096), (6687, -257107183362432), (6688, -299507012986752), (6689, -210322992984192), (6690, -60611714574048), (6691, -78603488881632), (6692, 60611714574048), (6693, -918618264432), (6694, -286146672911904), (6695, -177095764276200), (6711, -85326141237696), (6712, -197135117788032), (6713, -184231835908992), (6714, -42663070618848), (6715, -59462502340032), (6716, 42663070618848), (6717, -27841584197232), (6718, -256143928240704), (6719, -138571650088200), (6736, -64334404149696), (6737, -157936968350592), (6738, -32167202074848), (6739, -59462502340032), (6740, 32167202074848), (6741, -43585387013232), (6742, -200600874352704), (6743, -162187354312200), (6761, -33409928604096), (6762, -16704964302048), (6763, -59462502340032), (6764, 16704964302048), (6765, -66778743672432), (6766, -231525349898304), (6767, -196977389301000), (6787, -29731251170016), (6789, -45918095062752), (6790, -132467639251200), (6791, -117281779490304), (6812, 29731251170016), (6813, 44596876755024), (6814, 59462502340032), (6815, 66895315132536), (6837, 45918095062752), (6838, 132467639251200), (6839, 117281779490304), (6861, 68877142594128), (6862, 290537649002304), (6863, 279238383126648), (6886, 263697390998400), (6887, 532615747295808), (6911, 263884003853184), (7213, -53640653552640), (7214, -120131207602560), (7215, -87154171675776), (7216, -56998362254976), (7217, -16909814376576), (7219, -15397879128192), (7221, -10970693610624), (7222, -219044091432960), (7223, -166583577397248), (7237, -53640653552640), (7238, -227412514707840), (7239, -251671595515776), (7240, -192024673324416), (7241, -101662912492416), (7242, -26820326776320), (7243, -29817503793792), (7244, 26820326776320), (7245, 29259796553856), (7246, -352887836901120), (7247, -237994989395328), (7262, -120131207602560), (7263, -257842992254976), (7264, -291078749546496), (7265, -192730657211136), (7266, -60065603801280), (7267, -34538865669792), (7268, 60065603801280), (7269, 79127712091296), (7270, -241347707388000), (7271, -110344531931568), (7287, -87154171675776), (7288, -191627106331392), (7289, -169559752119552), (7290, -43577085837888), (7291, -15397879128192), (7292, 43577085837888), (7293, 54394935146208), (7294, -208424710733184), (7295, -68535134262000), (7312, -56998362254976), (7313, -134100812228352), (7314, -28499181127488), (7315, -15397879128192), (7316, 28499181127488), (7317, 31778078080608), (7318, -162045729177984), (7319, -102460419860400), (7337, -16909814376576), (7338, -8454907188288), (7339, -15397879128192), (7340, 8454907188288), (7341, 1711667171808), (7342, -202134277056384), (7343, -147560036223600), (7363, -7698939564096), (7365, -5485346805312), (7366, -109522045716480), (7367, -83291788698624), (7388, 7698939564096), (7389, 11548409346144), (7390, 15397879128192), (7391, 17322614019216), (7413, 5485346805312), (7414, 109522045716480), (7415, 83291788698624), (7437, 8228020207968), (7438, 175253762185344), (7439, 137279713359888), (7462, 217806203928960), (7463, 413008180259328), (7487, 187406524571904), (7814, -53640653552640), (7815, -110876770287360), (7816, -81385657516800), (7817, -31112444563200), (7819, -14419624665600), (7822, -187484399020800), (7823, -131757147244800), (7838, -53640653552640), (7839, -215075036816640), (7840, -248975490758400), (7841, -140442733347840), (7842, -26820326776320), (7843, -33560611207200), (7844, 26820326776320), (7845, 40230490164480), (7846, -276278569025760), (7847, -150319975085280), (7863, -110876770287360), (7864, -239737000204800), (7865, -207484980917760), (7866, -55438385143680), (7867, -14419624665600), (7868, 55438385143680), (7869, 83157577715520), (7870, -153142419709440), (7871, -7020780671520), (7888, -81385657516800), (7889, -172690737676800), (7890, -40692828758400), (7891, -14419624665600), (7892, 40692828758400), (7893, 61039243137600), (7894, -106098741504000), (7895, -40198282538400), (7913, -31112444563200), (7914, -15556222281600), (7915, -14419624665600), (7916, 15556222281600), (7917, 23334333422400), (7918, -156371954457600), (7919, -96755647111200), (7939, -7209812332800), (7942, -93742199510400), (7943, -65878573622400), (7964, 7209812332800), (7965, 10814718499200), (7966, 14419624665600), (7967, 16222077748800), (7990, 93742199510400), (7991, 65878573622400), (8014, 140613299265600), (8015, 98817860433600), (8038, 186246511516800), (8039, 342677096143200), (8063, 148226790650400), (8415, -50557612976640), (8416, -113949179688960), (8417, -55689635232000), (8419, -19140986541600), (8422, -142434823557600), (8423, -78908563087200), (8439, -50557612976640), (8440, -211981365066240), (8441, -171743014275840), (8442, -25278806488320), (8443, -19140986541600), (8444, 25278806488320), (8445, 37918209732480), (8446, -168412001556960), (8447, -22031248488480), (8464, -113949179688960), (8465, -229831450517760), (8466, -56974589844480), (8467, -19140986541600), (8468, 56974589844480), (8469, 85461884766720), (8470, -28485643868640), (8471, 49284264062880), (8489, -55689635232000), (8490, -27844817616000), (8491, -19140986541600), (8492, 27844817616000), (8493, 41767226424000), (8494, -86745188325600), (8495, -16257723451200), (8515, -9570493270800), (8518, -71217411778800), (8519, -39454281543600), (8540, 9570493270800), (8541, 14355739906200), (8542, 19140986541600), (8543, 21533609859300), (8566, 71217411778800), (8567, 39454281543600), (8590, 106826117668200), (8591, 59181422315400), (8614, 141196936053600), (8615, 239147739589500), (8639, 88772133473100), (9016, -47474572400640), (9017, -65495766067200), (9022, -76534790976000), (9040, -47474572400640), (9041, -173162974064640), (9042, -23737286200320), (9044, 23737286200320), (9045, 35605929300480), (9046, -29060218575360), (9047, 53408893950720), (9065, -65495766067200), (9066, -32747883033600), (9068, 32747883033600), (9069, 49121824550400), (9070, -11039024908800), (9071, 73682736825600), (9094, -38267395488000), (9142, 38267395488000), (9166, 57401093232000), (9190, 75296903472000), (9191, 86101639848000), (9617, -60192635596800), (9641, -60192635596800), (9642, -30096317798400), (9644, 30096317798400), (9645, 45144476697600), (9646, 60192635596800), (9647, 67716715046400), (9766, -1237887504000), (10342, -1237887504000), (10918, -618943752000), (12070, 618943752000), (12646, 928415628000), (13222, 1237887504000), (13223, 1392623442000)]
theorem block004_data : block004 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4302807205842 : Int) atom0129Coded) (CoefficientMerge.scale (3324175386642 : Int) atom0130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1511071623666 : Int) atom0131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7003753939314 : Int) atom0132Coded) (CoefficientMerge.scale (3693823851762 : Int) atom0133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11221399009458 : Int) atom0134Coded) (CoefficientMerge.scale (5188983412800 : Int) atom0135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9065709577728 : Int) atom0136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3352540847040 : Int) atom0137Coded) (CoefficientMerge.scale (7846321654710 : Int) atom0138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7558104430602 : Int) atom0139Coded) (CoefficientMerge.scale (6940369358802 : Int) atom0140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5398446374802 : Int) atom0141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4595430281202 : Int) atom0142Coded) (CoefficientMerge.scale (3171618034002 : Int) atom0143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (834131593746 : Int) atom0144Coded) (CoefficientMerge.scale (5723228982834 : Int) atom0145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1809713968722 : Int) atom0146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8575299701298 : Int) atom0147Coded) (CoefficientMerge.scale (10861157920800 : Int) atom0148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14235738281568 : Int) atom0149Coded) (CoefficientMerge.scale (3352540847040 : Int) atom0150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7219663757460 : Int) atom0151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7576464321756 : Int) atom0152Coded) (CoefficientMerge.scale (5332883827356 : Int) atom0153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4020900259356 : Int) atom0154Coded) (CoefficientMerge.scale (2088120537756 : Int) atom0155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3716406396252 : Int) atom0156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5739761882844 : Int) atom0157Coded) (CoefficientMerge.scale (16558454906400 : Int) atom0158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14660222436288 : Int) atom0159Coded) (CoefficientMerge.scale (3352540847040 : Int) atom0160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7508200475160 : Int) atom0161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5447135729736 : Int) atom0162Coded) (CoefficientMerge.scale (3562397640936 : Int) atom0163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1056863398536 : Int) atom0164Coded) (CoefficientMerge.scale (962367445512 : Int) atom0165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (685668350664 : Int) atom0166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13690255714560 : Int) atom0167Coded) (CoefficientMerge.scale (10411473587328 : Int) atom0168Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3352540847040 : Int) atom0169Coded) (CoefficientMerge.scale (6929798142960 : Int) atom0170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5086603594800 : Int) atom0171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1944527785200 : Int) atom0172Coded) (CoefficientMerge.scale (901226541600 : Int) atom0173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11717774938800 : Int) atom0174Coded) (CoefficientMerge.scale (8234821702800 : Int) atom0175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3159850811040 : Int) atom0176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7121823730560 : Int) atom0177Coded) (CoefficientMerge.scale (3480602202000 : Int) atom0178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1196311658850 : Int) atom0179Coded) (CoefficientMerge.scale (8902176472350 : Int) atom0180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4931785192950 : Int) atom0181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2967160775040 : Int) atom0182Coded) (CoefficientMerge.scale (4093485379200 : Int) atom0183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4783424436000 : Int) atom0184Coded) (CoefficientMerge.scale (3762039724800 : Int) atom0185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77367969000 : Int) atom0186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (813284841600 : Int) atom0187Coded) (CoefficientMerge.scale (1198664913600 : Int) atom0188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1584044985600 : Int) atom0189Coded) (CoefficientMerge.scale (1969425057600 : Int) atom0190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1494443412000 : Int) atom0191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2740185201600 : Int) atom0192Coded) (CoefficientMerge.scale (3125565273600 : Int) atom0193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3510945345600 : Int) atom0194Coded) (CoefficientMerge.scale (3144852786834 : Int) atom0195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1324795729554 : Int) atom0196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (78928416000 : Int) atom0197Coded) (CoefficientMerge.scale (1635670612800 : Int) atom0198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1950820502400 : Int) atom0199Coded) (CoefficientMerge.scale (1084379788800 : Int) atom0200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1242961473600 : Int) atom0201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1511620110000 : Int) atom0202Coded) (CoefficientMerge.scale (3724897730400 : Int) atom0203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (284787224832 : Int) atom0204Coded) (CoefficientMerge.scale (4217032512000 : Int) atom0205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (598889491200 : Int) atom0206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2732171321088 : Int) atom0207Coded) (CoefficientMerge.scale (3522438404496 : Int) atom0208Coded)))))))) := by decide +kernel
theorem block004_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block004 := by
  rw [block004_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0129Coded_nonneg g hg hA hB) (atom0130Coded_nonneg g hg hA hB)) (add_nonneg (atom0131Coded_nonneg g hg hA hB) (add_nonneg (atom0132Coded_nonneg g hg hA hB) (atom0133Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0134Coded_nonneg g hg hA hB) (atom0135Coded_nonneg g hg hA hB)) (add_nonneg (atom0136Coded_nonneg g hg hA hB) (add_nonneg (atom0137Coded_nonneg g hg hA hB) (atom0138Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0139Coded_nonneg g hg hA hB) (atom0140Coded_nonneg g hg hA hB)) (add_nonneg (atom0141Coded_nonneg g hg hA hB) (add_nonneg (atom0142Coded_nonneg g hg hA hB) (atom0143Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0144Coded_nonneg g hg hA hB) (atom0145Coded_nonneg g hg hA hB)) (add_nonneg (atom0146Coded_nonneg g hg hA hB) (add_nonneg (atom0147Coded_nonneg g hg hA hB) (atom0148Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0149Coded_nonneg g hg hA hB) (atom0150Coded_nonneg g hg hA hB)) (add_nonneg (atom0151Coded_nonneg g hg hA hB) (add_nonneg (atom0152Coded_nonneg g hg hA hB) (atom0153Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0154Coded_nonneg g hg hA hB) (atom0155Coded_nonneg g hg hA hB)) (add_nonneg (atom0156Coded_nonneg g hg hA hB) (add_nonneg (atom0157Coded_nonneg g hg hA hB) (atom0158Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0159Coded_nonneg g hg hA hB) (atom0160Coded_nonneg g hg hA hB)) (add_nonneg (atom0161Coded_nonneg g hg hA hB) (add_nonneg (atom0162Coded_nonneg g hg hA hB) (atom0163Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0164Coded_nonneg g hg hA hB) (atom0165Coded_nonneg g hg hA hB)) (add_nonneg (atom0166Coded_nonneg g hg hA hB) (add_nonneg (atom0167Coded_nonneg g hg hA hB) (atom0168Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0169Coded_nonneg g hg hA hB) (atom0170Coded_nonneg g hg hA hB)) (add_nonneg (atom0171Coded_nonneg g hg hA hB) (add_nonneg (atom0172Coded_nonneg g hg hA hB) (atom0173Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0174Coded_nonneg g hg hA hB) (atom0175Coded_nonneg g hg hA hB)) (add_nonneg (atom0176Coded_nonneg g hg hA hB) (add_nonneg (atom0177Coded_nonneg g hg hA hB) (atom0178Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0179Coded_nonneg g hg hA hB) (atom0180Coded_nonneg g hg hA hB)) (add_nonneg (atom0181Coded_nonneg g hg hA hB) (add_nonneg (atom0182Coded_nonneg g hg hA hB) (atom0183Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0184Coded_nonneg g hg hA hB) (atom0185Coded_nonneg g hg hA hB)) (add_nonneg (atom0186Coded_nonneg g hg hA hB) (add_nonneg (atom0187Coded_nonneg g hg hA hB) (atom0188Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0189Coded_nonneg g hg hA hB) (atom0190Coded_nonneg g hg hA hB)) (add_nonneg (atom0191Coded_nonneg g hg hA hB) (add_nonneg (atom0192Coded_nonneg g hg hA hB) (atom0193Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0194Coded_nonneg g hg hA hB) (atom0195Coded_nonneg g hg hA hB)) (add_nonneg (atom0196Coded_nonneg g hg hA hB) (add_nonneg (atom0197Coded_nonneg g hg hA hB) (atom0198Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0199Coded_nonneg g hg hA hB) (atom0200Coded_nonneg g hg hA hB)) (add_nonneg (atom0201Coded_nonneg g hg hA hB) (add_nonneg (atom0202Coded_nonneg g hg hA hB) (atom0203Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0204Coded_nonneg g hg hA hB) (atom0205Coded_nonneg g hg hA hB)) (add_nonneg (atom0206Coded_nonneg g hg hA hB) (add_nonneg (atom0207Coded_nonneg g hg hA hB) (atom0208Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
