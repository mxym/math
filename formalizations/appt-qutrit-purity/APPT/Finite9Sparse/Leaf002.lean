import APPT.Finite9Sparse.Base06
import APPT.Finite9Sparse.Base07
import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def atom0160 : SparsePolynomial.Poly := [([0,2,7], -4), ([1,2,7], -8), ([2,2,7], -16), ([2,3,7], -8), ([2,5,7], 8), ([2,6,7], 12), ([2,7,7], 16), ([2,7,8], 18)]
theorem atom0160_data : atom0160 = SparsePolynomial.monoTimes [2,7] 1 base06 := by decide +kernel
theorem eval_atom0160 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0160 = (quadB (outer g) ![1,2,2] * g 2 * g 7) := by
  rw [atom0160_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0160_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2565 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 2 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160Coded : CoefficientMerge.Poly := [(25, -4), (106, -8), (187, -16), (196, -8), (214, 8), (223, 12), (232, 16), (233, 18)]
theorem atom0160Coded_decode : atom0160 = SparsePolynomial.decodeCubic 9 atom0160Coded := by decide +kernel
theorem atom0160Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (2565 : Int) atom0160Coded) := by
  have h := atom0160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0161 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -14), ([0,1,4], -10), ([0,1,5], -2), ([0,1,6], 2), ([0,1,7], 10), ([0,1,8], 18)]
theorem atom0161_data : atom0161 = SparsePolynomial.monoTimes [0,1] 1 base07 := by decide +kernel
theorem eval_atom0161 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0161 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0161_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0161_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7830 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161Coded : CoefficientMerge.Poly := [(1, -8), (10, -12), (11, -16), (12, -14), (13, -10), (14, -2), (15, 2), (16, 10), (17, 18)]
theorem atom0161Coded_decode : atom0161 = SparsePolynomial.decodeCubic 9 atom0161Coded := by decide +kernel
theorem atom0161Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (7830 : Int) atom0161Coded) := by
  have h := atom0161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0162 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -14), ([0,2,4], -10), ([0,2,5], -2), ([0,2,6], 2), ([0,2,7], 10), ([0,2,8], 18)]
theorem atom0162_data : atom0162 = SparsePolynomial.monoTimes [0,2] 1 base07 := by decide +kernel
theorem eval_atom0162 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0162 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0162_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0162_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10980 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162Coded : CoefficientMerge.Poly := [(2, -8), (11, -12), (20, -16), (21, -14), (22, -10), (23, -2), (24, 2), (25, 10), (26, 18)]
theorem atom0162Coded_decode : atom0162 = SparsePolynomial.decodeCubic 9 atom0162Coded := by decide +kernel
theorem atom0162Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (10980 : Int) atom0162Coded) := by
  have h := atom0162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0163 : SparsePolynomial.Poly := [([0,0,7], -8), ([0,1,7], -12), ([0,2,7], -16), ([0,3,7], -14), ([0,4,7], -10), ([0,5,7], -2), ([0,6,7], 2), ([0,7,7], 10), ([0,7,8], 18)]
theorem atom0163_data : atom0163 = SparsePolynomial.monoTimes [0,7] 1 base07 := by decide +kernel
theorem eval_atom0163 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0163 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0163_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0163_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6930 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163Coded : CoefficientMerge.Poly := [(7, -8), (16, -12), (25, -16), (34, -14), (43, -10), (52, -2), (61, 2), (70, 10), (71, 18)]
theorem atom0163Coded_decode : atom0163 = SparsePolynomial.decodeCubic 9 atom0163Coded := by decide +kernel
theorem atom0163Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (6930 : Int) atom0163Coded) := by
  have h := atom0163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0164 : SparsePolynomial.Poly := [([0,1,8], -8), ([1,1,8], -12), ([1,2,8], -16), ([1,3,8], -14), ([1,4,8], -10), ([1,5,8], -2), ([1,6,8], 2), ([1,7,8], 10), ([1,8,8], 18)]
theorem atom0164_data : atom0164 = SparsePolynomial.monoTimes [1,8] 1 base07 := by decide +kernel
theorem eval_atom0164 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0164 = (quadB (outer g) ![2,2,1] * g 1 * g 8) := by
  rw [atom0164_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0164_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164Coded : CoefficientMerge.Poly := [(17, -8), (98, -12), (107, -16), (116, -14), (125, -10), (134, -2), (143, 2), (152, 10), (161, 18)]
theorem atom0164Coded_decode : atom0164 = SparsePolynomial.decodeCubic 9 atom0164Coded := by decide +kernel
theorem atom0164Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (210 : Int) atom0164Coded) := by
  have h := atom0164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0165 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -14), ([4,4,4], -10), ([4,4,5], -2), ([4,4,6], 2), ([4,4,7], 10), ([4,4,8], 18)]
theorem atom0165_data : atom0165 = SparsePolynomial.monoTimes [4,4] 1 base07 := by decide +kernel
theorem eval_atom0165 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) atom0165 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0165_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0165_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9108 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165Coded : CoefficientMerge.Poly := [(40, -8), (121, -12), (202, -16), (283, -14), (364, -10), (365, -2), (366, 2), (367, 10), (368, 18)]
theorem atom0165Coded_decode : atom0165 = SparsePolynomial.decodeCubic 9 atom0165Coded := by decide +kernel
theorem atom0165Coded_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) (CoefficientMerge.scale (9108 : Int) atom0165Coded) := by
  have h := atom0165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block002 : CoefficientMerge.Poly := [(1, -62640), (2, -87840), (7, -55440), (10, -93960), (11, -257040), (12, -109620), (13, -78300), (14, -15660), (15, 15660), (16, -4860), (17, 139260), (20, -175680), (21, -153720), (22, -109800), (23, -21960), (24, 21960), (25, -11340), (26, 197640), (34, -97020), (40, -72864), (43, -69300), (52, -13860), (61, 13860), (70, 69300), (71, 124740), (98, -2520), (106, -20520), (107, -3360), (116, -2940), (121, -109296), (125, -2100), (134, -420), (143, 420), (152, 2100), (161, 3780), (187, -41040), (196, -20520), (202, -145728), (214, 20520), (223, 30780), (232, 41040), (233, 46170), (283, -127512), (364, -91080), (365, -18216), (366, 18216), (367, 91080), (368, 163944)]
theorem block002_data : block002 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2565 : Int) atom0160Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7830 : Int) atom0161Coded) (CoefficientMerge.scale (10980 : Int) atom0162Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6930 : Int) atom0163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210 : Int) atom0164Coded) (CoefficientMerge.scale (9108 : Int) atom0165Coded)))) := by decide +kernel
theorem block002_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) block002 := by
  rw [block002_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (atom0160Coded_nonneg g hg hA hB) (add_nonneg (atom0161Coded_nonneg g hg hA hB) (atom0162Coded_nonneg g hg hA hB))) (add_nonneg (atom0163Coded_nonneg g hg hA hB) (add_nonneg (atom0164Coded_nonneg g hg hA hB) (atom0165Coded_nonneg g hg hA hB))))

end APPT.Finite9
