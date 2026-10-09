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
theorem eval_atom0160 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) atom0160 = (quadB (outer g) ![1,2,2] * g 2 * g 7) := by
  rw [atom0160_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0160_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2565 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 2 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -14), ([0,1,4], -10), ([0,1,5], -2), ([0,1,6], 2), ([0,1,7], 10), ([0,1,8], 18)]
theorem atom0161_data : atom0161 = SparsePolynomial.monoTimes [0,1] 1 base07 := by decide +kernel
theorem eval_atom0161 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) atom0161 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0161_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0161_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7830 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -14), ([0,2,4], -10), ([0,2,5], -2), ([0,2,6], 2), ([0,2,7], 10), ([0,2,8], 18)]
theorem atom0162_data : atom0162 = SparsePolynomial.monoTimes [0,2] 1 base07 := by decide +kernel
theorem eval_atom0162 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) atom0162 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0162_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0162_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10980 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163 : SparsePolynomial.Poly := [([0,0,7], -8), ([0,1,7], -12), ([0,2,7], -16), ([0,3,7], -14), ([0,4,7], -10), ([0,5,7], -2), ([0,6,7], 2), ([0,7,7], 10), ([0,7,8], 18)]
theorem atom0163_data : atom0163 = SparsePolynomial.monoTimes [0,7] 1 base07 := by decide +kernel
theorem eval_atom0163 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) atom0163 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0163_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0163_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6930 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164 : SparsePolynomial.Poly := [([0,1,8], -8), ([1,1,8], -12), ([1,2,8], -16), ([1,3,8], -14), ([1,4,8], -10), ([1,5,8], -2), ([1,6,8], 2), ([1,7,8], 10), ([1,8,8], 18)]
theorem atom0164_data : atom0164 = SparsePolynomial.monoTimes [1,8] 1 base07 := by decide +kernel
theorem eval_atom0164 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) atom0164 = (quadB (outer g) ![2,2,1] * g 1 * g 8) := by
  rw [atom0164_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0164_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (210 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -14), ([4,4,4], -10), ([4,4,5], -2), ([4,4,6], 2), ([4,4,7], 10), ([4,4,8], 18)]
theorem atom0165_data : atom0165 = SparsePolynomial.monoTimes [4,4] 1 base07 := by decide +kernel
theorem eval_atom0165 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) atom0165 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0165_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0165_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9108 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def block002 : SparsePolynomial.Poly := [([0,0,1], -62640), ([0,0,2], -87840), ([0,0,7], -55440), ([0,1,1], -93960), ([0,1,2], -257040), ([0,1,3], -109620), ([0,1,4], -78300), ([0,1,5], -15660), ([0,1,6], 15660), ([0,1,7], -4860), ([0,1,8], 139260), ([0,2,2], -175680), ([0,2,3], -153720), ([0,2,4], -109800), ([0,2,5], -21960), ([0,2,6], 21960), ([0,2,7], -11340), ([0,2,8], 197640), ([0,3,7], -97020), ([0,4,4], -72864), ([0,4,7], -69300), ([0,5,7], -13860), ([0,6,7], 13860), ([0,7,7], 69300), ([0,7,8], 124740), ([1,1,8], -2520), ([1,2,7], -20520), ([1,2,8], -3360), ([1,3,8], -2940), ([1,4,4], -109296), ([1,4,8], -2100), ([1,5,8], -420), ([1,6,8], 420), ([1,7,8], 2100), ([1,8,8], 3780), ([2,2,7], -41040), ([2,3,7], -20520), ([2,4,4], -145728), ([2,5,7], 20520), ([2,6,7], 30780), ([2,7,7], 41040), ([2,7,8], 46170), ([3,4,4], -127512), ([4,4,4], -91080), ([4,4,5], -18216), ([4,4,6], 18216), ([4,4,7], 91080), ([4,4,8], 163944)]
theorem block002_data : block002 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2565 : Int) atom0160) (SparsePolynomial.merge (SparsePolynomial.scale (7830 : Int) atom0161) (SparsePolynomial.scale (10980 : Int) atom0162))) (SparsePolynomial.merge (SparsePolynomial.scale (6930 : Int) atom0163) (SparsePolynomial.merge (SparsePolynomial.scale (210 : Int) atom0164) (SparsePolynomial.scale (9108 : Int) atom0165)))) := by decide +kernel
theorem block002_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block002 := by
  rw [block002_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (atom0160_nonneg g hg hA hB) (add_nonneg (atom0161_nonneg g hg hA hB) (atom0162_nonneg g hg hA hB))) (add_nonneg (atom0163_nonneg g hg hA hB) (add_nonneg (atom0164_nonneg g hg hA hB) (atom0165_nonneg g hg hA hB))))

end APPT.Finite9
