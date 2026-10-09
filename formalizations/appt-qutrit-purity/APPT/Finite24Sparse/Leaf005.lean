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
theorem eval_atom0209 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0209 = (quadB (outer g) ![2,2,1] * g 10 * g 12) := by
  rw [atom0209_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0209_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (559159273728 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210 : SparsePolynomial.Poly := [([0,11,11], -8), ([1,11,11], -12), ([2,11,11], -16), ([3,11,11], -16), ([4,11,11], -16), ([5,11,11], -16), ([6,11,11], -16), ([7,11,11], -16), ([8,11,11], -16), ([9,11,11], -16), ([10,11,11], -16), ([11,11,11], -16), ([11,11,12], -16), ([11,11,13], -16), ([11,11,14], -16), ([11,11,15], -16), ([11,11,16], -16), ([11,11,17], -16), ([11,11,18], -14), ([11,11,19], -10), ([11,11,20], -2), ([11,11,21], 2), ([11,11,22], 10), ([11,11,23], 18)]
theorem atom0210_data : atom0210 = SparsePolynomial.monoTimes [11,11] 1 base08 := by decide +kernel
theorem eval_atom0210 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0210 = (quadB (outer g) ![2,2,1] * g 11 * g 11) := by
  rw [atom0210_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0210_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2572011413136 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211 : SparsePolynomial.Poly := [([0,11,12], -8), ([1,11,12], -12), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -16), ([11,12,13], -16), ([11,12,14], -16), ([11,12,15], -16), ([11,12,16], -16), ([11,12,17], -16), ([11,12,18], -14), ([11,12,19], -10), ([11,12,20], -2), ([11,12,21], 2), ([11,12,22], 10), ([11,12,23], 18)]
theorem atom0211_data : atom0211 = SparsePolynomial.monoTimes [11,12] 1 base08 := by decide +kernel
theorem eval_atom0211 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0211 = (quadB (outer g) ![2,2,1] * g 11 * g 12) := by
  rw [atom0211_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0211_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7092350065152 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212 : SparsePolynomial.Poly := [([0,11,13], -8), ([1,11,13], -12), ([2,11,13], -16), ([3,11,13], -16), ([4,11,13], -16), ([5,11,13], -16), ([6,11,13], -16), ([7,11,13], -16), ([8,11,13], -16), ([9,11,13], -16), ([10,11,13], -16), ([11,11,13], -16), ([11,12,13], -16), ([11,13,13], -16), ([11,13,14], -16), ([11,13,15], -16), ([11,13,16], -16), ([11,13,17], -16), ([11,13,18], -14), ([11,13,19], -10), ([11,13,20], -2), ([11,13,21], 2), ([11,13,22], 10), ([11,13,23], 18)]
theorem atom0212_data : atom0212 = SparsePolynomial.monoTimes [11,13] 1 base08 := by decide +kernel
theorem eval_atom0212 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0212 = (quadB (outer g) ![2,2,1] * g 11 * g 13) := by
  rw [atom0212_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0212_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1676193146496 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213 : SparsePolynomial.Poly := [([0,12,12], -8), ([1,12,12], -12), ([2,12,12], -16), ([3,12,12], -16), ([4,12,12], -16), ([5,12,12], -16), ([6,12,12], -16), ([7,12,12], -16), ([8,12,12], -16), ([9,12,12], -16), ([10,12,12], -16), ([11,12,12], -16), ([12,12,12], -16), ([12,12,13], -16), ([12,12,14], -16), ([12,12,15], -16), ([12,12,16], -16), ([12,12,17], -16), ([12,12,18], -14), ([12,12,19], -10), ([12,12,20], -2), ([12,12,21], 2), ([12,12,22], 10), ([12,12,23], 18)]
theorem atom0213_data : atom0213 = SparsePolynomial.monoTimes [12,12] 1 base08 := by decide +kernel
theorem eval_atom0213 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0213 = (quadB (outer g) ![2,2,1] * g 12 * g 12) := by
  rw [atom0213_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0213_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6218852276736 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214 : SparsePolynomial.Poly := [([0,12,13], -8), ([1,12,13], -12), ([2,12,13], -16), ([3,12,13], -16), ([4,12,13], -16), ([5,12,13], -16), ([6,12,13], -16), ([7,12,13], -16), ([8,12,13], -16), ([9,12,13], -16), ([10,12,13], -16), ([11,12,13], -16), ([12,12,13], -16), ([12,13,13], -16), ([12,13,14], -16), ([12,13,15], -16), ([12,13,16], -16), ([12,13,17], -16), ([12,13,18], -14), ([12,13,19], -10), ([12,13,20], -2), ([12,13,21], 2), ([12,13,22], 10), ([12,13,23], 18)]
theorem atom0214_data : atom0214 = SparsePolynomial.monoTimes [12,13] 1 base08 := by decide +kernel
theorem eval_atom0214 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0214 = (quadB (outer g) ![2,2,1] * g 12 * g 13) := by
  rw [atom0214_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0214_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6417696928896 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215 : SparsePolynomial.Poly := [([0,12,14], -8), ([1,12,14], -12), ([2,12,14], -16), ([3,12,14], -16), ([4,12,14], -16), ([5,12,14], -16), ([6,12,14], -16), ([7,12,14], -16), ([8,12,14], -16), ([9,12,14], -16), ([10,12,14], -16), ([11,12,14], -16), ([12,12,14], -16), ([12,13,14], -16), ([12,14,14], -16), ([12,14,15], -16), ([12,14,16], -16), ([12,14,17], -16), ([12,14,18], -14), ([12,14,19], -10), ([12,14,20], -2), ([12,14,21], 2), ([12,14,22], 10), ([12,14,23], 18)]
theorem atom0215_data : atom0215 = SparsePolynomial.monoTimes [12,14] 1 base08 := by decide +kernel
theorem eval_atom0215 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0215 = (quadB (outer g) ![2,2,1] * g 12 * g 14) := by
  rw [atom0215_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0215_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (562580233776 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216 : SparsePolynomial.Poly := [([0,13,13], -8), ([1,13,13], -12), ([2,13,13], -16), ([3,13,13], -16), ([4,13,13], -16), ([5,13,13], -16), ([6,13,13], -16), ([7,13,13], -16), ([8,13,13], -16), ([9,13,13], -16), ([10,13,13], -16), ([11,13,13], -16), ([12,13,13], -16), ([13,13,13], -16), ([13,13,14], -16), ([13,13,15], -16), ([13,13,16], -16), ([13,13,17], -16), ([13,13,18], -14), ([13,13,19], -10), ([13,13,20], -2), ([13,13,21], 2), ([13,13,22], 10), ([13,13,23], 18)]
theorem atom0216_data : atom0216 = SparsePolynomial.monoTimes [13,13] 1 base08 := by decide +kernel
theorem eval_atom0216 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0216 = (quadB (outer g) ![2,2,1] * g 13 * g 13) := by
  rw [atom0216_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0216_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7083593193600 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217 : SparsePolynomial.Poly := [([0,13,14], -8), ([1,13,14], -12), ([2,13,14], -16), ([3,13,14], -16), ([4,13,14], -16), ([5,13,14], -16), ([6,13,14], -16), ([7,13,14], -16), ([8,13,14], -16), ([9,13,14], -16), ([10,13,14], -16), ([11,13,14], -16), ([12,13,14], -16), ([13,13,14], -16), ([13,14,14], -16), ([13,14,15], -16), ([13,14,16], -16), ([13,14,17], -16), ([13,14,18], -14), ([13,14,19], -10), ([13,14,20], -2), ([13,14,21], 2), ([13,14,22], 10), ([13,14,23], 18)]
theorem atom0217_data : atom0217 = SparsePolynomial.monoTimes [13,14] 1 base08 := by decide +kernel
theorem eval_atom0217 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0217 = (quadB (outer g) ![2,2,1] * g 13 * g 14) := by
  rw [atom0217_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0217_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7708218986160 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218 : SparsePolynomial.Poly := [([0,13,15], -8), ([1,13,15], -12), ([2,13,15], -16), ([3,13,15], -16), ([4,13,15], -16), ([5,13,15], -16), ([6,13,15], -16), ([7,13,15], -16), ([8,13,15], -16), ([9,13,15], -16), ([10,13,15], -16), ([11,13,15], -16), ([12,13,15], -16), ([13,13,15], -16), ([13,14,15], -16), ([13,15,15], -16), ([13,15,16], -16), ([13,15,17], -16), ([13,15,18], -14), ([13,15,19], -10), ([13,15,20], -2), ([13,15,21], 2), ([13,15,22], 10), ([13,15,23], 18)]
theorem atom0218_data : atom0218 = SparsePolynomial.monoTimes [13,15] 1 base08 := by decide +kernel
theorem eval_atom0218 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0218 = (quadB (outer g) ![2,2,1] * g 13 * g 15) := by
  rw [atom0218_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0218_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (678085107840 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219 : SparsePolynomial.Poly := [([0,14,14], -8), ([1,14,14], -12), ([2,14,14], -16), ([3,14,14], -16), ([4,14,14], -16), ([5,14,14], -16), ([6,14,14], -16), ([7,14,14], -16), ([8,14,14], -16), ([9,14,14], -16), ([10,14,14], -16), ([11,14,14], -16), ([12,14,14], -16), ([13,14,14], -16), ([14,14,14], -16), ([14,14,15], -16), ([14,14,16], -16), ([14,14,17], -16), ([14,14,18], -14), ([14,14,19], -10), ([14,14,20], -2), ([14,14,21], 2), ([14,14,22], 10), ([14,14,23], 18)]
theorem atom0219_data : atom0219 = SparsePolynomial.monoTimes [14,14] 1 base08 := by decide +kernel
theorem eval_atom0219 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0219 = (quadB (outer g) ![2,2,1] * g 14 * g 14) := by
  rw [atom0219_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0219_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7509374334000 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220 : SparsePolynomial.Poly := [([0,14,15], -8), ([1,14,15], -12), ([2,14,15], -16), ([3,14,15], -16), ([4,14,15], -16), ([5,14,15], -16), ([6,14,15], -16), ([7,14,15], -16), ([8,14,15], -16), ([9,14,15], -16), ([10,14,15], -16), ([11,14,15], -16), ([12,14,15], -16), ([13,14,15], -16), ([14,14,15], -16), ([14,15,15], -16), ([14,15,16], -16), ([14,15,17], -16), ([14,15,18], -14), ([14,15,19], -10), ([14,15,20], -2), ([14,15,21], 2), ([14,15,22], 10), ([14,15,23], 18)]
theorem atom0220_data : atom0220 = SparsePolynomial.monoTimes [14,15] 1 base08 := by decide +kernel
theorem eval_atom0220 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0220 = (quadB (outer g) ![2,2,1] * g 14 * g 15) := by
  rw [atom0220_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0220_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7384764083760 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221 : SparsePolynomial.Poly := [([0,14,16], -8), ([1,14,16], -12), ([2,14,16], -16), ([3,14,16], -16), ([4,14,16], -16), ([5,14,16], -16), ([6,14,16], -16), ([7,14,16], -16), ([8,14,16], -16), ([9,14,16], -16), ([10,14,16], -16), ([11,14,16], -16), ([12,14,16], -16), ([13,14,16], -16), ([14,14,16], -16), ([14,15,16], -16), ([14,16,16], -16), ([14,16,17], -16), ([14,16,18], -14), ([14,16,19], -10), ([14,16,20], -2), ([14,16,21], 2), ([14,16,22], 10), ([14,16,23], 18)]
theorem atom0221_data : atom0221 = SparsePolynomial.monoTimes [14,16] 1 base08 := by decide +kernel
theorem eval_atom0221 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0221 = (quadB (outer g) ![2,2,1] * g 14 * g 16) := by
  rw [atom0221_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0221_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (201182894640 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222 : SparsePolynomial.Poly := [([0,15,15], -8), ([1,15,15], -12), ([2,15,15], -16), ([3,15,15], -16), ([4,15,15], -16), ([5,15,15], -16), ([6,15,15], -16), ([7,15,15], -16), ([8,15,15], -16), ([9,15,15], -16), ([10,15,15], -16), ([11,15,15], -16), ([12,15,15], -16), ([13,15,15], -16), ([14,15,15], -16), ([15,15,15], -16), ([15,15,16], -16), ([15,15,17], -16), ([15,15,18], -14), ([15,15,19], -10), ([15,15,20], -2), ([15,15,21], 2), ([15,15,22], 10), ([15,15,23], 18)]
theorem atom0222_data : atom0222 = SparsePolynomial.monoTimes [15,15] 1 base08 := by decide +kernel
theorem eval_atom0222 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0222 = (quadB (outer g) ![2,2,1] * g 15 * g 15) := by
  rw [atom0222_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0222_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6760138291200 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 15 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223 : SparsePolynomial.Poly := [([0,15,16], -8), ([1,15,16], -12), ([2,15,16], -16), ([3,15,16], -16), ([4,15,16], -16), ([5,15,16], -16), ([6,15,16], -16), ([7,15,16], -16), ([8,15,16], -16), ([9,15,16], -16), ([10,15,16], -16), ([11,15,16], -16), ([12,15,16], -16), ([13,15,16], -16), ([14,15,16], -16), ([15,15,16], -16), ([15,16,16], -16), ([15,16,17], -16), ([15,16,18], -14), ([15,16,19], -10), ([15,16,20], -2), ([15,16,21], 2), ([15,16,22], 10), ([15,16,23], 18)]
theorem atom0223_data : atom0223 = SparsePolynomial.monoTimes [15,16] 1 base08 := by decide +kernel
theorem eval_atom0223 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0223 = (quadB (outer g) ![2,2,1] * g 15 * g 16) := by
  rw [atom0223_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0223_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5732844687360 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 15 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224 : SparsePolynomial.Poly := [([0,16,16], -8), ([1,16,16], -12), ([2,16,16], -16), ([3,16,16], -16), ([4,16,16], -16), ([5,16,16], -16), ([6,16,16], -16), ([7,16,16], -16), ([8,16,16], -16), ([9,16,16], -16), ([10,16,16], -16), ([11,16,16], -16), ([12,16,16], -16), ([13,16,16], -16), ([14,16,16], -16), ([15,16,16], -16), ([16,16,16], -16), ([16,16,17], -16), ([16,16,18], -14), ([16,16,19], -10), ([16,16,20], -2), ([16,16,21], 2), ([16,16,22], 10), ([16,16,23], 18)]
theorem atom0224_data : atom0224 = SparsePolynomial.monoTimes [16,16] 1 base08 := by decide +kernel
theorem eval_atom0224 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0224 = (quadB (outer g) ![2,2,1] * g 16 * g 16) := by
  rw [atom0224_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0224_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5857454937600 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 16 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225 : SparsePolynomial.Poly := [([0,16,17], -8), ([1,16,17], -12), ([2,16,17], -16), ([3,16,17], -16), ([4,16,17], -16), ([5,16,17], -16), ([6,16,17], -16), ([7,16,17], -16), ([8,16,17], -16), ([9,16,17], -16), ([10,16,17], -16), ([11,16,17], -16), ([12,16,17], -16), ([13,16,17], -16), ([14,16,17], -16), ([15,16,17], -16), ([16,16,17], -16), ([16,17,17], -16), ([16,17,18], -14), ([16,17,19], -10), ([16,17,20], -2), ([16,17,21], 2), ([16,17,22], 10), ([16,17,23], 18)]
theorem atom0225_data : atom0225 = SparsePolynomial.monoTimes [16,17] 1 base08 := by decide +kernel
theorem eval_atom0225 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0225 = (quadB (outer g) ![2,2,1] * g 16 * g 17) := by
  rw [atom0225_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0225_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2325757324800 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 16 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226 : SparsePolynomial.Poly := [([0,17,17], -8), ([1,17,17], -12), ([2,17,17], -16), ([3,17,17], -16), ([4,17,17], -16), ([5,17,17], -16), ([6,17,17], -16), ([7,17,17], -16), ([8,17,17], -16), ([9,17,17], -16), ([10,17,17], -16), ([11,17,17], -16), ([12,17,17], -16), ([13,17,17], -16), ([14,17,17], -16), ([15,17,17], -16), ([16,17,17], -16), ([17,17,17], -16), ([17,17,18], -14), ([17,17,19], -10), ([17,17,20], -2), ([17,17,21], 2), ([17,17,22], 10), ([17,17,23], 18)]
theorem atom0226_data : atom0226 = SparsePolynomial.monoTimes [17,17] 1 base08 := by decide +kernel
theorem eval_atom0226 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0226 = (quadB (outer g) ![2,2,1] * g 17 * g 17) := by
  rw [atom0226_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0226_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3848485132800 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 17 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227 : SparsePolynomial.Poly := [([0,19,19], -8), ([1,19,19], -12), ([2,19,19], -16), ([3,19,19], -16), ([4,19,19], -16), ([5,19,19], -16), ([6,19,19], -16), ([7,19,19], -16), ([8,19,19], -16), ([9,19,19], -16), ([10,19,19], -16), ([11,19,19], -16), ([12,19,19], -16), ([13,19,19], -16), ([14,19,19], -16), ([15,19,19], -16), ([16,19,19], -16), ([17,19,19], -16), ([18,19,19], -14), ([19,19,19], -10), ([19,19,20], -2), ([19,19,21], 2), ([19,19,22], 10), ([19,19,23], 18)]
theorem atom0227_data : atom0227 = SparsePolynomial.monoTimes [19,19] 1 base08 := by decide +kernel
theorem eval_atom0227 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0227 = (quadB (outer g) ![2,2,1] * g 19 * g 19) := by
  rw [atom0227_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0227_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (612355645440 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 19 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228 : SparsePolynomial.Poly := [([0,0,11], 1)]
theorem eval_atom0228 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0228 = ((g 0) * (g 0) * (g 11)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0228_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2323663382304 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 0) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229 : SparsePolynomial.Poly := [([0,0,12], 1)]
theorem eval_atom0229 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0229 = ((g 0) * (g 0) * (g 12)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0229_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27162605029824 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 0) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230 : SparsePolynomial.Poly := [([0,0,13], 1)]
theorem eval_atom0230 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0230 = ((g 0) * (g 0) * (g 13)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0230_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15418433923200 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 0) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231 : SparsePolynomial.Poly := [([0,0,18], 1)]
theorem eval_atom0231 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0231 = ((g 0) * (g 0) * (g 18)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0231_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11502930700800 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 0) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232 : SparsePolynomial.Poly := [([0,0,19], 1)]
theorem eval_atom0232 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0232 = ((g 0) * (g 0) * (g 19)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0232_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8419890124800 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 0) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233 : SparsePolynomial.Poly := [([0,0,20], 1)]
theorem eval_atom0233 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0233 = ((g 0) * (g 0) * (g 20)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0233_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5336849548800 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 0) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234 : SparsePolynomial.Poly := [([0,0,21], 1)]
theorem eval_atom0234 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0234 = ((g 0) * (g 0) * (g 21)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0234_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2253808972800 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 0) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235 : SparsePolynomial.Poly := [([0,1,1], 1)]
theorem eval_atom0235 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0235 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0235_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2338858368000 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236 : SparsePolynomial.Poly := [([0,1,2], 1)]
theorem eval_atom0236 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0236 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0236_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60480751161600 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237 : SparsePolynomial.Poly := [([0,1,3], 1)]
theorem eval_atom0237 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0237 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0237_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (59959823616000 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238 : SparsePolynomial.Poly := [([0,1,4], 1)]
theorem eval_atom0238 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0238 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0238_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (59438896070400 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239 : SparsePolynomial.Poly := [([0,1,5], 1)]
theorem eval_atom0239 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0239 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0239_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (62359415395200 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0240 : SparsePolynomial.Poly := [([0,1,6], 1)]
theorem eval_atom0240 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0240 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0240_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58397040979200 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241 : SparsePolynomial.Poly := [([0,1,7], 1)]
theorem eval_atom0241 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0241 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0241_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57876113433600 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242 : SparsePolynomial.Poly := [([0,1,8], 1)]
theorem eval_atom0242 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0242 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0242_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57355185888000 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243 : SparsePolynomial.Poly := [([0,1,9], 1)]
theorem eval_atom0243 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0243 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0243_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (59840148865464 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244 : SparsePolynomial.Poly := [([0,1,10], 1)]
theorem eval_atom0244 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0244 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0244_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68140969836984 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245 : SparsePolynomial.Poly := [([0,1,11], 1)]
theorem eval_atom0245 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0245 = ((g 0) * (g 1) * (g 11)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0245_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79108072262208 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246 : SparsePolynomial.Poly := [([0,1,12], 1)]
theorem eval_atom0246 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0246 = ((g 0) * (g 1) * (g 12)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0246_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (129806548299648 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247 : SparsePolynomial.Poly := [([0,1,13], 1)]
theorem eval_atom0247 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0247 = ((g 0) * (g 1) * (g 13)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0247_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (107338798828800 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248 : SparsePolynomial.Poly := [([0,1,14], 1)]
theorem eval_atom0248 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0248 = ((g 0) * (g 1) * (g 14)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0248_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (77522523724800 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249 : SparsePolynomial.Poly := [([0,1,15], 1)]
theorem eval_atom0249 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0249 = ((g 0) * (g 1) * (g 15)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0249_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78227402803200 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250 : SparsePolynomial.Poly := [([0,1,16], 1)]
theorem eval_atom0250 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0250 = ((g 0) * (g 1) * (g 16)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0250_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (73021026758400 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251 : SparsePolynomial.Poly := [([0,1,17], 1)]
theorem eval_atom0251 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0251 = ((g 0) * (g 1) * (g 17)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0251_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (72781019942400 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252 : SparsePolynomial.Poly := [([0,1,18], 1)]
theorem eval_atom0252 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0252 = ((g 0) * (g 1) * (g 18)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0252_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (102984186412800 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 1) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253 : SparsePolynomial.Poly := [([0,1,19], 1)]
theorem eval_atom0253 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0253 = ((g 0) * (g 1) * (g 19)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0253_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40961914963200 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 1) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254 : SparsePolynomial.Poly := [([0,1,20], 1)]
theorem eval_atom0254 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0254 = ((g 0) * (g 1) * (g 20)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0254_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12512892268800 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 1) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0255 : SparsePolynomial.Poly := [([0,1,21], 1)]
theorem eval_atom0255 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0255 = ((g 0) * (g 1) * (g 21)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0255_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5205731731200 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 1) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0256 : SparsePolynomial.Poly := [([0,1,22], 1)]
theorem eval_atom0256 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0256 = ((g 0) * (g 1) * (g 22)) := by
  norm_num [atom0256, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0256_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4086988550400 : Int) atom0256) := by
  rw [SparsePolynomial.eval_scale, eval_atom0256]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 1) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0257 : SparsePolynomial.Poly := [([0,2,2], 1)]
theorem eval_atom0257 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0257 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0257, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0257_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (65275410816000 : Int) atom0257) := by
  rw [SparsePolynomial.eval_scale, eval_atom0257]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0258 : SparsePolynomial.Poly := [([0,2,3], 1)]
theorem eval_atom0258 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0258 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0258, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0258_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (132592007116800 : Int) atom0258) := by
  rw [SparsePolynomial.eval_scale, eval_atom0258]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0259 : SparsePolynomial.Poly := [([0,2,4], 1)]
theorem eval_atom0259 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0259 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0259, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0259_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (134633192601600 : Int) atom0259) := by
  rw [SparsePolynomial.eval_scale, eval_atom0259]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0260 : SparsePolynomial.Poly := [([0,2,5], 1)]
theorem eval_atom0260 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0260 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0260, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0260_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (136674378086400 : Int) atom0260) := by
  rw [SparsePolynomial.eval_scale, eval_atom0260]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0261 : SparsePolynomial.Poly := [([0,2,6], 1)]
theorem eval_atom0261 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0261 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0261, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0261_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (138715563571200 : Int) atom0261) := by
  rw [SparsePolynomial.eval_scale, eval_atom0261]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0262 : SparsePolynomial.Poly := [([0,2,7], 1)]
theorem eval_atom0262 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0262 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0262, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0262_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (140756749056000 : Int) atom0262) := by
  rw [SparsePolynomial.eval_scale, eval_atom0262]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0263 : SparsePolynomial.Poly := [([0,2,8], 1)]
theorem eval_atom0263 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0263 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0263, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0263_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (142797934540800 : Int) atom0263) := by
  rw [SparsePolynomial.eval_scale, eval_atom0263]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0264 : SparsePolynomial.Poly := [([0,2,9], 1)]
theorem eval_atom0264 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0264 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0264, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0264_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (144839120025600 : Int) atom0264) := by
  rw [SparsePolynomial.eval_scale, eval_atom0264]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0265 : SparsePolynomial.Poly := [([0,2,10], 1)]
theorem eval_atom0265 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0265 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0265, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0265_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (146880305510400 : Int) atom0265) := by
  rw [SparsePolynomial.eval_scale, eval_atom0265]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0266 : SparsePolynomial.Poly := [([0,2,11], 1)]
theorem eval_atom0266 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0266 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0266, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0266_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (153568817759808 : Int) atom0266) := by
  rw [SparsePolynomial.eval_scale, eval_atom0266]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0267 : SparsePolynomial.Poly := [([0,2,12], 1)]
theorem eval_atom0267 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0267 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0267, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0267_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (205287886539648 : Int) atom0267) := by
  rw [SparsePolynomial.eval_scale, eval_atom0267]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0268 : SparsePolynomial.Poly := [([0,2,13], 1)]
theorem eval_atom0268 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0268 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0268, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0268_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (183840729811200 : Int) atom0268) := by
  rw [SparsePolynomial.eval_scale, eval_atom0268]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0269 : SparsePolynomial.Poly := [([0,2,14], 1)]
theorem eval_atom0269 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0269 = ((g 0) * (g 2) * (g 14)) := by
  norm_num [atom0269, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0269_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (155045047449600 : Int) atom0269) := by
  rw [SparsePolynomial.eval_scale, eval_atom0269]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0270 : SparsePolynomial.Poly := [([0,2,15], 1)]
theorem eval_atom0270 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0270 = ((g 0) * (g 2) * (g 15)) := by
  norm_num [atom0270, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0270_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (157086232934400 : Int) atom0270) := by
  rw [SparsePolynomial.eval_scale, eval_atom0270]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0271 : SparsePolynomial.Poly := [([0,2,16], 1)]
theorem eval_atom0271 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0271 = ((g 0) * (g 2) * (g 16)) := by
  norm_num [atom0271, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0271_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (159127418419200 : Int) atom0271) := by
  rw [SparsePolynomial.eval_scale, eval_atom0271]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0272 : SparsePolynomial.Poly := [([0,2,17], 1)]
theorem eval_atom0272 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0272 = ((g 0) * (g 2) * (g 17)) := by
  norm_num [atom0272, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0272_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (161168603904000 : Int) atom0272) := by
  rw [SparsePolynomial.eval_scale, eval_atom0272]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0273 : SparsePolynomial.Poly := [([0,2,18], 1)]
theorem eval_atom0273 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0273 = ((g 0) * (g 2) * (g 18)) := by
  norm_num [atom0273, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0273_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (183818320963200 : Int) atom0273) := by
  rw [SparsePolynomial.eval_scale, eval_atom0273]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0274 : SparsePolynomial.Poly := [([0,2,19], 1)]
theorem eval_atom0274 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0274 = ((g 0) * (g 2) * (g 19)) := by
  norm_num [atom0274, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0274_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (104477866416000 : Int) atom0274) := by
  rw [SparsePolynomial.eval_scale, eval_atom0274]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0275 : SparsePolynomial.Poly := [([0,2,20], 1)]
theorem eval_atom0275 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0275 = ((g 0) * (g 2) * (g 20)) := by
  norm_num [atom0275, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0275_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90763651440000 : Int) atom0275) := by
  rw [SparsePolynomial.eval_scale, eval_atom0275]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0276 : SparsePolynomial.Poly := [([0,2,21], 1)]
theorem eval_atom0276 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0276 = ((g 0) * (g 2) * (g 21)) := by
  norm_num [atom0276, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0276_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11423196892800 : Int) atom0276) := by
  rw [SparsePolynomial.eval_scale, eval_atom0276]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 2) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0277 : SparsePolynomial.Poly := [([0,2,22], 1)]
theorem eval_atom0277 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0277 = ((g 0) * (g 2) * (g 22)) := by
  norm_num [atom0277, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0277_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20816644867200 : Int) atom0277) := by
  rw [SparsePolynomial.eval_scale, eval_atom0277]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 2) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0278 : SparsePolynomial.Poly := [([0,3,3], 1)]
theorem eval_atom0278 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0278 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0278, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0278_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64233555724800 : Int) atom0278) := by
  rw [SparsePolynomial.eval_scale, eval_atom0278]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0279 : SparsePolynomial.Poly := [([0,3,4], 1)]
theorem eval_atom0279 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0279 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0279, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0279_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (131528889676800 : Int) atom0279) := by
  rw [SparsePolynomial.eval_scale, eval_atom0279]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0280 : SparsePolynomial.Poly := [([0,3,5], 1)]
theorem eval_atom0280 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0280 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0280, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0280_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (134590667904000 : Int) atom0280) := by
  rw [SparsePolynomial.eval_scale, eval_atom0280]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0281 : SparsePolynomial.Poly := [([0,3,6], 1)]
theorem eval_atom0281 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0281 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0281, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0281_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (137652446131200 : Int) atom0281) := by
  rw [SparsePolynomial.eval_scale, eval_atom0281]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0282 : SparsePolynomial.Poly := [([0,3,7], 1)]
theorem eval_atom0282 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0282 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0282, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0282_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (140714224358400 : Int) atom0282) := by
  rw [SparsePolynomial.eval_scale, eval_atom0282]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0283 : SparsePolynomial.Poly := [([0,3,8], 1)]
theorem eval_atom0283 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0283 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0283, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0283_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (143776002585600 : Int) atom0283) := by
  rw [SparsePolynomial.eval_scale, eval_atom0283]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0284 : SparsePolynomial.Poly := [([0,3,9], 1)]
theorem eval_atom0284 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0284 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0284, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0284_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (146837780812800 : Int) atom0284) := by
  rw [SparsePolynomial.eval_scale, eval_atom0284]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0285 : SparsePolynomial.Poly := [([0,3,10], 1)]
theorem eval_atom0285 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0285 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0285, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0285_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (149899559040000 : Int) atom0285) := by
  rw [SparsePolynomial.eval_scale, eval_atom0285]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0286 : SparsePolynomial.Poly := [([0,3,11], 1)]
theorem eval_atom0286 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0286 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0286, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0286_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (157608664031808 : Int) atom0286) := by
  rw [SparsePolynomial.eval_scale, eval_atom0286]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0287 : SparsePolynomial.Poly := [([0,3,12], 1)]
theorem eval_atom0287 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0287 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0287, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0287_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (210348325554048 : Int) atom0287) := by
  rw [SparsePolynomial.eval_scale, eval_atom0287]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0288 : SparsePolynomial.Poly := [([0,3,13], 1)]
theorem eval_atom0288 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0288 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0288, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0288_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (189921761568000 : Int) atom0288) := by
  rw [SparsePolynomial.eval_scale, eval_atom0288]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block005 : SparsePolynomial.Poly := [([0,0,11], 2323663382304), ([0,0,12], 27162605029824), ([0,0,13], 15418433923200), ([0,0,18], 11502930700800), ([0,0,19], 8419890124800), ([0,0,20], 5336849548800), ([0,0,21], 2253808972800), ([0,1,1], 2338858368000), ([0,1,2], 60480751161600), ([0,1,3], 59959823616000), ([0,1,4], 59438896070400), ([0,1,5], 62359415395200), ([0,1,6], 58397040979200), ([0,1,7], 57876113433600), ([0,1,8], 57355185888000), ([0,1,9], 59840148865464), ([0,1,10], 68140969836984), ([0,1,11], 79108072262208), ([0,1,12], 129806548299648), ([0,1,13], 107338798828800), ([0,1,14], 77522523724800), ([0,1,15], 78227402803200), ([0,1,16], 73021026758400), ([0,1,17], 72781019942400), ([0,1,18], 102984186412800), ([0,1,19], 40961914963200), ([0,1,20], 12512892268800), ([0,1,21], 5205731731200), ([0,1,22], 4086988550400), ([0,2,2], 65275410816000), ([0,2,3], 132592007116800), ([0,2,4], 134633192601600), ([0,2,5], 136674378086400), ([0,2,6], 138715563571200), ([0,2,7], 140756749056000), ([0,2,8], 142797934540800), ([0,2,9], 144839120025600), ([0,2,10], 146880305510400), ([0,2,11], 153568817759808), ([0,2,12], 205287886539648), ([0,2,13], 183840729811200), ([0,2,14], 155045047449600), ([0,2,15], 157086232934400), ([0,2,16], 159127418419200), ([0,2,17], 161168603904000), ([0,2,18], 183818320963200), ([0,2,19], 104477866416000), ([0,2,20], 90763651440000), ([0,2,21], 11423196892800), ([0,2,22], 20816644867200), ([0,3,3], 64233555724800), ([0,3,4], 131528889676800), ([0,3,5], 134590667904000), ([0,3,6], 137652446131200), ([0,3,7], 140714224358400), ([0,3,8], 143776002585600), ([0,3,9], 146837780812800), ([0,3,10], 149899559040000), ([0,3,11], 157608664031808), ([0,3,12], 210348325554048), ([0,3,13], 189921761568000), ([0,10,12], -4473274189824), ([0,11,11], -20576091305088), ([0,11,12], -56738800521216), ([0,11,13], -13409545171968), ([0,12,12], -49750818213888), ([0,12,13], -51341575431168), ([0,12,14], -4500641870208), ([0,13,13], -56668745548800), ([0,13,14], -61665751889280), ([0,13,15], -5424680862720), ([0,14,14], -60074994672000), ([0,14,15], -59078112670080), ([0,14,16], -1609463157120), ([0,15,15], -54081106329600), ([0,15,16], -45862757498880), ([0,16,16], -46859639500800), ([0,16,17], -18606058598400), ([0,17,17], -30787881062400), ([0,19,19], -4898845163520), ([1,10,12], -6709911284736), ([1,11,11], -30864136957632), ([1,11,12], -85108200781824), ([1,11,13], -20114317757952), ([1,12,12], -74626227320832), ([1,12,13], -77012363146752), ([1,12,14], -6750962805312), ([1,13,13], -85003118323200), ([1,13,14], -92498627833920), ([1,13,15], -8137021294080), ([1,14,14], -90112492008000), ([1,14,15], -88617169005120), ([1,14,16], -2414194735680), ([1,15,15], -81121659494400), ([1,15,16], -68794136248320), ([1,16,16], -70289459251200), ([1,16,17], -27909087897600), ([1,17,17], -46181821593600), ([1,19,19], -7348267745280), ([2,10,12], -8946548379648), ([2,11,11], -41152182610176), ([2,11,12], -113477601042432), ([2,11,13], -26819090343936), ([2,12,12], -99501636427776), ([2,12,13], -102683150862336), ([2,12,14], -9001283740416), ([2,13,13], -113337491097600), ([2,13,14], -123331503778560), ([2,13,15], -10849361725440), ([2,14,14], -120149989344000), ([2,14,15], -118156225340160), ([2,14,16], -3218926314240), ([2,15,15], -108162212659200), ([2,15,16], -91725514997760), ([2,16,16], -93719279001600), ([2,16,17], -37212117196800), ([2,17,17], -61575762124800), ([2,19,19], -9797690327040), ([3,10,12], -8946548379648), ([3,11,11], -41152182610176), ([3,11,12], -113477601042432), ([3,11,13], -26819090343936), ([3,12,12], -99501636427776), ([3,12,13], -102683150862336), ([3,12,14], -9001283740416), ([3,13,13], -113337491097600), ([3,13,14], -123331503778560), ([3,13,15], -10849361725440), ([3,14,14], -120149989344000), ([3,14,15], -118156225340160), ([3,14,16], -3218926314240), ([3,15,15], -108162212659200), ([3,15,16], -91725514997760), ([3,16,16], -93719279001600), ([3,16,17], -37212117196800), ([3,17,17], -61575762124800), ([3,19,19], -9797690327040), ([4,10,12], -8946548379648), ([4,11,11], -41152182610176), ([4,11,12], -113477601042432), ([4,11,13], -26819090343936), ([4,12,12], -99501636427776), ([4,12,13], -102683150862336), ([4,12,14], -9001283740416), ([4,13,13], -113337491097600), ([4,13,14], -123331503778560), ([4,13,15], -10849361725440), ([4,14,14], -120149989344000), ([4,14,15], -118156225340160), ([4,14,16], -3218926314240), ([4,15,15], -108162212659200), ([4,15,16], -91725514997760), ([4,16,16], -93719279001600), ([4,16,17], -37212117196800), ([4,17,17], -61575762124800), ([4,19,19], -9797690327040), ([5,10,12], -8946548379648), ([5,11,11], -41152182610176), ([5,11,12], -113477601042432), ([5,11,13], -26819090343936), ([5,12,12], -99501636427776), ([5,12,13], -102683150862336), ([5,12,14], -9001283740416), ([5,13,13], -113337491097600), ([5,13,14], -123331503778560), ([5,13,15], -10849361725440), ([5,14,14], -120149989344000), ([5,14,15], -118156225340160), ([5,14,16], -3218926314240), ([5,15,15], -108162212659200), ([5,15,16], -91725514997760), ([5,16,16], -93719279001600), ([5,16,17], -37212117196800), ([5,17,17], -61575762124800), ([5,19,19], -9797690327040), ([6,10,12], -8946548379648), ([6,11,11], -41152182610176), ([6,11,12], -113477601042432), ([6,11,13], -26819090343936), ([6,12,12], -99501636427776), ([6,12,13], -102683150862336), ([6,12,14], -9001283740416), ([6,13,13], -113337491097600), ([6,13,14], -123331503778560), ([6,13,15], -10849361725440), ([6,14,14], -120149989344000), ([6,14,15], -118156225340160), ([6,14,16], -3218926314240), ([6,15,15], -108162212659200), ([6,15,16], -91725514997760), ([6,16,16], -93719279001600), ([6,16,17], -37212117196800), ([6,17,17], -61575762124800), ([6,19,19], -9797690327040), ([7,10,12], -8946548379648), ([7,11,11], -41152182610176), ([7,11,12], -113477601042432), ([7,11,13], -26819090343936), ([7,12,12], -99501636427776), ([7,12,13], -102683150862336), ([7,12,14], -9001283740416), ([7,13,13], -113337491097600), ([7,13,14], -123331503778560), ([7,13,15], -10849361725440), ([7,14,14], -120149989344000), ([7,14,15], -118156225340160), ([7,14,16], -3218926314240), ([7,15,15], -108162212659200), ([7,15,16], -91725514997760), ([7,16,16], -93719279001600), ([7,16,17], -37212117196800), ([7,17,17], -61575762124800), ([7,19,19], -9797690327040), ([8,10,12], -8946548379648), ([8,11,11], -41152182610176), ([8,11,12], -113477601042432), ([8,11,13], -26819090343936), ([8,12,12], -99501636427776), ([8,12,13], -102683150862336), ([8,12,14], -9001283740416), ([8,13,13], -113337491097600), ([8,13,14], -123331503778560), ([8,13,15], -10849361725440), ([8,14,14], -120149989344000), ([8,14,15], -118156225340160), ([8,14,16], -3218926314240), ([8,15,15], -108162212659200), ([8,15,16], -91725514997760), ([8,16,16], -93719279001600), ([8,16,17], -37212117196800), ([8,17,17], -61575762124800), ([8,19,19], -9797690327040), ([9,10,12], -8946548379648), ([9,11,11], -41152182610176), ([9,11,12], -113477601042432), ([9,11,13], -26819090343936), ([9,12,12], -99501636427776), ([9,12,13], -102683150862336), ([9,12,14], -9001283740416), ([9,13,13], -113337491097600), ([9,13,14], -123331503778560), ([9,13,15], -10849361725440), ([9,14,14], -120149989344000), ([9,14,15], -118156225340160), ([9,14,16], -3218926314240), ([9,15,15], -108162212659200), ([9,15,16], -91725514997760), ([9,16,16], -93719279001600), ([9,16,17], -37212117196800), ([9,17,17], -61575762124800), ([9,19,19], -9797690327040), ([10,10,12], -8946548379648), ([10,11,11], -41152182610176), ([10,11,12], -122424149422080), ([10,11,13], -26819090343936), ([10,12,12], -108448184807424), ([10,12,13], -111629699241984), ([10,12,14], -17947832120064), ([10,12,15], -8946548379648), ([10,12,16], -8946548379648), ([10,12,17], -8946548379648), ([10,12,18], -7828229832192), ([10,12,19], -5591592737280), ([10,12,20], -1118318547456), ([10,12,21], 1118318547456), ([10,12,22], 5591592737280), ([10,12,23], 10064866927104), ([10,13,13], -113337491097600), ([10,13,14], -123331503778560), ([10,13,15], -10849361725440), ([10,14,14], -120149989344000), ([10,14,15], -118156225340160), ([10,14,16], -3218926314240), ([10,15,15], -108162212659200), ([10,15,16], -91725514997760), ([10,16,16], -93719279001600), ([10,16,17], -37212117196800), ([10,17,17], -61575762124800), ([10,19,19], -9797690327040), ([11,11,11], -41152182610176), ([11,11,12], -154629783652608), ([11,11,13], -67971272954112), ([11,11,14], -41152182610176), ([11,11,15], -41152182610176), ([11,11,16], -41152182610176), ([11,11,17], -41152182610176), ([11,11,18], -36008159783904), ([11,11,19], -25720114131360), ([11,11,20], -5144022826272), ([11,11,21], 5144022826272), ([11,11,22], 25720114131360), ([11,11,23], 46296205436448), ([11,12,12], -212979237470208), ([11,12,13], -242979842248704), ([11,12,14], -122478884782848), ([11,12,15], -113477601042432), ([11,12,16], -113477601042432), ([11,12,17], -113477601042432), ([11,12,18], -99292900912128), ([11,12,19], -70923500651520), ([11,12,20], -14184700130304), ([11,12,21], 14184700130304), ([11,12,22], 70923500651520), ([11,12,23], 127662301172736), ([11,13,13], -140156581441536), ([11,13,14], -150150594122496), ([11,13,15], -37668452069376), ([11,13,16], -26819090343936), ([11,13,17], -26819090343936), ([11,13,18], -23466704050944), ([11,13,19], -16761931464960), ([11,13,20], -3352386292992), ([11,13,21], 3352386292992), ([11,13,22], 16761931464960), ([11,13,23], 30171476636928), ([11,14,14], -120149989344000), ([11,14,15], -118156225340160), ([11,14,16], -3218926314240), ([11,15,15], -108162212659200), ([11,15,16], -91725514997760), ([11,16,16], -93719279001600), ([11,16,17], -37212117196800), ([11,17,17], -61575762124800), ([11,19,19], -9797690327040), ([12,12,12], -99501636427776), ([12,12,13], -202184787290112), ([12,12,14], -108502920168192), ([12,12,15], -99501636427776), ([12,12,16], -99501636427776), ([12,12,17], -99501636427776), ([12,12,18], -87063931874304), ([12,12,19], -62188522767360), ([12,12,20], -12437704553472), ([12,12,21], 12437704553472), ([12,12,22], 62188522767360), ([12,12,23], 111939340981248), ([12,13,13], -216020641959936), ([12,13,14], -235015938381312), ([12,13,15], -113532512587776), ([12,13,16], -102683150862336), ([12,13,17], -102683150862336), ([12,13,18], -89847757004544), ([12,13,19], -64176969288960), ([12,13,20], -12835393857792), ([12,13,21], 12835393857792), ([12,13,22], 64176969288960), ([12,13,23], 115518544720128), ([12,14,14], -129151273084416), ([12,14,15], -127157509080576), ([12,14,16], -12220210054656), ([12,14,17], -9001283740416), ([12,14,18], -7876123272864), ([12,14,19], -5625802337760), ([12,14,20], -1125160467552), ([12,14,21], 1125160467552), ([12,14,22], 5625802337760), ([12,14,23], 10126444207968), ([12,15,15], -108162212659200), ([12,15,16], -91725514997760), ([12,16,16], -93719279001600), ([12,16,17], -37212117196800), ([12,17,17], -61575762124800), ([12,19,19], -9797690327040), ([13,13,13], -113337491097600), ([13,13,14], -236668994876160), ([13,13,15], -124186852823040), ([13,13,16], -113337491097600), ([13,13,17], -113337491097600), ([13,13,18], -99170304710400), ([13,13,19], -70835931936000), ([13,13,20], -14167186387200), ([13,13,21], 14167186387200), ([13,13,22], 70835931936000), ([13,13,23], 127504677484800), ([13,14,14], -243481493122560), ([13,14,15], -252337090844160), ([13,14,16], -126550430092800), ([13,14,17], -123331503778560), ([13,14,18], -107915065806240), ([13,14,19], -77082189861600), ([13,14,20], -15416437972320), ([13,14,21], 15416437972320), ([13,14,22], 77082189861600), ([13,14,23], 138747941750880), ([13,15,15], -119011574384640), ([13,15,16], -102574876723200), ([13,15,17], -10849361725440), ([13,15,18], -9493191509760), ([13,15,19], -6780851078400), ([13,15,20], -1356170215680), ([13,15,21], 1356170215680), ([13,15,22], 6780851078400), ([13,15,23], 12205531941120), ([13,16,16], -93719279001600), ([13,16,17], -37212117196800), ([13,17,17], -61575762124800), ([13,19,19], -9797690327040), ([14,14,14], -120149989344000), ([14,14,15], -238306214684160), ([14,14,16], -123368915658240), ([14,14,17], -120149989344000), ([14,14,18], -105131240676000), ([14,14,19], -75093743340000), ([14,14,20], -15018748668000), ([14,14,21], 15018748668000), ([14,14,22], 75093743340000), ([14,14,23], 135168738012000), ([14,15,15], -226318437999360), ([14,15,16], -213100666652160), ([14,15,17], -118156225340160), ([14,15,18], -103386697172640), ([14,15,19], -73847640837600), ([14,15,20], -14769528167520), ([14,15,21], 14769528167520), ([14,15,22], 73847640837600), ([14,15,23], 132925753507680), ([14,16,16], -96938205315840), ([14,16,17], -40431043511040), ([14,16,18], -2816560524960), ([14,16,19], -2011828946400), ([14,16,20], -402365789280), ([14,16,21], 402365789280), ([14,16,22], 2011828946400), ([14,16,23], 3621292103520), ([14,17,17], -61575762124800), ([14,19,19], -9797690327040), ([15,15,15], -108162212659200), ([15,15,16], -199887727656960), ([15,15,17], -108162212659200), ([15,15,18], -94641936076800), ([15,15,19], -67601382912000), ([15,15,20], -13520276582400), ([15,15,21], 13520276582400), ([15,15,22], 67601382912000), ([15,15,23], 121682489241600), ([15,16,16], -185444793999360), ([15,16,17], -128937632194560), ([15,16,18], -80259825623040), ([15,16,19], -57328446873600), ([15,16,20], -11465689374720), ([15,16,21], 11465689374720), ([15,16,22], 57328446873600), ([15,16,23], 103191204372480), ([15,17,17], -61575762124800), ([15,19,19], -9797690327040), ([16,16,16], -93719279001600), ([16,16,17], -130931396198400), ([16,16,18], -82004369126400), ([16,16,19], -58574549376000), ([16,16,20], -11714909875200), ([16,16,21], 11714909875200), ([16,16,22], 58574549376000), ([16,16,23], 105434188876800), ([16,17,17], -98787879321600), ([16,17,18], -32560602547200), ([16,17,19], -23257573248000), ([16,17,20], -4651514649600), ([16,17,21], 4651514649600), ([16,17,22], 23257573248000), ([16,17,23], 41863631846400), ([16,19,19], -9797690327040), ([17,17,17], -61575762124800), ([17,17,18], -53878791859200), ([17,17,19], -38484851328000), ([17,17,20], -7696970265600), ([17,17,21], 7696970265600), ([17,17,22], 38484851328000), ([17,17,23], 69272732390400), ([17,19,19], -9797690327040), ([18,19,19], -8572979036160), ([19,19,19], -6123556454400), ([19,19,20], -1224711290880), ([19,19,21], 1224711290880), ([19,19,22], 6123556454400), ([19,19,23], 11022401617920)]
theorem block005_data : block005 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (559159273728 : Int) atom0209) (SparsePolynomial.scale (2572011413136 : Int) atom0210)) (SparsePolynomial.merge (SparsePolynomial.scale (7092350065152 : Int) atom0211) (SparsePolynomial.merge (SparsePolynomial.scale (1676193146496 : Int) atom0212) (SparsePolynomial.scale (6218852276736 : Int) atom0213)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6417696928896 : Int) atom0214) (SparsePolynomial.scale (562580233776 : Int) atom0215)) (SparsePolynomial.merge (SparsePolynomial.scale (7083593193600 : Int) atom0216) (SparsePolynomial.merge (SparsePolynomial.scale (7708218986160 : Int) atom0217) (SparsePolynomial.scale (678085107840 : Int) atom0218))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7509374334000 : Int) atom0219) (SparsePolynomial.scale (7384764083760 : Int) atom0220)) (SparsePolynomial.merge (SparsePolynomial.scale (201182894640 : Int) atom0221) (SparsePolynomial.merge (SparsePolynomial.scale (6760138291200 : Int) atom0222) (SparsePolynomial.scale (5732844687360 : Int) atom0223)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5857454937600 : Int) atom0224) (SparsePolynomial.scale (2325757324800 : Int) atom0225)) (SparsePolynomial.merge (SparsePolynomial.scale (3848485132800 : Int) atom0226) (SparsePolynomial.merge (SparsePolynomial.scale (612355645440 : Int) atom0227) (SparsePolynomial.scale (2323663382304 : Int) atom0228)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (27162605029824 : Int) atom0229) (SparsePolynomial.scale (15418433923200 : Int) atom0230)) (SparsePolynomial.merge (SparsePolynomial.scale (11502930700800 : Int) atom0231) (SparsePolynomial.merge (SparsePolynomial.scale (8419890124800 : Int) atom0232) (SparsePolynomial.scale (5336849548800 : Int) atom0233)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2253808972800 : Int) atom0234) (SparsePolynomial.scale (2338858368000 : Int) atom0235)) (SparsePolynomial.merge (SparsePolynomial.scale (60480751161600 : Int) atom0236) (SparsePolynomial.merge (SparsePolynomial.scale (59959823616000 : Int) atom0237) (SparsePolynomial.scale (59438896070400 : Int) atom0238))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (62359415395200 : Int) atom0239) (SparsePolynomial.scale (58397040979200 : Int) atom0240)) (SparsePolynomial.merge (SparsePolynomial.scale (57876113433600 : Int) atom0241) (SparsePolynomial.merge (SparsePolynomial.scale (57355185888000 : Int) atom0242) (SparsePolynomial.scale (59840148865464 : Int) atom0243)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (68140969836984 : Int) atom0244) (SparsePolynomial.scale (79108072262208 : Int) atom0245)) (SparsePolynomial.merge (SparsePolynomial.scale (129806548299648 : Int) atom0246) (SparsePolynomial.merge (SparsePolynomial.scale (107338798828800 : Int) atom0247) (SparsePolynomial.scale (77522523724800 : Int) atom0248))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (78227402803200 : Int) atom0249) (SparsePolynomial.scale (73021026758400 : Int) atom0250)) (SparsePolynomial.merge (SparsePolynomial.scale (72781019942400 : Int) atom0251) (SparsePolynomial.merge (SparsePolynomial.scale (102984186412800 : Int) atom0252) (SparsePolynomial.scale (40961914963200 : Int) atom0253)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12512892268800 : Int) atom0254) (SparsePolynomial.scale (5205731731200 : Int) atom0255)) (SparsePolynomial.merge (SparsePolynomial.scale (4086988550400 : Int) atom0256) (SparsePolynomial.merge (SparsePolynomial.scale (65275410816000 : Int) atom0257) (SparsePolynomial.scale (132592007116800 : Int) atom0258))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (134633192601600 : Int) atom0259) (SparsePolynomial.scale (136674378086400 : Int) atom0260)) (SparsePolynomial.merge (SparsePolynomial.scale (138715563571200 : Int) atom0261) (SparsePolynomial.merge (SparsePolynomial.scale (140756749056000 : Int) atom0262) (SparsePolynomial.scale (142797934540800 : Int) atom0263)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (144839120025600 : Int) atom0264) (SparsePolynomial.scale (146880305510400 : Int) atom0265)) (SparsePolynomial.merge (SparsePolynomial.scale (153568817759808 : Int) atom0266) (SparsePolynomial.merge (SparsePolynomial.scale (205287886539648 : Int) atom0267) (SparsePolynomial.scale (183840729811200 : Int) atom0268)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (155045047449600 : Int) atom0269) (SparsePolynomial.scale (157086232934400 : Int) atom0270)) (SparsePolynomial.merge (SparsePolynomial.scale (159127418419200 : Int) atom0271) (SparsePolynomial.merge (SparsePolynomial.scale (161168603904000 : Int) atom0272) (SparsePolynomial.scale (183818320963200 : Int) atom0273)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (104477866416000 : Int) atom0274) (SparsePolynomial.scale (90763651440000 : Int) atom0275)) (SparsePolynomial.merge (SparsePolynomial.scale (11423196892800 : Int) atom0276) (SparsePolynomial.merge (SparsePolynomial.scale (20816644867200 : Int) atom0277) (SparsePolynomial.scale (64233555724800 : Int) atom0278))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (131528889676800 : Int) atom0279) (SparsePolynomial.scale (134590667904000 : Int) atom0280)) (SparsePolynomial.merge (SparsePolynomial.scale (137652446131200 : Int) atom0281) (SparsePolynomial.merge (SparsePolynomial.scale (140714224358400 : Int) atom0282) (SparsePolynomial.scale (143776002585600 : Int) atom0283)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (146837780812800 : Int) atom0284) (SparsePolynomial.scale (149899559040000 : Int) atom0285)) (SparsePolynomial.merge (SparsePolynomial.scale (157608664031808 : Int) atom0286) (SparsePolynomial.merge (SparsePolynomial.scale (210348325554048 : Int) atom0287) (SparsePolynomial.scale (189921761568000 : Int) atom0288)))))))) := by decide +kernel
theorem block005_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block005 := by
  rw [block005_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0209_nonneg g hg hA hB) (atom0210_nonneg g hg hA hB)) (add_nonneg (atom0211_nonneg g hg hA hB) (add_nonneg (atom0212_nonneg g hg hA hB) (atom0213_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0214_nonneg g hg hA hB) (atom0215_nonneg g hg hA hB)) (add_nonneg (atom0216_nonneg g hg hA hB) (add_nonneg (atom0217_nonneg g hg hA hB) (atom0218_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0219_nonneg g hg hA hB) (atom0220_nonneg g hg hA hB)) (add_nonneg (atom0221_nonneg g hg hA hB) (add_nonneg (atom0222_nonneg g hg hA hB) (atom0223_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0224_nonneg g hg hA hB) (atom0225_nonneg g hg hA hB)) (add_nonneg (atom0226_nonneg g hg hA hB) (add_nonneg (atom0227_nonneg g hg hA hB) (atom0228_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0229_nonneg g hg hA hB) (atom0230_nonneg g hg hA hB)) (add_nonneg (atom0231_nonneg g hg hA hB) (add_nonneg (atom0232_nonneg g hg hA hB) (atom0233_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0234_nonneg g hg hA hB) (atom0235_nonneg g hg hA hB)) (add_nonneg (atom0236_nonneg g hg hA hB) (add_nonneg (atom0237_nonneg g hg hA hB) (atom0238_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0239_nonneg g hg hA hB) (atom0240_nonneg g hg hA hB)) (add_nonneg (atom0241_nonneg g hg hA hB) (add_nonneg (atom0242_nonneg g hg hA hB) (atom0243_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0244_nonneg g hg hA hB) (atom0245_nonneg g hg hA hB)) (add_nonneg (atom0246_nonneg g hg hA hB) (add_nonneg (atom0247_nonneg g hg hA hB) (atom0248_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0249_nonneg g hg hA hB) (atom0250_nonneg g hg hA hB)) (add_nonneg (atom0251_nonneg g hg hA hB) (add_nonneg (atom0252_nonneg g hg hA hB) (atom0253_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0254_nonneg g hg hA hB) (atom0255_nonneg g hg hA hB)) (add_nonneg (atom0256_nonneg g hg hA hB) (add_nonneg (atom0257_nonneg g hg hA hB) (atom0258_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0259_nonneg g hg hA hB) (atom0260_nonneg g hg hA hB)) (add_nonneg (atom0261_nonneg g hg hA hB) (add_nonneg (atom0262_nonneg g hg hA hB) (atom0263_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0264_nonneg g hg hA hB) (atom0265_nonneg g hg hA hB)) (add_nonneg (atom0266_nonneg g hg hA hB) (add_nonneg (atom0267_nonneg g hg hA hB) (atom0268_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0269_nonneg g hg hA hB) (atom0270_nonneg g hg hA hB)) (add_nonneg (atom0271_nonneg g hg hA hB) (add_nonneg (atom0272_nonneg g hg hA hB) (atom0273_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0274_nonneg g hg hA hB) (atom0275_nonneg g hg hA hB)) (add_nonneg (atom0276_nonneg g hg hA hB) (add_nonneg (atom0277_nonneg g hg hA hB) (atom0278_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0279_nonneg g hg hA hB) (atom0280_nonneg g hg hA hB)) (add_nonneg (atom0281_nonneg g hg hA hB) (add_nonneg (atom0282_nonneg g hg hA hB) (atom0283_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0284_nonneg g hg hA hB) (atom0285_nonneg g hg hA hB)) (add_nonneg (atom0286_nonneg g hg hA hB) (add_nonneg (atom0287_nonneg g hg hA hB) (atom0288_nonneg g hg hA hB))))))))

end APPT.Finite24
