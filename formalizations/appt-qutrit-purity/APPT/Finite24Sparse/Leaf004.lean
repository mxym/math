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
theorem eval_atom0129 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0129 = (quadB (outer g) ![1,2,2] * g 9 * g 16) := by
  rw [atom0129_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0129_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4302807205842 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130 : SparsePolynomial.Poly := [([0,9,17], -4), ([1,9,17], -8), ([2,9,17], -16), ([3,9,17], -16), ([4,9,17], -16), ([5,9,17], -16), ([6,9,17], -16), ([7,9,17], -16), ([8,9,17], -16), ([9,9,17], -16), ([9,10,17], -16), ([9,11,17], -16), ([9,12,17], -16), ([9,13,17], -16), ([9,14,17], -16), ([9,15,17], -16), ([9,16,17], -16), ([9,17,17], -16), ([9,17,18], -8), ([9,17,20], 8), ([9,17,21], 12), ([9,17,22], 16), ([9,17,23], 18)]
theorem atom0130_data : atom0130 = SparsePolynomial.monoTimes [9,17] 1 base07 := by decide +kernel
theorem eval_atom0130 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0130 = (quadB (outer g) ![1,2,2] * g 9 * g 17) := by
  rw [atom0130_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0130_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3324175386642 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131 : SparsePolynomial.Poly := [([0,9,18], -4), ([1,9,18], -8), ([2,9,18], -16), ([3,9,18], -16), ([4,9,18], -16), ([5,9,18], -16), ([6,9,18], -16), ([7,9,18], -16), ([8,9,18], -16), ([9,9,18], -16), ([9,10,18], -16), ([9,11,18], -16), ([9,12,18], -16), ([9,13,18], -16), ([9,14,18], -16), ([9,15,18], -16), ([9,16,18], -16), ([9,17,18], -16), ([9,18,18], -8), ([9,18,20], 8), ([9,18,21], 12), ([9,18,22], 16), ([9,18,23], 18)]
theorem atom0131_data : atom0131 = SparsePolynomial.monoTimes [9,18] 1 base07 := by decide +kernel
theorem eval_atom0131 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0131 = (quadB (outer g) ![1,2,2] * g 9 * g 18) := by
  rw [atom0131_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0131_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1511071623666 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 18) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132 : SparsePolynomial.Poly := [([0,9,19], -4), ([1,9,19], -8), ([2,9,19], -16), ([3,9,19], -16), ([4,9,19], -16), ([5,9,19], -16), ([6,9,19], -16), ([7,9,19], -16), ([8,9,19], -16), ([9,9,19], -16), ([9,10,19], -16), ([9,11,19], -16), ([9,12,19], -16), ([9,13,19], -16), ([9,14,19], -16), ([9,15,19], -16), ([9,16,19], -16), ([9,17,19], -16), ([9,18,19], -8), ([9,19,20], 8), ([9,19,21], 12), ([9,19,22], 16), ([9,19,23], 18)]
theorem atom0132_data : atom0132 = SparsePolynomial.monoTimes [9,19] 1 base07 := by decide +kernel
theorem eval_atom0132 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0132 = (quadB (outer g) ![1,2,2] * g 9 * g 19) := by
  rw [atom0132_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0132_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7003753939314 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133 : SparsePolynomial.Poly := [([0,9,20], -4), ([1,9,20], -8), ([2,9,20], -16), ([3,9,20], -16), ([4,9,20], -16), ([5,9,20], -16), ([6,9,20], -16), ([7,9,20], -16), ([8,9,20], -16), ([9,9,20], -16), ([9,10,20], -16), ([9,11,20], -16), ([9,12,20], -16), ([9,13,20], -16), ([9,14,20], -16), ([9,15,20], -16), ([9,16,20], -16), ([9,17,20], -16), ([9,18,20], -8), ([9,20,20], 8), ([9,20,21], 12), ([9,20,22], 16), ([9,20,23], 18)]
theorem atom0133_data : atom0133 = SparsePolynomial.monoTimes [9,20] 1 base07 := by decide +kernel
theorem eval_atom0133 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0133 = (quadB (outer g) ![1,2,2] * g 9 * g 20) := by
  rw [atom0133_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0133_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3693823851762 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134 : SparsePolynomial.Poly := [([0,9,21], -4), ([1,9,21], -8), ([2,9,21], -16), ([3,9,21], -16), ([4,9,21], -16), ([5,9,21], -16), ([6,9,21], -16), ([7,9,21], -16), ([8,9,21], -16), ([9,9,21], -16), ([9,10,21], -16), ([9,11,21], -16), ([9,12,21], -16), ([9,13,21], -16), ([9,14,21], -16), ([9,15,21], -16), ([9,16,21], -16), ([9,17,21], -16), ([9,18,21], -8), ([9,20,21], 8), ([9,21,21], 12), ([9,21,22], 16), ([9,21,23], 18)]
theorem atom0134_data : atom0134 = SparsePolynomial.monoTimes [9,21] 1 base07 := by decide +kernel
theorem eval_atom0134 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0134 = (quadB (outer g) ![1,2,2] * g 9 * g 21) := by
  rw [atom0134_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0134_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11221399009458 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135 : SparsePolynomial.Poly := [([0,9,22], -4), ([1,9,22], -8), ([2,9,22], -16), ([3,9,22], -16), ([4,9,22], -16), ([5,9,22], -16), ([6,9,22], -16), ([7,9,22], -16), ([8,9,22], -16), ([9,9,22], -16), ([9,10,22], -16), ([9,11,22], -16), ([9,12,22], -16), ([9,13,22], -16), ([9,14,22], -16), ([9,15,22], -16), ([9,16,22], -16), ([9,17,22], -16), ([9,18,22], -8), ([9,20,22], 8), ([9,21,22], 12), ([9,22,22], 16), ([9,22,23], 18)]
theorem atom0135_data : atom0135 = SparsePolynomial.monoTimes [9,22] 1 base07 := by decide +kernel
theorem eval_atom0135 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0135 = (quadB (outer g) ![1,2,2] * g 9 * g 22) := by
  rw [atom0135_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0135_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5188983412800 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136 : SparsePolynomial.Poly := [([0,9,23], -4), ([1,9,23], -8), ([2,9,23], -16), ([3,9,23], -16), ([4,9,23], -16), ([5,9,23], -16), ([6,9,23], -16), ([7,9,23], -16), ([8,9,23], -16), ([9,9,23], -16), ([9,10,23], -16), ([9,11,23], -16), ([9,12,23], -16), ([9,13,23], -16), ([9,14,23], -16), ([9,15,23], -16), ([9,16,23], -16), ([9,17,23], -16), ([9,18,23], -8), ([9,20,23], 8), ([9,21,23], 12), ([9,22,23], 16), ([9,23,23], 18)]
theorem atom0136_data : atom0136 = SparsePolynomial.monoTimes [9,23] 1 base07 := by decide +kernel
theorem eval_atom0136 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0136 = (quadB (outer g) ![1,2,2] * g 9 * g 23) := by
  rw [atom0136_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0136_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9065709577728 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137 : SparsePolynomial.Poly := [([0,10,11], -4), ([1,10,11], -8), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -16), ([10,11,13], -16), ([10,11,14], -16), ([10,11,15], -16), ([10,11,16], -16), ([10,11,17], -16), ([10,11,18], -8), ([10,11,20], 8), ([10,11,21], 12), ([10,11,22], 16), ([10,11,23], 18)]
theorem atom0137_data : atom0137 = SparsePolynomial.monoTimes [10,11] 1 base07 := by decide +kernel
theorem eval_atom0137 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0137 = (quadB (outer g) ![1,2,2] * g 10 * g 11) := by
  rw [atom0137_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0137_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3352540847040 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138 : SparsePolynomial.Poly := [([0,10,12], -4), ([1,10,12], -8), ([2,10,12], -16), ([3,10,12], -16), ([4,10,12], -16), ([5,10,12], -16), ([6,10,12], -16), ([7,10,12], -16), ([8,10,12], -16), ([9,10,12], -16), ([10,10,12], -16), ([10,11,12], -16), ([10,12,12], -16), ([10,12,13], -16), ([10,12,14], -16), ([10,12,15], -16), ([10,12,16], -16), ([10,12,17], -16), ([10,12,18], -8), ([10,12,20], 8), ([10,12,21], 12), ([10,12,22], 16), ([10,12,23], 18)]
theorem atom0138_data : atom0138 = SparsePolynomial.monoTimes [10,12] 1 base07 := by decide +kernel
theorem eval_atom0138 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0138 = (quadB (outer g) ![1,2,2] * g 10 * g 12) := by
  rw [atom0138_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0138_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7846321654710 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139 : SparsePolynomial.Poly := [([0,10,13], -4), ([1,10,13], -8), ([2,10,13], -16), ([3,10,13], -16), ([4,10,13], -16), ([5,10,13], -16), ([6,10,13], -16), ([7,10,13], -16), ([8,10,13], -16), ([9,10,13], -16), ([10,10,13], -16), ([10,11,13], -16), ([10,12,13], -16), ([10,13,13], -16), ([10,13,14], -16), ([10,13,15], -16), ([10,13,16], -16), ([10,13,17], -16), ([10,13,18], -8), ([10,13,20], 8), ([10,13,21], 12), ([10,13,22], 16), ([10,13,23], 18)]
theorem atom0139_data : atom0139 = SparsePolynomial.monoTimes [10,13] 1 base07 := by decide +kernel
theorem eval_atom0139 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0139 = (quadB (outer g) ![1,2,2] * g 10 * g 13) := by
  rw [atom0139_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0139_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7558104430602 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140 : SparsePolynomial.Poly := [([0,10,14], -4), ([1,10,14], -8), ([2,10,14], -16), ([3,10,14], -16), ([4,10,14], -16), ([5,10,14], -16), ([6,10,14], -16), ([7,10,14], -16), ([8,10,14], -16), ([9,10,14], -16), ([10,10,14], -16), ([10,11,14], -16), ([10,12,14], -16), ([10,13,14], -16), ([10,14,14], -16), ([10,14,15], -16), ([10,14,16], -16), ([10,14,17], -16), ([10,14,18], -8), ([10,14,20], 8), ([10,14,21], 12), ([10,14,22], 16), ([10,14,23], 18)]
theorem atom0140_data : atom0140 = SparsePolynomial.monoTimes [10,14] 1 base07 := by decide +kernel
theorem eval_atom0140 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0140 = (quadB (outer g) ![1,2,2] * g 10 * g 14) := by
  rw [atom0140_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0140_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6940369358802 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141 : SparsePolynomial.Poly := [([0,10,15], -4), ([1,10,15], -8), ([2,10,15], -16), ([3,10,15], -16), ([4,10,15], -16), ([5,10,15], -16), ([6,10,15], -16), ([7,10,15], -16), ([8,10,15], -16), ([9,10,15], -16), ([10,10,15], -16), ([10,11,15], -16), ([10,12,15], -16), ([10,13,15], -16), ([10,14,15], -16), ([10,15,15], -16), ([10,15,16], -16), ([10,15,17], -16), ([10,15,18], -8), ([10,15,20], 8), ([10,15,21], 12), ([10,15,22], 16), ([10,15,23], 18)]
theorem atom0141_data : atom0141 = SparsePolynomial.monoTimes [10,15] 1 base07 := by decide +kernel
theorem eval_atom0141 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0141 = (quadB (outer g) ![1,2,2] * g 10 * g 15) := by
  rw [atom0141_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0141_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5398446374802 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142 : SparsePolynomial.Poly := [([0,10,16], -4), ([1,10,16], -8), ([2,10,16], -16), ([3,10,16], -16), ([4,10,16], -16), ([5,10,16], -16), ([6,10,16], -16), ([7,10,16], -16), ([8,10,16], -16), ([9,10,16], -16), ([10,10,16], -16), ([10,11,16], -16), ([10,12,16], -16), ([10,13,16], -16), ([10,14,16], -16), ([10,15,16], -16), ([10,16,16], -16), ([10,16,17], -16), ([10,16,18], -8), ([10,16,20], 8), ([10,16,21], 12), ([10,16,22], 16), ([10,16,23], 18)]
theorem atom0142_data : atom0142 = SparsePolynomial.monoTimes [10,16] 1 base07 := by decide +kernel
theorem eval_atom0142 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0142 = (quadB (outer g) ![1,2,2] * g 10 * g 16) := by
  rw [atom0142_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0142_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4595430281202 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143 : SparsePolynomial.Poly := [([0,10,17], -4), ([1,10,17], -8), ([2,10,17], -16), ([3,10,17], -16), ([4,10,17], -16), ([5,10,17], -16), ([6,10,17], -16), ([7,10,17], -16), ([8,10,17], -16), ([9,10,17], -16), ([10,10,17], -16), ([10,11,17], -16), ([10,12,17], -16), ([10,13,17], -16), ([10,14,17], -16), ([10,15,17], -16), ([10,16,17], -16), ([10,17,17], -16), ([10,17,18], -8), ([10,17,20], 8), ([10,17,21], 12), ([10,17,22], 16), ([10,17,23], 18)]
theorem atom0143_data : atom0143 = SparsePolynomial.monoTimes [10,17] 1 base07 := by decide +kernel
theorem eval_atom0143 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0143 = (quadB (outer g) ![1,2,2] * g 10 * g 17) := by
  rw [atom0143_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0143_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3171618034002 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144 : SparsePolynomial.Poly := [([0,10,18], -4), ([1,10,18], -8), ([2,10,18], -16), ([3,10,18], -16), ([4,10,18], -16), ([5,10,18], -16), ([6,10,18], -16), ([7,10,18], -16), ([8,10,18], -16), ([9,10,18], -16), ([10,10,18], -16), ([10,11,18], -16), ([10,12,18], -16), ([10,13,18], -16), ([10,14,18], -16), ([10,15,18], -16), ([10,16,18], -16), ([10,17,18], -16), ([10,18,18], -8), ([10,18,20], 8), ([10,18,21], 12), ([10,18,22], 16), ([10,18,23], 18)]
theorem atom0144_data : atom0144 = SparsePolynomial.monoTimes [10,18] 1 base07 := by decide +kernel
theorem eval_atom0144 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0144 = (quadB (outer g) ![1,2,2] * g 10 * g 18) := by
  rw [atom0144_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0144_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (834131593746 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 18) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145 : SparsePolynomial.Poly := [([0,10,19], -4), ([1,10,19], -8), ([2,10,19], -16), ([3,10,19], -16), ([4,10,19], -16), ([5,10,19], -16), ([6,10,19], -16), ([7,10,19], -16), ([8,10,19], -16), ([9,10,19], -16), ([10,10,19], -16), ([10,11,19], -16), ([10,12,19], -16), ([10,13,19], -16), ([10,14,19], -16), ([10,15,19], -16), ([10,16,19], -16), ([10,17,19], -16), ([10,18,19], -8), ([10,19,20], 8), ([10,19,21], 12), ([10,19,22], 16), ([10,19,23], 18)]
theorem atom0145_data : atom0145 = SparsePolynomial.monoTimes [10,19] 1 base07 := by decide +kernel
theorem eval_atom0145 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0145 = (quadB (outer g) ![1,2,2] * g 10 * g 19) := by
  rw [atom0145_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0145_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5723228982834 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146 : SparsePolynomial.Poly := [([0,10,20], -4), ([1,10,20], -8), ([2,10,20], -16), ([3,10,20], -16), ([4,10,20], -16), ([5,10,20], -16), ([6,10,20], -16), ([7,10,20], -16), ([8,10,20], -16), ([9,10,20], -16), ([10,10,20], -16), ([10,11,20], -16), ([10,12,20], -16), ([10,13,20], -16), ([10,14,20], -16), ([10,15,20], -16), ([10,16,20], -16), ([10,17,20], -16), ([10,18,20], -8), ([10,20,20], 8), ([10,20,21], 12), ([10,20,22], 16), ([10,20,23], 18)]
theorem atom0146_data : atom0146 = SparsePolynomial.monoTimes [10,20] 1 base07 := by decide +kernel
theorem eval_atom0146 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0146 = (quadB (outer g) ![1,2,2] * g 10 * g 20) := by
  rw [atom0146_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0146_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1809713968722 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147 : SparsePolynomial.Poly := [([0,10,21], -4), ([1,10,21], -8), ([2,10,21], -16), ([3,10,21], -16), ([4,10,21], -16), ([5,10,21], -16), ([6,10,21], -16), ([7,10,21], -16), ([8,10,21], -16), ([9,10,21], -16), ([10,10,21], -16), ([10,11,21], -16), ([10,12,21], -16), ([10,13,21], -16), ([10,14,21], -16), ([10,15,21], -16), ([10,16,21], -16), ([10,17,21], -16), ([10,18,21], -8), ([10,20,21], 8), ([10,21,21], 12), ([10,21,22], 16), ([10,21,23], 18)]
theorem atom0147_data : atom0147 = SparsePolynomial.monoTimes [10,21] 1 base07 := by decide +kernel
theorem eval_atom0147 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0147 = (quadB (outer g) ![1,2,2] * g 10 * g 21) := by
  rw [atom0147_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0147_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8575299701298 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148 : SparsePolynomial.Poly := [([0,10,22], -4), ([1,10,22], -8), ([2,10,22], -16), ([3,10,22], -16), ([4,10,22], -16), ([5,10,22], -16), ([6,10,22], -16), ([7,10,22], -16), ([8,10,22], -16), ([9,10,22], -16), ([10,10,22], -16), ([10,11,22], -16), ([10,12,22], -16), ([10,13,22], -16), ([10,14,22], -16), ([10,15,22], -16), ([10,16,22], -16), ([10,17,22], -16), ([10,18,22], -8), ([10,20,22], 8), ([10,21,22], 12), ([10,22,22], 16), ([10,22,23], 18)]
theorem atom0148_data : atom0148 = SparsePolynomial.monoTimes [10,22] 1 base07 := by decide +kernel
theorem eval_atom0148 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0148 = (quadB (outer g) ![1,2,2] * g 10 * g 22) := by
  rw [atom0148_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0148_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10861157920800 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149 : SparsePolynomial.Poly := [([0,10,23], -4), ([1,10,23], -8), ([2,10,23], -16), ([3,10,23], -16), ([4,10,23], -16), ([5,10,23], -16), ([6,10,23], -16), ([7,10,23], -16), ([8,10,23], -16), ([9,10,23], -16), ([10,10,23], -16), ([10,11,23], -16), ([10,12,23], -16), ([10,13,23], -16), ([10,14,23], -16), ([10,15,23], -16), ([10,16,23], -16), ([10,17,23], -16), ([10,18,23], -8), ([10,20,23], 8), ([10,21,23], 12), ([10,22,23], 16), ([10,23,23], 18)]
theorem atom0149_data : atom0149 = SparsePolynomial.monoTimes [10,23] 1 base07 := by decide +kernel
theorem eval_atom0149 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0149 = (quadB (outer g) ![1,2,2] * g 10 * g 23) := by
  rw [atom0149_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0149_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14235738281568 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150 : SparsePolynomial.Poly := [([0,11,12], -4), ([1,11,12], -8), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -16), ([11,12,13], -16), ([11,12,14], -16), ([11,12,15], -16), ([11,12,16], -16), ([11,12,17], -16), ([11,12,18], -8), ([11,12,20], 8), ([11,12,21], 12), ([11,12,22], 16), ([11,12,23], 18)]
theorem atom0150_data : atom0150 = SparsePolynomial.monoTimes [11,12] 1 base07 := by decide +kernel
theorem eval_atom0150 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0150 = (quadB (outer g) ![1,2,2] * g 11 * g 12) := by
  rw [atom0150_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0150_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3352540847040 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151 : SparsePolynomial.Poly := [([0,11,13], -4), ([1,11,13], -8), ([2,11,13], -16), ([3,11,13], -16), ([4,11,13], -16), ([5,11,13], -16), ([6,11,13], -16), ([7,11,13], -16), ([8,11,13], -16), ([9,11,13], -16), ([10,11,13], -16), ([11,11,13], -16), ([11,12,13], -16), ([11,13,13], -16), ([11,13,14], -16), ([11,13,15], -16), ([11,13,16], -16), ([11,13,17], -16), ([11,13,18], -8), ([11,13,20], 8), ([11,13,21], 12), ([11,13,22], 16), ([11,13,23], 18)]
theorem atom0151_data : atom0151 = SparsePolynomial.monoTimes [11,13] 1 base07 := by decide +kernel
theorem eval_atom0151 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0151 = (quadB (outer g) ![1,2,2] * g 11 * g 13) := by
  rw [atom0151_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0151_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7219663757460 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152 : SparsePolynomial.Poly := [([0,11,14], -4), ([1,11,14], -8), ([2,11,14], -16), ([3,11,14], -16), ([4,11,14], -16), ([5,11,14], -16), ([6,11,14], -16), ([7,11,14], -16), ([8,11,14], -16), ([9,11,14], -16), ([10,11,14], -16), ([11,11,14], -16), ([11,12,14], -16), ([11,13,14], -16), ([11,14,14], -16), ([11,14,15], -16), ([11,14,16], -16), ([11,14,17], -16), ([11,14,18], -8), ([11,14,20], 8), ([11,14,21], 12), ([11,14,22], 16), ([11,14,23], 18)]
theorem atom0152_data : atom0152 = SparsePolynomial.monoTimes [11,14] 1 base07 := by decide +kernel
theorem eval_atom0152 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0152 = (quadB (outer g) ![1,2,2] * g 11 * g 14) := by
  rw [atom0152_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0152_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7576464321756 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153 : SparsePolynomial.Poly := [([0,11,15], -4), ([1,11,15], -8), ([2,11,15], -16), ([3,11,15], -16), ([4,11,15], -16), ([5,11,15], -16), ([6,11,15], -16), ([7,11,15], -16), ([8,11,15], -16), ([9,11,15], -16), ([10,11,15], -16), ([11,11,15], -16), ([11,12,15], -16), ([11,13,15], -16), ([11,14,15], -16), ([11,15,15], -16), ([11,15,16], -16), ([11,15,17], -16), ([11,15,18], -8), ([11,15,20], 8), ([11,15,21], 12), ([11,15,22], 16), ([11,15,23], 18)]
theorem atom0153_data : atom0153 = SparsePolynomial.monoTimes [11,15] 1 base07 := by decide +kernel
theorem eval_atom0153 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0153 = (quadB (outer g) ![1,2,2] * g 11 * g 15) := by
  rw [atom0153_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0153_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5332883827356 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154 : SparsePolynomial.Poly := [([0,11,16], -4), ([1,11,16], -8), ([2,11,16], -16), ([3,11,16], -16), ([4,11,16], -16), ([5,11,16], -16), ([6,11,16], -16), ([7,11,16], -16), ([8,11,16], -16), ([9,11,16], -16), ([10,11,16], -16), ([11,11,16], -16), ([11,12,16], -16), ([11,13,16], -16), ([11,14,16], -16), ([11,15,16], -16), ([11,16,16], -16), ([11,16,17], -16), ([11,16,18], -8), ([11,16,20], 8), ([11,16,21], 12), ([11,16,22], 16), ([11,16,23], 18)]
theorem atom0154_data : atom0154 = SparsePolynomial.monoTimes [11,16] 1 base07 := by decide +kernel
theorem eval_atom0154 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0154 = (quadB (outer g) ![1,2,2] * g 11 * g 16) := by
  rw [atom0154_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0154_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4020900259356 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155 : SparsePolynomial.Poly := [([0,11,17], -4), ([1,11,17], -8), ([2,11,17], -16), ([3,11,17], -16), ([4,11,17], -16), ([5,11,17], -16), ([6,11,17], -16), ([7,11,17], -16), ([8,11,17], -16), ([9,11,17], -16), ([10,11,17], -16), ([11,11,17], -16), ([11,12,17], -16), ([11,13,17], -16), ([11,14,17], -16), ([11,15,17], -16), ([11,16,17], -16), ([11,17,17], -16), ([11,17,18], -8), ([11,17,20], 8), ([11,17,21], 12), ([11,17,22], 16), ([11,17,23], 18)]
theorem atom0155_data : atom0155 = SparsePolynomial.monoTimes [11,17] 1 base07 := by decide +kernel
theorem eval_atom0155 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0155 = (quadB (outer g) ![1,2,2] * g 11 * g 17) := by
  rw [atom0155_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0155_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2088120537756 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156 : SparsePolynomial.Poly := [([0,11,19], -4), ([1,11,19], -8), ([2,11,19], -16), ([3,11,19], -16), ([4,11,19], -16), ([5,11,19], -16), ([6,11,19], -16), ([7,11,19], -16), ([8,11,19], -16), ([9,11,19], -16), ([10,11,19], -16), ([11,11,19], -16), ([11,12,19], -16), ([11,13,19], -16), ([11,14,19], -16), ([11,15,19], -16), ([11,16,19], -16), ([11,17,19], -16), ([11,18,19], -8), ([11,19,20], 8), ([11,19,21], 12), ([11,19,22], 16), ([11,19,23], 18)]
theorem atom0156_data : atom0156 = SparsePolynomial.monoTimes [11,19] 1 base07 := by decide +kernel
theorem eval_atom0156 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0156 = (quadB (outer g) ![1,2,2] * g 11 * g 19) := by
  rw [atom0156_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0156_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3716406396252 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157 : SparsePolynomial.Poly := [([0,11,21], -4), ([1,11,21], -8), ([2,11,21], -16), ([3,11,21], -16), ([4,11,21], -16), ([5,11,21], -16), ([6,11,21], -16), ([7,11,21], -16), ([8,11,21], -16), ([9,11,21], -16), ([10,11,21], -16), ([11,11,21], -16), ([11,12,21], -16), ([11,13,21], -16), ([11,14,21], -16), ([11,15,21], -16), ([11,16,21], -16), ([11,17,21], -16), ([11,18,21], -8), ([11,20,21], 8), ([11,21,21], 12), ([11,21,22], 16), ([11,21,23], 18)]
theorem atom0157_data : atom0157 = SparsePolynomial.monoTimes [11,21] 1 base07 := by decide +kernel
theorem eval_atom0157 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0157 = (quadB (outer g) ![1,2,2] * g 11 * g 21) := by
  rw [atom0157_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0157_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5739761882844 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158 : SparsePolynomial.Poly := [([0,11,22], -4), ([1,11,22], -8), ([2,11,22], -16), ([3,11,22], -16), ([4,11,22], -16), ([5,11,22], -16), ([6,11,22], -16), ([7,11,22], -16), ([8,11,22], -16), ([9,11,22], -16), ([10,11,22], -16), ([11,11,22], -16), ([11,12,22], -16), ([11,13,22], -16), ([11,14,22], -16), ([11,15,22], -16), ([11,16,22], -16), ([11,17,22], -16), ([11,18,22], -8), ([11,20,22], 8), ([11,21,22], 12), ([11,22,22], 16), ([11,22,23], 18)]
theorem atom0158_data : atom0158 = SparsePolynomial.monoTimes [11,22] 1 base07 := by decide +kernel
theorem eval_atom0158 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0158 = (quadB (outer g) ![1,2,2] * g 11 * g 22) := by
  rw [atom0158_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0158_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16558454906400 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159 : SparsePolynomial.Poly := [([0,11,23], -4), ([1,11,23], -8), ([2,11,23], -16), ([3,11,23], -16), ([4,11,23], -16), ([5,11,23], -16), ([6,11,23], -16), ([7,11,23], -16), ([8,11,23], -16), ([9,11,23], -16), ([10,11,23], -16), ([11,11,23], -16), ([11,12,23], -16), ([11,13,23], -16), ([11,14,23], -16), ([11,15,23], -16), ([11,16,23], -16), ([11,17,23], -16), ([11,18,23], -8), ([11,20,23], 8), ([11,21,23], 12), ([11,22,23], 16), ([11,23,23], 18)]
theorem atom0159_data : atom0159 = SparsePolynomial.monoTimes [11,23] 1 base07 := by decide +kernel
theorem eval_atom0159 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0159 = (quadB (outer g) ![1,2,2] * g 11 * g 23) := by
  rw [atom0159_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0159_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14660222436288 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160 : SparsePolynomial.Poly := [([0,12,13], -4), ([1,12,13], -8), ([2,12,13], -16), ([3,12,13], -16), ([4,12,13], -16), ([5,12,13], -16), ([6,12,13], -16), ([7,12,13], -16), ([8,12,13], -16), ([9,12,13], -16), ([10,12,13], -16), ([11,12,13], -16), ([12,12,13], -16), ([12,13,13], -16), ([12,13,14], -16), ([12,13,15], -16), ([12,13,16], -16), ([12,13,17], -16), ([12,13,18], -8), ([12,13,20], 8), ([12,13,21], 12), ([12,13,22], 16), ([12,13,23], 18)]
theorem atom0160_data : atom0160 = SparsePolynomial.monoTimes [12,13] 1 base07 := by decide +kernel
theorem eval_atom0160 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0160 = (quadB (outer g) ![1,2,2] * g 12 * g 13) := by
  rw [atom0160_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0160_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3352540847040 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161 : SparsePolynomial.Poly := [([0,12,14], -4), ([1,12,14], -8), ([2,12,14], -16), ([3,12,14], -16), ([4,12,14], -16), ([5,12,14], -16), ([6,12,14], -16), ([7,12,14], -16), ([8,12,14], -16), ([9,12,14], -16), ([10,12,14], -16), ([11,12,14], -16), ([12,12,14], -16), ([12,13,14], -16), ([12,14,14], -16), ([12,14,15], -16), ([12,14,16], -16), ([12,14,17], -16), ([12,14,18], -8), ([12,14,20], 8), ([12,14,21], 12), ([12,14,22], 16), ([12,14,23], 18)]
theorem atom0161_data : atom0161 = SparsePolynomial.monoTimes [12,14] 1 base07 := by decide +kernel
theorem eval_atom0161 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0161 = (quadB (outer g) ![1,2,2] * g 12 * g 14) := by
  rw [atom0161_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0161_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7508200475160 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162 : SparsePolynomial.Poly := [([0,12,15], -4), ([1,12,15], -8), ([2,12,15], -16), ([3,12,15], -16), ([4,12,15], -16), ([5,12,15], -16), ([6,12,15], -16), ([7,12,15], -16), ([8,12,15], -16), ([9,12,15], -16), ([10,12,15], -16), ([11,12,15], -16), ([12,12,15], -16), ([12,13,15], -16), ([12,14,15], -16), ([12,15,15], -16), ([12,15,16], -16), ([12,15,17], -16), ([12,15,18], -8), ([12,15,20], 8), ([12,15,21], 12), ([12,15,22], 16), ([12,15,23], 18)]
theorem atom0162_data : atom0162 = SparsePolynomial.monoTimes [12,15] 1 base07 := by decide +kernel
theorem eval_atom0162 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0162 = (quadB (outer g) ![1,2,2] * g 12 * g 15) := by
  rw [atom0162_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0162_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5447135729736 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163 : SparsePolynomial.Poly := [([0,12,16], -4), ([1,12,16], -8), ([2,12,16], -16), ([3,12,16], -16), ([4,12,16], -16), ([5,12,16], -16), ([6,12,16], -16), ([7,12,16], -16), ([8,12,16], -16), ([9,12,16], -16), ([10,12,16], -16), ([11,12,16], -16), ([12,12,16], -16), ([12,13,16], -16), ([12,14,16], -16), ([12,15,16], -16), ([12,16,16], -16), ([12,16,17], -16), ([12,16,18], -8), ([12,16,20], 8), ([12,16,21], 12), ([12,16,22], 16), ([12,16,23], 18)]
theorem atom0163_data : atom0163 = SparsePolynomial.monoTimes [12,16] 1 base07 := by decide +kernel
theorem eval_atom0163 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0163 = (quadB (outer g) ![1,2,2] * g 12 * g 16) := by
  rw [atom0163_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0163_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3562397640936 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164 : SparsePolynomial.Poly := [([0,12,17], -4), ([1,12,17], -8), ([2,12,17], -16), ([3,12,17], -16), ([4,12,17], -16), ([5,12,17], -16), ([6,12,17], -16), ([7,12,17], -16), ([8,12,17], -16), ([9,12,17], -16), ([10,12,17], -16), ([11,12,17], -16), ([12,12,17], -16), ([12,13,17], -16), ([12,14,17], -16), ([12,15,17], -16), ([12,16,17], -16), ([12,17,17], -16), ([12,17,18], -8), ([12,17,20], 8), ([12,17,21], 12), ([12,17,22], 16), ([12,17,23], 18)]
theorem atom0164_data : atom0164 = SparsePolynomial.monoTimes [12,17] 1 base07 := by decide +kernel
theorem eval_atom0164 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0164 = (quadB (outer g) ![1,2,2] * g 12 * g 17) := by
  rw [atom0164_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0164_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1056863398536 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165 : SparsePolynomial.Poly := [([0,12,19], -4), ([1,12,19], -8), ([2,12,19], -16), ([3,12,19], -16), ([4,12,19], -16), ([5,12,19], -16), ([6,12,19], -16), ([7,12,19], -16), ([8,12,19], -16), ([9,12,19], -16), ([10,12,19], -16), ([11,12,19], -16), ([12,12,19], -16), ([12,13,19], -16), ([12,14,19], -16), ([12,15,19], -16), ([12,16,19], -16), ([12,17,19], -16), ([12,18,19], -8), ([12,19,20], 8), ([12,19,21], 12), ([12,19,22], 16), ([12,19,23], 18)]
theorem atom0165_data : atom0165 = SparsePolynomial.monoTimes [12,19] 1 base07 := by decide +kernel
theorem eval_atom0165 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0165 = (quadB (outer g) ![1,2,2] * g 12 * g 19) := by
  rw [atom0165_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0165_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (962367445512 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0166 : SparsePolynomial.Poly := [([0,12,21], -4), ([1,12,21], -8), ([2,12,21], -16), ([3,12,21], -16), ([4,12,21], -16), ([5,12,21], -16), ([6,12,21], -16), ([7,12,21], -16), ([8,12,21], -16), ([9,12,21], -16), ([10,12,21], -16), ([11,12,21], -16), ([12,12,21], -16), ([12,13,21], -16), ([12,14,21], -16), ([12,15,21], -16), ([12,16,21], -16), ([12,17,21], -16), ([12,18,21], -8), ([12,20,21], 8), ([12,21,21], 12), ([12,21,22], 16), ([12,21,23], 18)]
theorem atom0166_data : atom0166 = SparsePolynomial.monoTimes [12,21] 1 base07 := by decide +kernel
theorem eval_atom0166 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0166 = (quadB (outer g) ![1,2,2] * g 12 * g 21) := by
  rw [atom0166_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0166_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (685668350664 : Int) atom0166) := by
  rw [SparsePolynomial.eval_scale, eval_atom0166]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 21) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0167 : SparsePolynomial.Poly := [([0,12,22], -4), ([1,12,22], -8), ([2,12,22], -16), ([3,12,22], -16), ([4,12,22], -16), ([5,12,22], -16), ([6,12,22], -16), ([7,12,22], -16), ([8,12,22], -16), ([9,12,22], -16), ([10,12,22], -16), ([11,12,22], -16), ([12,12,22], -16), ([12,13,22], -16), ([12,14,22], -16), ([12,15,22], -16), ([12,16,22], -16), ([12,17,22], -16), ([12,18,22], -8), ([12,20,22], 8), ([12,21,22], 12), ([12,22,22], 16), ([12,22,23], 18)]
theorem atom0167_data : atom0167 = SparsePolynomial.monoTimes [12,22] 1 base07 := by decide +kernel
theorem eval_atom0167 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0167 = (quadB (outer g) ![1,2,2] * g 12 * g 22) := by
  rw [atom0167_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0167_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13690255714560 : Int) atom0167) := by
  rw [SparsePolynomial.eval_scale, eval_atom0167]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0168 : SparsePolynomial.Poly := [([0,12,23], -4), ([1,12,23], -8), ([2,12,23], -16), ([3,12,23], -16), ([4,12,23], -16), ([5,12,23], -16), ([6,12,23], -16), ([7,12,23], -16), ([8,12,23], -16), ([9,12,23], -16), ([10,12,23], -16), ([11,12,23], -16), ([12,12,23], -16), ([12,13,23], -16), ([12,14,23], -16), ([12,15,23], -16), ([12,16,23], -16), ([12,17,23], -16), ([12,18,23], -8), ([12,20,23], 8), ([12,21,23], 12), ([12,22,23], 16), ([12,23,23], 18)]
theorem atom0168_data : atom0168 = SparsePolynomial.monoTimes [12,23] 1 base07 := by decide +kernel
theorem eval_atom0168 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0168 = (quadB (outer g) ![1,2,2] * g 12 * g 23) := by
  rw [atom0168_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0168_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10411473587328 : Int) atom0168) := by
  rw [SparsePolynomial.eval_scale, eval_atom0168]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0169 : SparsePolynomial.Poly := [([0,13,14], -4), ([1,13,14], -8), ([2,13,14], -16), ([3,13,14], -16), ([4,13,14], -16), ([5,13,14], -16), ([6,13,14], -16), ([7,13,14], -16), ([8,13,14], -16), ([9,13,14], -16), ([10,13,14], -16), ([11,13,14], -16), ([12,13,14], -16), ([13,13,14], -16), ([13,14,14], -16), ([13,14,15], -16), ([13,14,16], -16), ([13,14,17], -16), ([13,14,18], -8), ([13,14,20], 8), ([13,14,21], 12), ([13,14,22], 16), ([13,14,23], 18)]
theorem atom0169_data : atom0169 = SparsePolynomial.monoTimes [13,14] 1 base07 := by decide +kernel
theorem eval_atom0169 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0169 = (quadB (outer g) ![1,2,2] * g 13 * g 14) := by
  rw [atom0169_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0169_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3352540847040 : Int) atom0169) := by
  rw [SparsePolynomial.eval_scale, eval_atom0169]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0170 : SparsePolynomial.Poly := [([0,13,15], -4), ([1,13,15], -8), ([2,13,15], -16), ([3,13,15], -16), ([4,13,15], -16), ([5,13,15], -16), ([6,13,15], -16), ([7,13,15], -16), ([8,13,15], -16), ([9,13,15], -16), ([10,13,15], -16), ([11,13,15], -16), ([12,13,15], -16), ([13,13,15], -16), ([13,14,15], -16), ([13,15,15], -16), ([13,15,16], -16), ([13,15,17], -16), ([13,15,18], -8), ([13,15,20], 8), ([13,15,21], 12), ([13,15,22], 16), ([13,15,23], 18)]
theorem atom0170_data : atom0170 = SparsePolynomial.monoTimes [13,15] 1 base07 := by decide +kernel
theorem eval_atom0170 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0170 = (quadB (outer g) ![1,2,2] * g 13 * g 15) := by
  rw [atom0170_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0170_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6929798142960 : Int) atom0170) := by
  rw [SparsePolynomial.eval_scale, eval_atom0170]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0171 : SparsePolynomial.Poly := [([0,13,16], -4), ([1,13,16], -8), ([2,13,16], -16), ([3,13,16], -16), ([4,13,16], -16), ([5,13,16], -16), ([6,13,16], -16), ([7,13,16], -16), ([8,13,16], -16), ([9,13,16], -16), ([10,13,16], -16), ([11,13,16], -16), ([12,13,16], -16), ([13,13,16], -16), ([13,14,16], -16), ([13,15,16], -16), ([13,16,16], -16), ([13,16,17], -16), ([13,16,18], -8), ([13,16,20], 8), ([13,16,21], 12), ([13,16,22], 16), ([13,16,23], 18)]
theorem atom0171_data : atom0171 = SparsePolynomial.monoTimes [13,16] 1 base07 := by decide +kernel
theorem eval_atom0171 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0171 = (quadB (outer g) ![1,2,2] * g 13 * g 16) := by
  rw [atom0171_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0171_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5086603594800 : Int) atom0171) := by
  rw [SparsePolynomial.eval_scale, eval_atom0171]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0172 : SparsePolynomial.Poly := [([0,13,17], -4), ([1,13,17], -8), ([2,13,17], -16), ([3,13,17], -16), ([4,13,17], -16), ([5,13,17], -16), ([6,13,17], -16), ([7,13,17], -16), ([8,13,17], -16), ([9,13,17], -16), ([10,13,17], -16), ([11,13,17], -16), ([12,13,17], -16), ([13,13,17], -16), ([13,14,17], -16), ([13,15,17], -16), ([13,16,17], -16), ([13,17,17], -16), ([13,17,18], -8), ([13,17,20], 8), ([13,17,21], 12), ([13,17,22], 16), ([13,17,23], 18)]
theorem atom0172_data : atom0172 = SparsePolynomial.monoTimes [13,17] 1 base07 := by decide +kernel
theorem eval_atom0172 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0172 = (quadB (outer g) ![1,2,2] * g 13 * g 17) := by
  rw [atom0172_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0172_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1944527785200 : Int) atom0172) := by
  rw [SparsePolynomial.eval_scale, eval_atom0172]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0173 : SparsePolynomial.Poly := [([0,13,19], -4), ([1,13,19], -8), ([2,13,19], -16), ([3,13,19], -16), ([4,13,19], -16), ([5,13,19], -16), ([6,13,19], -16), ([7,13,19], -16), ([8,13,19], -16), ([9,13,19], -16), ([10,13,19], -16), ([11,13,19], -16), ([12,13,19], -16), ([13,13,19], -16), ([13,14,19], -16), ([13,15,19], -16), ([13,16,19], -16), ([13,17,19], -16), ([13,18,19], -8), ([13,19,20], 8), ([13,19,21], 12), ([13,19,22], 16), ([13,19,23], 18)]
theorem atom0173_data : atom0173 = SparsePolynomial.monoTimes [13,19] 1 base07 := by decide +kernel
theorem eval_atom0173 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0173 = (quadB (outer g) ![1,2,2] * g 13 * g 19) := by
  rw [atom0173_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0173_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (901226541600 : Int) atom0173) := by
  rw [SparsePolynomial.eval_scale, eval_atom0173]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0174 : SparsePolynomial.Poly := [([0,13,22], -4), ([1,13,22], -8), ([2,13,22], -16), ([3,13,22], -16), ([4,13,22], -16), ([5,13,22], -16), ([6,13,22], -16), ([7,13,22], -16), ([8,13,22], -16), ([9,13,22], -16), ([10,13,22], -16), ([11,13,22], -16), ([12,13,22], -16), ([13,13,22], -16), ([13,14,22], -16), ([13,15,22], -16), ([13,16,22], -16), ([13,17,22], -16), ([13,18,22], -8), ([13,20,22], 8), ([13,21,22], 12), ([13,22,22], 16), ([13,22,23], 18)]
theorem atom0174_data : atom0174 = SparsePolynomial.monoTimes [13,22] 1 base07 := by decide +kernel
theorem eval_atom0174 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0174 = (quadB (outer g) ![1,2,2] * g 13 * g 22) := by
  rw [atom0174_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0174_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11717774938800 : Int) atom0174) := by
  rw [SparsePolynomial.eval_scale, eval_atom0174]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0175 : SparsePolynomial.Poly := [([0,13,23], -4), ([1,13,23], -8), ([2,13,23], -16), ([3,13,23], -16), ([4,13,23], -16), ([5,13,23], -16), ([6,13,23], -16), ([7,13,23], -16), ([8,13,23], -16), ([9,13,23], -16), ([10,13,23], -16), ([11,13,23], -16), ([12,13,23], -16), ([13,13,23], -16), ([13,14,23], -16), ([13,15,23], -16), ([13,16,23], -16), ([13,17,23], -16), ([13,18,23], -8), ([13,20,23], 8), ([13,21,23], 12), ([13,22,23], 16), ([13,23,23], 18)]
theorem atom0175_data : atom0175 = SparsePolynomial.monoTimes [13,23] 1 base07 := by decide +kernel
theorem eval_atom0175 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0175 = (quadB (outer g) ![1,2,2] * g 13 * g 23) := by
  rw [atom0175_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0175_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8234821702800 : Int) atom0175) := by
  rw [SparsePolynomial.eval_scale, eval_atom0175]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0176 : SparsePolynomial.Poly := [([0,14,15], -4), ([1,14,15], -8), ([2,14,15], -16), ([3,14,15], -16), ([4,14,15], -16), ([5,14,15], -16), ([6,14,15], -16), ([7,14,15], -16), ([8,14,15], -16), ([9,14,15], -16), ([10,14,15], -16), ([11,14,15], -16), ([12,14,15], -16), ([13,14,15], -16), ([14,14,15], -16), ([14,15,15], -16), ([14,15,16], -16), ([14,15,17], -16), ([14,15,18], -8), ([14,15,20], 8), ([14,15,21], 12), ([14,15,22], 16), ([14,15,23], 18)]
theorem atom0176_data : atom0176 = SparsePolynomial.monoTimes [14,15] 1 base07 := by decide +kernel
theorem eval_atom0176 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0176 = (quadB (outer g) ![1,2,2] * g 14 * g 15) := by
  rw [atom0176_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0176_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3159850811040 : Int) atom0176) := by
  rw [SparsePolynomial.eval_scale, eval_atom0176]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0177 : SparsePolynomial.Poly := [([0,14,16], -4), ([1,14,16], -8), ([2,14,16], -16), ([3,14,16], -16), ([4,14,16], -16), ([5,14,16], -16), ([6,14,16], -16), ([7,14,16], -16), ([8,14,16], -16), ([9,14,16], -16), ([10,14,16], -16), ([11,14,16], -16), ([12,14,16], -16), ([13,14,16], -16), ([14,14,16], -16), ([14,15,16], -16), ([14,16,16], -16), ([14,16,17], -16), ([14,16,18], -8), ([14,16,20], 8), ([14,16,21], 12), ([14,16,22], 16), ([14,16,23], 18)]
theorem atom0177_data : atom0177 = SparsePolynomial.monoTimes [14,16] 1 base07 := by decide +kernel
theorem eval_atom0177 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0177 = (quadB (outer g) ![1,2,2] * g 14 * g 16) := by
  rw [atom0177_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0177_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7121823730560 : Int) atom0177) := by
  rw [SparsePolynomial.eval_scale, eval_atom0177]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0178 : SparsePolynomial.Poly := [([0,14,17], -4), ([1,14,17], -8), ([2,14,17], -16), ([3,14,17], -16), ([4,14,17], -16), ([5,14,17], -16), ([6,14,17], -16), ([7,14,17], -16), ([8,14,17], -16), ([9,14,17], -16), ([10,14,17], -16), ([11,14,17], -16), ([12,14,17], -16), ([13,14,17], -16), ([14,14,17], -16), ([14,15,17], -16), ([14,16,17], -16), ([14,17,17], -16), ([14,17,18], -8), ([14,17,20], 8), ([14,17,21], 12), ([14,17,22], 16), ([14,17,23], 18)]
theorem atom0178_data : atom0178 = SparsePolynomial.monoTimes [14,17] 1 base07 := by decide +kernel
theorem eval_atom0178 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0178 = (quadB (outer g) ![1,2,2] * g 14 * g 17) := by
  rw [atom0178_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0178_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3480602202000 : Int) atom0178) := by
  rw [SparsePolynomial.eval_scale, eval_atom0178]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0179 : SparsePolynomial.Poly := [([0,14,19], -4), ([1,14,19], -8), ([2,14,19], -16), ([3,14,19], -16), ([4,14,19], -16), ([5,14,19], -16), ([6,14,19], -16), ([7,14,19], -16), ([8,14,19], -16), ([9,14,19], -16), ([10,14,19], -16), ([11,14,19], -16), ([12,14,19], -16), ([13,14,19], -16), ([14,14,19], -16), ([14,15,19], -16), ([14,16,19], -16), ([14,17,19], -16), ([14,18,19], -8), ([14,19,20], 8), ([14,19,21], 12), ([14,19,22], 16), ([14,19,23], 18)]
theorem atom0179_data : atom0179 = SparsePolynomial.monoTimes [14,19] 1 base07 := by decide +kernel
theorem eval_atom0179 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0179 = (quadB (outer g) ![1,2,2] * g 14 * g 19) := by
  rw [atom0179_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0179_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1196311658850 : Int) atom0179) := by
  rw [SparsePolynomial.eval_scale, eval_atom0179]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0180 : SparsePolynomial.Poly := [([0,14,22], -4), ([1,14,22], -8), ([2,14,22], -16), ([3,14,22], -16), ([4,14,22], -16), ([5,14,22], -16), ([6,14,22], -16), ([7,14,22], -16), ([8,14,22], -16), ([9,14,22], -16), ([10,14,22], -16), ([11,14,22], -16), ([12,14,22], -16), ([13,14,22], -16), ([14,14,22], -16), ([14,15,22], -16), ([14,16,22], -16), ([14,17,22], -16), ([14,18,22], -8), ([14,20,22], 8), ([14,21,22], 12), ([14,22,22], 16), ([14,22,23], 18)]
theorem atom0180_data : atom0180 = SparsePolynomial.monoTimes [14,22] 1 base07 := by decide +kernel
theorem eval_atom0180 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0180 = (quadB (outer g) ![1,2,2] * g 14 * g 22) := by
  rw [atom0180_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0180_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8902176472350 : Int) atom0180) := by
  rw [SparsePolynomial.eval_scale, eval_atom0180]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0181 : SparsePolynomial.Poly := [([0,14,23], -4), ([1,14,23], -8), ([2,14,23], -16), ([3,14,23], -16), ([4,14,23], -16), ([5,14,23], -16), ([6,14,23], -16), ([7,14,23], -16), ([8,14,23], -16), ([9,14,23], -16), ([10,14,23], -16), ([11,14,23], -16), ([12,14,23], -16), ([13,14,23], -16), ([14,14,23], -16), ([14,15,23], -16), ([14,16,23], -16), ([14,17,23], -16), ([14,18,23], -8), ([14,20,23], 8), ([14,21,23], 12), ([14,22,23], 16), ([14,23,23], 18)]
theorem atom0181_data : atom0181 = SparsePolynomial.monoTimes [14,23] 1 base07 := by decide +kernel
theorem eval_atom0181 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0181 = (quadB (outer g) ![1,2,2] * g 14 * g 23) := by
  rw [atom0181_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0181_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4931785192950 : Int) atom0181) := by
  rw [SparsePolynomial.eval_scale, eval_atom0181]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0182 : SparsePolynomial.Poly := [([0,15,16], -4), ([1,15,16], -8), ([2,15,16], -16), ([3,15,16], -16), ([4,15,16], -16), ([5,15,16], -16), ([6,15,16], -16), ([7,15,16], -16), ([8,15,16], -16), ([9,15,16], -16), ([10,15,16], -16), ([11,15,16], -16), ([12,15,16], -16), ([13,15,16], -16), ([14,15,16], -16), ([15,15,16], -16), ([15,16,16], -16), ([15,16,17], -16), ([15,16,18], -8), ([15,16,20], 8), ([15,16,21], 12), ([15,16,22], 16), ([15,16,23], 18)]
theorem atom0182_data : atom0182 = SparsePolynomial.monoTimes [15,16] 1 base07 := by decide +kernel
theorem eval_atom0182 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0182 = (quadB (outer g) ![1,2,2] * g 15 * g 16) := by
  rw [atom0182_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0182_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2967160775040 : Int) atom0182) := by
  rw [SparsePolynomial.eval_scale, eval_atom0182]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 15 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0183 : SparsePolynomial.Poly := [([0,15,17], -4), ([1,15,17], -8), ([2,15,17], -16), ([3,15,17], -16), ([4,15,17], -16), ([5,15,17], -16), ([6,15,17], -16), ([7,15,17], -16), ([8,15,17], -16), ([9,15,17], -16), ([10,15,17], -16), ([11,15,17], -16), ([12,15,17], -16), ([13,15,17], -16), ([14,15,17], -16), ([15,15,17], -16), ([15,16,17], -16), ([15,17,17], -16), ([15,17,18], -8), ([15,17,20], 8), ([15,17,21], 12), ([15,17,22], 16), ([15,17,23], 18)]
theorem atom0183_data : atom0183 = SparsePolynomial.monoTimes [15,17] 1 base07 := by decide +kernel
theorem eval_atom0183 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0183 = (quadB (outer g) ![1,2,2] * g 15 * g 17) := by
  rw [atom0183_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0183_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4093485379200 : Int) atom0183) := by
  rw [SparsePolynomial.eval_scale, eval_atom0183]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 15 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0184 : SparsePolynomial.Poly := [([0,15,22], -4), ([1,15,22], -8), ([2,15,22], -16), ([3,15,22], -16), ([4,15,22], -16), ([5,15,22], -16), ([6,15,22], -16), ([7,15,22], -16), ([8,15,22], -16), ([9,15,22], -16), ([10,15,22], -16), ([11,15,22], -16), ([12,15,22], -16), ([13,15,22], -16), ([14,15,22], -16), ([15,15,22], -16), ([15,16,22], -16), ([15,17,22], -16), ([15,18,22], -8), ([15,20,22], 8), ([15,21,22], 12), ([15,22,22], 16), ([15,22,23], 18)]
theorem atom0184_data : atom0184 = SparsePolynomial.monoTimes [15,22] 1 base07 := by decide +kernel
theorem eval_atom0184 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0184 = (quadB (outer g) ![1,2,2] * g 15 * g 22) := by
  rw [atom0184_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0184_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4783424436000 : Int) atom0184) := by
  rw [SparsePolynomial.eval_scale, eval_atom0184]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 15 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0185 : SparsePolynomial.Poly := [([0,16,17], -4), ([1,16,17], -8), ([2,16,17], -16), ([3,16,17], -16), ([4,16,17], -16), ([5,16,17], -16), ([6,16,17], -16), ([7,16,17], -16), ([8,16,17], -16), ([9,16,17], -16), ([10,16,17], -16), ([11,16,17], -16), ([12,16,17], -16), ([13,16,17], -16), ([14,16,17], -16), ([15,16,17], -16), ([16,16,17], -16), ([16,17,17], -16), ([16,17,18], -8), ([16,17,20], 8), ([16,17,21], 12), ([16,17,22], 16), ([16,17,23], 18)]
theorem atom0185_data : atom0185 = SparsePolynomial.monoTimes [16,17] 1 base07 := by decide +kernel
theorem eval_atom0185 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0185 = (quadB (outer g) ![1,2,2] * g 16 * g 17) := by
  rw [atom0185_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0185_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3762039724800 : Int) atom0185) := by
  rw [SparsePolynomial.eval_scale, eval_atom0185]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 16 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0186 : SparsePolynomial.Poly := [([0,22,22], -4), ([1,22,22], -8), ([2,22,22], -16), ([3,22,22], -16), ([4,22,22], -16), ([5,22,22], -16), ([6,22,22], -16), ([7,22,22], -16), ([8,22,22], -16), ([9,22,22], -16), ([10,22,22], -16), ([11,22,22], -16), ([12,22,22], -16), ([13,22,22], -16), ([14,22,22], -16), ([15,22,22], -16), ([16,22,22], -16), ([17,22,22], -16), ([18,22,22], -8), ([20,22,22], 8), ([21,22,22], 12), ([22,22,22], 16), ([22,22,23], 18)]
theorem atom0186_data : atom0186 = SparsePolynomial.monoTimes [22,22] 1 base07 := by decide +kernel
theorem eval_atom0186 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0186 = (quadB (outer g) ![1,2,2] * g 22 * g 22) := by
  rw [atom0186_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0186_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (77367969000 : Int) atom0186) := by
  rw [SparsePolynomial.eval_scale, eval_atom0186]
  have hg22 : 0 ≤ g 22 := hg 22
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 22 * g 22) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0187 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -16), ([0,1,4], -16), ([0,1,5], -16), ([0,1,6], -16), ([0,1,7], -16), ([0,1,8], -16), ([0,1,9], -16), ([0,1,10], -16), ([0,1,11], -16), ([0,1,12], -16), ([0,1,13], -16), ([0,1,14], -16), ([0,1,15], -16), ([0,1,16], -16), ([0,1,17], -16), ([0,1,18], -14), ([0,1,19], -10), ([0,1,20], -2), ([0,1,21], 2), ([0,1,22], 10), ([0,1,23], 18)]
theorem atom0187_data : atom0187 = SparsePolynomial.monoTimes [0,1] 1 base08 := by decide +kernel
theorem eval_atom0187 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0187 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0187_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0187_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (813284841600 : Int) atom0187) := by
  rw [SparsePolynomial.eval_scale, eval_atom0187]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0188 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -16), ([0,2,4], -16), ([0,2,5], -16), ([0,2,6], -16), ([0,2,7], -16), ([0,2,8], -16), ([0,2,9], -16), ([0,2,10], -16), ([0,2,11], -16), ([0,2,12], -16), ([0,2,13], -16), ([0,2,14], -16), ([0,2,15], -16), ([0,2,16], -16), ([0,2,17], -16), ([0,2,18], -14), ([0,2,19], -10), ([0,2,20], -2), ([0,2,21], 2), ([0,2,22], 10), ([0,2,23], 18)]
theorem atom0188_data : atom0188 = SparsePolynomial.monoTimes [0,2] 1 base08 := by decide +kernel
theorem eval_atom0188 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0188 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0188_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0188_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1198664913600 : Int) atom0188) := by
  rw [SparsePolynomial.eval_scale, eval_atom0188]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0189 : SparsePolynomial.Poly := [([0,0,3], -8), ([0,1,3], -12), ([0,2,3], -16), ([0,3,3], -16), ([0,3,4], -16), ([0,3,5], -16), ([0,3,6], -16), ([0,3,7], -16), ([0,3,8], -16), ([0,3,9], -16), ([0,3,10], -16), ([0,3,11], -16), ([0,3,12], -16), ([0,3,13], -16), ([0,3,14], -16), ([0,3,15], -16), ([0,3,16], -16), ([0,3,17], -16), ([0,3,18], -14), ([0,3,19], -10), ([0,3,20], -2), ([0,3,21], 2), ([0,3,22], 10), ([0,3,23], 18)]
theorem atom0189_data : atom0189 = SparsePolynomial.monoTimes [0,3] 1 base08 := by decide +kernel
theorem eval_atom0189 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0189 = (quadB (outer g) ![2,2,1] * g 0 * g 3) := by
  rw [atom0189_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0189_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1584044985600 : Int) atom0189) := by
  rw [SparsePolynomial.eval_scale, eval_atom0189]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0190 : SparsePolynomial.Poly := [([0,0,4], -8), ([0,1,4], -12), ([0,2,4], -16), ([0,3,4], -16), ([0,4,4], -16), ([0,4,5], -16), ([0,4,6], -16), ([0,4,7], -16), ([0,4,8], -16), ([0,4,9], -16), ([0,4,10], -16), ([0,4,11], -16), ([0,4,12], -16), ([0,4,13], -16), ([0,4,14], -16), ([0,4,15], -16), ([0,4,16], -16), ([0,4,17], -16), ([0,4,18], -14), ([0,4,19], -10), ([0,4,20], -2), ([0,4,21], 2), ([0,4,22], 10), ([0,4,23], 18)]
theorem atom0190_data : atom0190 = SparsePolynomial.monoTimes [0,4] 1 base08 := by decide +kernel
theorem eval_atom0190 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0190 = (quadB (outer g) ![2,2,1] * g 0 * g 4) := by
  rw [atom0190_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0190_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1969425057600 : Int) atom0190) := by
  rw [SparsePolynomial.eval_scale, eval_atom0190]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0191 : SparsePolynomial.Poly := [([0,0,5], -8), ([0,1,5], -12), ([0,2,5], -16), ([0,3,5], -16), ([0,4,5], -16), ([0,5,5], -16), ([0,5,6], -16), ([0,5,7], -16), ([0,5,8], -16), ([0,5,9], -16), ([0,5,10], -16), ([0,5,11], -16), ([0,5,12], -16), ([0,5,13], -16), ([0,5,14], -16), ([0,5,15], -16), ([0,5,16], -16), ([0,5,17], -16), ([0,5,18], -14), ([0,5,19], -10), ([0,5,20], -2), ([0,5,21], 2), ([0,5,22], 10), ([0,5,23], 18)]
theorem atom0191_data : atom0191 = SparsePolynomial.monoTimes [0,5] 1 base08 := by decide +kernel
theorem eval_atom0191 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0191 = (quadB (outer g) ![2,2,1] * g 0 * g 5) := by
  rw [atom0191_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0191_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1494443412000 : Int) atom0191) := by
  rw [SparsePolynomial.eval_scale, eval_atom0191]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0192 : SparsePolynomial.Poly := [([0,0,6], -8), ([0,1,6], -12), ([0,2,6], -16), ([0,3,6], -16), ([0,4,6], -16), ([0,5,6], -16), ([0,6,6], -16), ([0,6,7], -16), ([0,6,8], -16), ([0,6,9], -16), ([0,6,10], -16), ([0,6,11], -16), ([0,6,12], -16), ([0,6,13], -16), ([0,6,14], -16), ([0,6,15], -16), ([0,6,16], -16), ([0,6,17], -16), ([0,6,18], -14), ([0,6,19], -10), ([0,6,20], -2), ([0,6,21], 2), ([0,6,22], 10), ([0,6,23], 18)]
theorem atom0192_data : atom0192 = SparsePolynomial.monoTimes [0,6] 1 base08 := by decide +kernel
theorem eval_atom0192 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0192 = (quadB (outer g) ![2,2,1] * g 0 * g 6) := by
  rw [atom0192_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0192_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2740185201600 : Int) atom0192) := by
  rw [SparsePolynomial.eval_scale, eval_atom0192]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0193 : SparsePolynomial.Poly := [([0,0,7], -8), ([0,1,7], -12), ([0,2,7], -16), ([0,3,7], -16), ([0,4,7], -16), ([0,5,7], -16), ([0,6,7], -16), ([0,7,7], -16), ([0,7,8], -16), ([0,7,9], -16), ([0,7,10], -16), ([0,7,11], -16), ([0,7,12], -16), ([0,7,13], -16), ([0,7,14], -16), ([0,7,15], -16), ([0,7,16], -16), ([0,7,17], -16), ([0,7,18], -14), ([0,7,19], -10), ([0,7,20], -2), ([0,7,21], 2), ([0,7,22], 10), ([0,7,23], 18)]
theorem atom0193_data : atom0193 = SparsePolynomial.monoTimes [0,7] 1 base08 := by decide +kernel
theorem eval_atom0193 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0193 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0193_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0193_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3125565273600 : Int) atom0193) := by
  rw [SparsePolynomial.eval_scale, eval_atom0193]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0194 : SparsePolynomial.Poly := [([0,0,8], -8), ([0,1,8], -12), ([0,2,8], -16), ([0,3,8], -16), ([0,4,8], -16), ([0,5,8], -16), ([0,6,8], -16), ([0,7,8], -16), ([0,8,8], -16), ([0,8,9], -16), ([0,8,10], -16), ([0,8,11], -16), ([0,8,12], -16), ([0,8,13], -16), ([0,8,14], -16), ([0,8,15], -16), ([0,8,16], -16), ([0,8,17], -16), ([0,8,18], -14), ([0,8,19], -10), ([0,8,20], -2), ([0,8,21], 2), ([0,8,22], 10), ([0,8,23], 18)]
theorem atom0194_data : atom0194 = SparsePolynomial.monoTimes [0,8] 1 base08 := by decide +kernel
theorem eval_atom0194 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0194 = (quadB (outer g) ![2,2,1] * g 0 * g 8) := by
  rw [atom0194_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0194_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3510945345600 : Int) atom0194) := by
  rw [SparsePolynomial.eval_scale, eval_atom0194]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0195 : SparsePolynomial.Poly := [([0,0,9], -8), ([0,1,9], -12), ([0,2,9], -16), ([0,3,9], -16), ([0,4,9], -16), ([0,5,9], -16), ([0,6,9], -16), ([0,7,9], -16), ([0,8,9], -16), ([0,9,9], -16), ([0,9,10], -16), ([0,9,11], -16), ([0,9,12], -16), ([0,9,13], -16), ([0,9,14], -16), ([0,9,15], -16), ([0,9,16], -16), ([0,9,17], -16), ([0,9,18], -14), ([0,9,19], -10), ([0,9,20], -2), ([0,9,21], 2), ([0,9,22], 10), ([0,9,23], 18)]
theorem atom0195_data : atom0195 = SparsePolynomial.monoTimes [0,9] 1 base08 := by decide +kernel
theorem eval_atom0195 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0195 = (quadB (outer g) ![2,2,1] * g 0 * g 9) := by
  rw [atom0195_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0195_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3144852786834 : Int) atom0195) := by
  rw [SparsePolynomial.eval_scale, eval_atom0195]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0196 : SparsePolynomial.Poly := [([0,0,10], -8), ([0,1,10], -12), ([0,2,10], -16), ([0,3,10], -16), ([0,4,10], -16), ([0,5,10], -16), ([0,6,10], -16), ([0,7,10], -16), ([0,8,10], -16), ([0,9,10], -16), ([0,10,10], -16), ([0,10,11], -16), ([0,10,12], -16), ([0,10,13], -16), ([0,10,14], -16), ([0,10,15], -16), ([0,10,16], -16), ([0,10,17], -16), ([0,10,18], -14), ([0,10,19], -10), ([0,10,20], -2), ([0,10,21], 2), ([0,10,22], 10), ([0,10,23], 18)]
theorem atom0196_data : atom0196 = SparsePolynomial.monoTimes [0,10] 1 base08 := by decide +kernel
theorem eval_atom0196 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0196 = (quadB (outer g) ![2,2,1] * g 0 * g 10) := by
  rw [atom0196_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0196_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1324795729554 : Int) atom0196) := by
  rw [SparsePolynomial.eval_scale, eval_atom0196]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0197 : SparsePolynomial.Poly := [([0,0,15], -8), ([0,1,15], -12), ([0,2,15], -16), ([0,3,15], -16), ([0,4,15], -16), ([0,5,15], -16), ([0,6,15], -16), ([0,7,15], -16), ([0,8,15], -16), ([0,9,15], -16), ([0,10,15], -16), ([0,11,15], -16), ([0,12,15], -16), ([0,13,15], -16), ([0,14,15], -16), ([0,15,15], -16), ([0,15,16], -16), ([0,15,17], -16), ([0,15,18], -14), ([0,15,19], -10), ([0,15,20], -2), ([0,15,21], 2), ([0,15,22], 10), ([0,15,23], 18)]
theorem atom0197_data : atom0197 = SparsePolynomial.monoTimes [0,15] 1 base08 := by decide +kernel
theorem eval_atom0197 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0197 = (quadB (outer g) ![2,2,1] * g 0 * g 15) := by
  rw [atom0197_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0197_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78928416000 : Int) atom0197) := by
  rw [SparsePolynomial.eval_scale, eval_atom0197]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0198 : SparsePolynomial.Poly := [([0,0,16], -8), ([0,1,16], -12), ([0,2,16], -16), ([0,3,16], -16), ([0,4,16], -16), ([0,5,16], -16), ([0,6,16], -16), ([0,7,16], -16), ([0,8,16], -16), ([0,9,16], -16), ([0,10,16], -16), ([0,11,16], -16), ([0,12,16], -16), ([0,13,16], -16), ([0,14,16], -16), ([0,15,16], -16), ([0,16,16], -16), ([0,16,17], -16), ([0,16,18], -14), ([0,16,19], -10), ([0,16,20], -2), ([0,16,21], 2), ([0,16,22], 10), ([0,16,23], 18)]
theorem atom0198_data : atom0198 = SparsePolynomial.monoTimes [0,16] 1 base08 := by decide +kernel
theorem eval_atom0198 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0198 = (quadB (outer g) ![2,2,1] * g 0 * g 16) := by
  rw [atom0198_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0198_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1635670612800 : Int) atom0198) := by
  rw [SparsePolynomial.eval_scale, eval_atom0198]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0199 : SparsePolynomial.Poly := [([0,0,17], -8), ([0,1,17], -12), ([0,2,17], -16), ([0,3,17], -16), ([0,4,17], -16), ([0,5,17], -16), ([0,6,17], -16), ([0,7,17], -16), ([0,8,17], -16), ([0,9,17], -16), ([0,10,17], -16), ([0,11,17], -16), ([0,12,17], -16), ([0,13,17], -16), ([0,14,17], -16), ([0,15,17], -16), ([0,16,17], -16), ([0,17,17], -16), ([0,17,18], -14), ([0,17,19], -10), ([0,17,20], -2), ([0,17,21], 2), ([0,17,22], 10), ([0,17,23], 18)]
theorem atom0199_data : atom0199 = SparsePolynomial.monoTimes [0,17] 1 base08 := by decide +kernel
theorem eval_atom0199 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0199 = (quadB (outer g) ![2,2,1] * g 0 * g 17) := by
  rw [atom0199_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0199_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1950820502400 : Int) atom0199) := by
  rw [SparsePolynomial.eval_scale, eval_atom0199]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0200 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -16), ([1,1,7], -16), ([1,1,8], -16), ([1,1,9], -16), ([1,1,10], -16), ([1,1,11], -16), ([1,1,12], -16), ([1,1,13], -16), ([1,1,14], -16), ([1,1,15], -16), ([1,1,16], -16), ([1,1,17], -16), ([1,1,18], -14), ([1,1,19], -10), ([1,1,20], -2), ([1,1,21], 2), ([1,1,22], 10), ([1,1,23], 18)]
theorem atom0200_data : atom0200 = SparsePolynomial.monoTimes [1,1] 1 base08 := by decide +kernel
theorem eval_atom0200 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0200 = (quadB (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0200_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0200_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1084379788800 : Int) atom0200) := by
  rw [SparsePolynomial.eval_scale, eval_atom0200]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0201 : SparsePolynomial.Poly := [([0,1,23], -8), ([1,1,23], -12), ([1,2,23], -16), ([1,3,23], -16), ([1,4,23], -16), ([1,5,23], -16), ([1,6,23], -16), ([1,7,23], -16), ([1,8,23], -16), ([1,9,23], -16), ([1,10,23], -16), ([1,11,23], -16), ([1,12,23], -16), ([1,13,23], -16), ([1,14,23], -16), ([1,15,23], -16), ([1,16,23], -16), ([1,17,23], -16), ([1,18,23], -14), ([1,19,23], -10), ([1,20,23], -2), ([1,21,23], 2), ([1,22,23], 10), ([1,23,23], 18)]
theorem atom0201_data : atom0201 = SparsePolynomial.monoTimes [1,23] 1 base08 := by decide +kernel
theorem eval_atom0201 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0201 = (quadB (outer g) ![2,2,1] * g 1 * g 23) := by
  rw [atom0201_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0201_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1242961473600 : Int) atom0201) := by
  rw [SparsePolynomial.eval_scale, eval_atom0201]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0202 : SparsePolynomial.Poly := [([0,2,23], -8), ([1,2,23], -12), ([2,2,23], -16), ([2,3,23], -16), ([2,4,23], -16), ([2,5,23], -16), ([2,6,23], -16), ([2,7,23], -16), ([2,8,23], -16), ([2,9,23], -16), ([2,10,23], -16), ([2,11,23], -16), ([2,12,23], -16), ([2,13,23], -16), ([2,14,23], -16), ([2,15,23], -16), ([2,16,23], -16), ([2,17,23], -16), ([2,18,23], -14), ([2,19,23], -10), ([2,20,23], -2), ([2,21,23], 2), ([2,22,23], 10), ([2,23,23], 18)]
theorem atom0202_data : atom0202 = SparsePolynomial.monoTimes [2,23] 1 base08 := by decide +kernel
theorem eval_atom0202 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0202 = (quadB (outer g) ![2,2,1] * g 2 * g 23) := by
  rw [atom0202_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0202_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1511620110000 : Int) atom0202) := by
  rw [SparsePolynomial.eval_scale, eval_atom0202]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg23 : 0 ≤ g 23 := hg 23
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 2 * g 23) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0203 : SparsePolynomial.Poly := [([0,7,8], -8), ([1,7,8], -12), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -16), ([7,8,13], -16), ([7,8,14], -16), ([7,8,15], -16), ([7,8,16], -16), ([7,8,17], -16), ([7,8,18], -14), ([7,8,19], -10), ([7,8,20], -2), ([7,8,21], 2), ([7,8,22], 10), ([7,8,23], 18)]
theorem atom0203_data : atom0203 = SparsePolynomial.monoTimes [7,8] 1 base08 := by decide +kernel
theorem eval_atom0203 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0203 = (quadB (outer g) ![2,2,1] * g 7 * g 8) := by
  rw [atom0203_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0203_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3724897730400 : Int) atom0203) := by
  rw [SparsePolynomial.eval_scale, eval_atom0203]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0204 : SparsePolynomial.Poly := [([0,7,9], -8), ([1,7,9], -12), ([2,7,9], -16), ([3,7,9], -16), ([4,7,9], -16), ([5,7,9], -16), ([6,7,9], -16), ([7,7,9], -16), ([7,8,9], -16), ([7,9,9], -16), ([7,9,10], -16), ([7,9,11], -16), ([7,9,12], -16), ([7,9,13], -16), ([7,9,14], -16), ([7,9,15], -16), ([7,9,16], -16), ([7,9,17], -16), ([7,9,18], -14), ([7,9,19], -10), ([7,9,20], -2), ([7,9,21], 2), ([7,9,22], 10), ([7,9,23], 18)]
theorem atom0204_data : atom0204 = SparsePolynomial.monoTimes [7,9] 1 base08 := by decide +kernel
theorem eval_atom0204 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0204 = (quadB (outer g) ![2,2,1] * g 7 * g 9) := by
  rw [atom0204_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0204_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (284787224832 : Int) atom0204) := by
  rw [SparsePolynomial.eval_scale, eval_atom0204]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0205 : SparsePolynomial.Poly := [([0,8,9], -8), ([1,8,9], -12), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -16), ([8,9,13], -16), ([8,9,14], -16), ([8,9,15], -16), ([8,9,16], -16), ([8,9,17], -16), ([8,9,18], -14), ([8,9,19], -10), ([8,9,20], -2), ([8,9,21], 2), ([8,9,22], 10), ([8,9,23], 18)]
theorem atom0205_data : atom0205 = SparsePolynomial.monoTimes [8,9] 1 base08 := by decide +kernel
theorem eval_atom0205 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0205 = (quadB (outer g) ![2,2,1] * g 8 * g 9) := by
  rw [atom0205_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0205_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4217032512000 : Int) atom0205) := by
  rw [SparsePolynomial.eval_scale, eval_atom0205]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0206 : SparsePolynomial.Poly := [([0,9,10], -8), ([1,9,10], -12), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -16), ([9,10,13], -16), ([9,10,14], -16), ([9,10,15], -16), ([9,10,16], -16), ([9,10,17], -16), ([9,10,18], -14), ([9,10,19], -10), ([9,10,20], -2), ([9,10,21], 2), ([9,10,22], 10), ([9,10,23], 18)]
theorem atom0206_data : atom0206 = SparsePolynomial.monoTimes [9,10] 1 base08 := by decide +kernel
theorem eval_atom0206 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0206 = (quadB (outer g) ![2,2,1] * g 9 * g 10) := by
  rw [atom0206_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0206_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (598889491200 : Int) atom0206) := by
  rw [SparsePolynomial.eval_scale, eval_atom0206]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0207 : SparsePolynomial.Poly := [([0,9,11], -8), ([1,9,11], -12), ([2,9,11], -16), ([3,9,11], -16), ([4,9,11], -16), ([5,9,11], -16), ([6,9,11], -16), ([7,9,11], -16), ([8,9,11], -16), ([9,9,11], -16), ([9,10,11], -16), ([9,11,11], -16), ([9,11,12], -16), ([9,11,13], -16), ([9,11,14], -16), ([9,11,15], -16), ([9,11,16], -16), ([9,11,17], -16), ([9,11,18], -14), ([9,11,19], -10), ([9,11,20], -2), ([9,11,21], 2), ([9,11,22], 10), ([9,11,23], 18)]
theorem atom0207_data : atom0207 = SparsePolynomial.monoTimes [9,11] 1 base08 := by decide +kernel
theorem eval_atom0207 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0207 = (quadB (outer g) ![2,2,1] * g 9 * g 11) := by
  rw [atom0207_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0207_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2732171321088 : Int) atom0207) := by
  rw [SparsePolynomial.eval_scale, eval_atom0207]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0208 : SparsePolynomial.Poly := [([0,10,11], -8), ([1,10,11], -12), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -16), ([10,11,13], -16), ([10,11,14], -16), ([10,11,15], -16), ([10,11,16], -16), ([10,11,17], -16), ([10,11,18], -14), ([10,11,19], -10), ([10,11,20], -2), ([10,11,21], 2), ([10,11,22], 10), ([10,11,23], 18)]
theorem atom0208_data : atom0208 = SparsePolynomial.monoTimes [10,11] 1 base08 := by decide +kernel
theorem eval_atom0208 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom0208 = (quadB (outer g) ![2,2,1] * g 10 * g 11) := by
  rw [atom0208_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0208_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3522438404496 : Int) atom0208) := by
  rw [SparsePolynomial.eval_scale, eval_atom0208]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def block004 : SparsePolynomial.Poly := [([0,0,1], -6506278732800), ([0,0,2], -9589319308800), ([0,0,3], -12672359884800), ([0,0,4], -15755400460800), ([0,0,5], -11955547296000), ([0,0,6], -21921481612800), ([0,0,7], -25004522188800), ([0,0,8], -28087562764800), ([0,0,9], -25158822294672), ([0,0,10], -10598365836432), ([0,0,15], -631427328000), ([0,0,16], -13085364902400), ([0,0,17], -15606564019200), ([0,1,1], -18434456409600), ([0,1,2], -27396536428800), ([0,1,3], -32021097292800), ([0,1,4], -36645658156800), ([0,1,5], -30945878409600), ([0,1,6], -45894779884800), ([0,1,7], -50519340748800), ([0,1,8], -55143901612800), ([0,1,9], -50750790907608), ([0,1,10], -28910106220248), ([0,1,11], -13012557465600), ([0,1,12], -13012557465600), ([0,1,13], -13012557465600), ([0,1,14], -13012557465600), ([0,1,15], -13959698457600), ([0,1,16], -32640604819200), ([0,1,17], -36422403494400), ([0,1,18], -11385987782400), ([0,1,19], -8132848416000), ([0,1,20], -1626569683200), ([0,1,21], 1626569683200), ([0,1,22], 8132848416000), ([0,1,23], 4695435360000), ([0,2,2], -19178638617600), ([0,2,3], -44523358387200), ([0,2,4], -50689439539200), ([0,2,5], -43089733209600), ([0,2,6], -63021601843200), ([0,2,7], -69187682995200), ([0,2,8], -75353764147200), ([0,2,9], -69496283206944), ([0,2,10], -40375370290464), ([0,2,11], -19178638617600), ([0,2,12], -19178638617600), ([0,2,13], -19178638617600), ([0,2,14], -19178638617600), ([0,2,15], -20441493273600), ([0,2,16], -45349368422400), ([0,2,17], -50391766656000), ([0,2,18], -16781308790400), ([0,2,19], -11986649136000), ([0,2,20], -2397329827200), ([0,2,21], 2397329827200), ([0,2,22], 11986649136000), ([0,2,23], 9483007564800), ([0,3,3], -25344719769600), ([0,3,4], -56855520691200), ([0,3,5], -49255814361600), ([0,3,6], -69187682995200), ([0,3,7], -75353764147200), ([0,3,8], -81519845299200), ([0,3,9], -75662364358944), ([0,3,10], -46541451442464), ([0,3,11], -25344719769600), ([0,3,12], -25344719769600), ([0,3,13], -25344719769600), ([0,3,14], -25344719769600), ([0,3,15], -26607574425600), ([0,3,16], -51515449574400), ([0,3,17], -56557847808000), ([0,3,18], -22176629798400), ([0,3,19], -15840449856000), ([0,3,20], -3168089971200), ([0,3,21], 3168089971200), ([0,3,22], 15840449856000), ([0,3,23], 28512809740800), ([0,4,4], -31510800921600), ([0,4,5], -55421895513600), ([0,4,6], -75353764147200), ([0,4,7], -81519845299200), ([0,4,8], -87685926451200), ([0,4,9], -81828445510944), ([0,4,10], -52707532594464), ([0,4,11], -31510800921600), ([0,4,12], -31510800921600), ([0,4,13], -31510800921600), ([0,4,14], -31510800921600), ([0,4,15], -32773655577600), ([0,4,16], -57681530726400), ([0,4,17], -62723928960000), ([0,4,18], -27571950806400), ([0,4,19], -19694250576000), ([0,4,20], -3938850115200), ([0,4,21], 3938850115200), ([0,4,22], 19694250576000), ([0,4,23], 35449651036800), ([0,5,5], -23911094592000), ([0,5,6], -67754057817600), ([0,5,7], -73920138969600), ([0,5,8], -80086220121600), ([0,5,9], -74228739181344), ([0,5,10], -45107826264864), ([0,5,11], -23911094592000), ([0,5,12], -23911094592000), ([0,5,13], -23911094592000), ([0,5,14], -23911094592000), ([0,5,15], -25173949248000), ([0,5,16], -50081824396800), ([0,5,17], -55124222630400), ([0,5,18], -20922207768000), ([0,5,19], -14944434120000), ([0,5,20], -2988886824000), ([0,5,21], 2988886824000), ([0,5,22], 14944434120000), ([0,5,23], 26899981416000), ([0,6,6], -43842963225600), ([0,6,7], -93852007603200), ([0,6,8], -100018088755200), ([0,6,9], -94160607814944), ([0,6,10], -65039694898464), ([0,6,11], -43842963225600), ([0,6,12], -43842963225600), ([0,6,13], -43842963225600), ([0,6,14], -43842963225600), ([0,6,15], -45105817881600), ([0,6,16], -70013693030400), ([0,6,17], -75056091264000), ([0,6,18], -38362592822400), ([0,6,19], -27401852016000), ([0,6,20], -5480370403200), ([0,6,21], 5480370403200), ([0,6,22], 27401852016000), ([0,6,23], 49323333628800), ([0,7,7], -50009044377600), ([0,7,8], -135983351750400), ([0,7,9], -102604986765600), ([0,7,10], -71205776050464), ([0,7,11], -50009044377600), ([0,7,12], -50009044377600), ([0,7,13], -50009044377600), ([0,7,14], -50009044377600), ([0,7,15], -51271899033600), ([0,7,16], -76179774182400), ([0,7,17], -81222172416000), ([0,7,18], -43757913830400), ([0,7,19], -31255652736000), ([0,7,20], -6251130547200), ([0,7,21], 6251130547200), ([0,7,22], 31255652736000), ([0,7,23], 56260174924800), ([0,8,8], -56175125529600), ([0,8,9], -140229030214944), ([0,8,10], -77371857202464), ([0,8,11], -56175125529600), ([0,8,12], -56175125529600), ([0,8,13], -56175125529600), ([0,8,14], -56175125529600), ([0,8,15], -57437980185600), ([0,8,16], -82345855334400), ([0,8,17], -87388253568000), ([0,8,18], -49153234838400), ([0,8,19], -35109453456000), ([0,8,20], -7021890691200), ([0,8,21], 7021890691200), ([0,8,22], 35109453456000), ([0,8,23], 63197016220800), ([0,9,9], -50317644589344), ([0,9,10], -76305492191808), ([0,9,11], -72175015158048), ([0,9,12], -50317644589344), ([0,9,13], -50317644589344), ([0,9,14], -50317644589344), ([0,9,15], -51580499245344), ([0,9,16], -93699603217512), ([0,9,17], -94827474174312), ([0,9,18], -50072225510340), ([0,9,19], -59463543625596), ([0,9,20], -21065000980716), ([0,9,21], -38595890464164), ([0,9,22], 10692594217140), ([0,9,23], 20344511852100), ([0,10,10], -21196731672864), ([0,10,11], -62786402296992), ([0,10,12], -52582018291704), ([0,10,13], -51429149395272), ([0,10,14], -48958209108072), ([0,10,15], -44053371828072), ([0,10,16], -65749182602472), ([0,10,17], -65096331847272), ([0,10,18], -21883666588740), ([0,10,19], -36140873226876), ([0,10,20], -9888447333996), ([0,10,21], -31651607346084), ([0,10,22], -30196674387660), ([0,10,23], -33096629994300), ([0,11,12], -13410163388160), ([0,11,13], -28878655029840), ([0,11,14], -30305857287024), ([0,11,15], -22594389965424), ([0,11,16], -42254330842224), ([0,11,17], -39565610189424), ([0,11,19], -14865625585008), ([0,11,21], -22959047531376), ([0,11,22], -66233819625600), ([0,11,23], -58640889745152), ([0,12,13], -13410163388160), ([0,12,14], -30032801900640), ([0,12,15], -23051397574944), ([0,12,16], -40420320368544), ([0,12,17], -35440581632544), ([0,12,19], -3849469782048), ([0,12,21], -2742673402656), ([0,12,22], -54761022858240), ([0,12,23], -41645894349312), ([0,13,14], -13410163388160), ([0,13,15], -28982047227840), ([0,13,16], -46517144184000), ([0,13,17], -38991239179200), ([0,13,19], -3604906166400), ([0,13,22], -46871099755200), ([0,13,23], -32939286811200), ([0,14,15], -13902257900160), ([0,14,16], -54658024727040), ([0,14,17], -45135536846400), ([0,14,19], -4785246635400), ([0,14,22], -35608705889400), ([0,14,23], -19727140771800), ([0,15,15], -1262854656000), ([0,15,16], -39302227560960), ([0,15,17], -48849924211200), ([0,15,18], -1104997824000), ([0,15,19], -789284160000), ([0,15,20], -157856832000), ([0,15,21], 157856832000), ([0,15,22], -18344413584000), ([0,15,23], 1420711488000), ([0,16,16], -26170729804800), ([0,16,17], -72432016742400), ([0,16,18], -22899388579200), ([0,16,19], -16356706128000), ([0,16,20], -3271341225600), ([0,16,21], 3271341225600), ([0,16,22], 16356706128000), ([0,16,23], 29442071030400), ([0,17,17], -31213128038400), ([0,17,18], -27311487033600), ([0,17,19], -19508205024000), ([0,17,20], -3901641004800), ([0,17,21], 3901641004800), ([0,17,22], 19508205024000), ([0,17,23], 35114769043200), ([0,22,22], -309471876000), ([1,1,1], -13012557465600), ([1,1,2], -17350076620800), ([1,1,3], -17350076620800), ([1,1,4], -17350076620800), ([1,1,5], -17350076620800), ([1,1,6], -17350076620800), ([1,1,7], -17350076620800), ([1,1,8], -17350076620800), ([1,1,9], -17350076620800), ([1,1,10], -17350076620800), ([1,1,11], -17350076620800), ([1,1,12], -17350076620800), ([1,1,13], -17350076620800), ([1,1,14], -17350076620800), ([1,1,15], -17350076620800), ([1,1,16], -17350076620800), ([1,1,17], -17350076620800), ([1,1,18], -15181317043200), ([1,1,19], -10843797888000), ([1,1,20], -2168759577600), ([1,1,21], 2168759577600), ([1,1,22], 10843797888000), ([1,1,23], 4603298515200), ([1,2,23], -38026824897600), ([1,3,23], -19887383577600), ([1,4,23], -19887383577600), ([1,5,23], -19887383577600), ([1,6,23], -19887383577600), ([1,7,8], -44698772764800), ([1,7,9], -3417446697984), ([1,7,23], -19887383577600), ([1,8,9], -50604390144000), ([1,8,23], -19887383577600), ([1,9,10], -7186673894400), ([1,9,11], -32786055853056), ([1,9,16], -34422457646736), ([1,9,17], -26593403093136), ([1,9,18], -12088572989328), ([1,9,19], -56030031514512), ([1,9,20], -29550590814096), ([1,9,21], -89771192075664), ([1,9,22], -41511867302400), ([1,9,23], -92413060199424), ([1,10,11], -69089587630272), ([1,10,12], -62770573237680), ([1,10,13], -60464835444816), ([1,10,14], -55522954870416), ([1,10,15], -43187570998416), ([1,10,16], -36763442249616), ([1,10,17], -25372944272016), ([1,10,18], -6673052749968), ([1,10,19], -45785831862672), ([1,10,20], -14477711749776), ([1,10,21], -68602397610384), ([1,10,22], -86889263366400), ([1,10,23], -133773289830144), ([1,11,12], -26820326776320), ([1,11,13], -57757310059680), ([1,11,14], -60611714574048), ([1,11,15], -42663070618848), ([1,11,16], -32167202074848), ([1,11,17], -16704964302048), ([1,11,19], -29731251170016), ([1,11,21], -45918095062752), ([1,11,22], -132467639251200), ([1,11,23], -137169163067904), ([1,12,13], -26820326776320), ([1,12,14], -60065603801280), ([1,12,15], -43577085837888), ([1,12,16], -28499181127488), ([1,12,17], -8454907188288), ([1,12,19], -7698939564096), ([1,12,21], -5485346805312), ([1,12,22], -109522045716480), ([1,12,23], -103179172276224), ([1,13,14], -26820326776320), ([1,13,15], -55438385143680), ([1,13,16], -40692828758400), ([1,13,17], -15556222281600), ([1,13,19], -7209812332800), ([1,13,22], -93742199510400), ([1,13,23], -85765957200000), ([1,14,15], -25278806488320), ([1,14,16], -56974589844480), ([1,14,17], -27844817616000), ([1,14,19], -9570493270800), ([1,14,22], -71217411778800), ([1,14,23], -59341665121200), ([1,15,16], -23737286200320), ([1,15,17], -32747883033600), ([1,15,22], -38267395488000), ([1,15,23], -19887383577600), ([1,16,17], -30096317798400), ([1,16,23], -19887383577600), ([1,17,23], -19887383577600), ([1,18,23], -17401460630400), ([1,19,23], -12429614736000), ([1,20,23], -2485922947200), ([1,21,23], 2485922947200), ([1,22,22], -618943752000), ([1,22,23], 12429614736000), ([1,23,23], 22373306524800), ([2,2,23], -24185921760000), ([2,3,23], -24185921760000), ([2,4,23], -24185921760000), ([2,5,23], -24185921760000), ([2,6,23], -24185921760000), ([2,7,8], -59598363686400), ([2,7,9], -4556595597312), ([2,7,23], -24185921760000), ([2,8,9], -67472520192000), ([2,8,23], -24185921760000), ([2,9,10], -9582231859200), ([2,9,11], -43714741137408), ([2,9,16], -68844915293472), ([2,9,17], -53186806186272), ([2,9,18], -24177145978656), ([2,9,19], -112060063029024), ([2,9,20], -59101181628192), ([2,9,21], -179542384151328), ([2,9,22], -83023734604800), ([2,9,23], -169237275003648), ([2,10,11], -109999668024576), ([2,10,12], -125541146475360), ([2,10,13], -120929670889632), ([2,10,14], -111045909740832), ([2,10,15], -86375141996832), ([2,10,16], -73526884499232), ([2,10,17], -50745888544032), ([2,10,18], -13346105499936), ([2,10,19], -91571663725344), ([2,10,20], -28955423499552), ([2,10,21], -137204795220768), ([2,10,22], -173778526732800), ([2,10,23], -251957734265088), ([2,11,12], -53640653552640), ([2,11,13], -115514620119360), ([2,11,14], -121223429148096), ([2,11,15], -85326141237696), ([2,11,16], -64334404149696), ([2,11,17], -33409928604096), ([2,11,19], -59462502340032), ([2,11,21], -91836190125504), ([2,11,22], -264935278502400), ([2,11,23], -258749480740608), ([2,12,13], -53640653552640), ([2,12,14], -120131207602560), ([2,12,15], -87154171675776), ([2,12,16], -56998362254976), ([2,12,17], -16909814376576), ([2,12,19], -15397879128192), ([2,12,21], -10970693610624), ([2,12,22], -219044091432960), ([2,12,23], -190769499157248), ([2,13,14], -53640653552640), ([2,13,15], -110876770287360), ([2,13,16], -81385657516800), ([2,13,17], -31112444563200), ([2,13,19], -14419624665600), ([2,13,22], -187484399020800), ([2,13,23], -155943069004800), ([2,14,15], -50557612976640), ([2,14,16], -113949179688960), ([2,14,17], -55689635232000), ([2,14,19], -19140986541600), ([2,14,22], -142434823557600), ([2,14,23], -103094484847200), ([2,15,16], -47474572400640), ([2,15,17], -65495766067200), ([2,15,22], -76534790976000), ([2,15,23], -24185921760000), ([2,16,17], -60192635596800), ([2,16,23], -24185921760000), ([2,17,23], -24185921760000), ([2,18,23], -21162681540000), ([2,19,23], -15116201100000), ([2,20,23], -3023240220000), ([2,21,23], 3023240220000), ([2,22,22], -1237887504000), ([2,22,23], 15116201100000), ([2,23,23], 27209161980000), ([3,7,8], -59598363686400), ([3,7,9], -4556595597312), ([3,8,9], -67472520192000), ([3,9,10], -9582231859200), ([3,9,11], -43714741137408), ([3,9,16], -68844915293472), ([3,9,17], -53186806186272), ([3,9,18], -24177145978656), ([3,9,19], -112060063029024), ([3,9,20], -59101181628192), ([3,9,21], -179542384151328), ([3,9,22], -83023734604800), ([3,9,23], -145051353243648), ([3,10,11], -109999668024576), ([3,10,12], -125541146475360), ([3,10,13], -120929670889632), ([3,10,14], -111045909740832), ([3,10,15], -86375141996832), ([3,10,16], -73526884499232), ([3,10,17], -50745888544032), ([3,10,18], -13346105499936), ([3,10,19], -91571663725344), ([3,10,20], -28955423499552), ([3,10,21], -137204795220768), ([3,10,22], -173778526732800), ([3,10,23], -227771812505088), ([3,11,12], -53640653552640), ([3,11,13], -115514620119360), ([3,11,14], -121223429148096), ([3,11,15], -85326141237696), ([3,11,16], -64334404149696), ([3,11,17], -33409928604096), ([3,11,19], -59462502340032), ([3,11,21], -91836190125504), ([3,11,22], -264935278502400), ([3,11,23], -234563558980608), ([3,12,13], -53640653552640), ([3,12,14], -120131207602560), ([3,12,15], -87154171675776), ([3,12,16], -56998362254976), ([3,12,17], -16909814376576), ([3,12,19], -15397879128192), ([3,12,21], -10970693610624), ([3,12,22], -219044091432960), ([3,12,23], -166583577397248), ([3,13,14], -53640653552640), ([3,13,15], -110876770287360), ([3,13,16], -81385657516800), ([3,13,17], -31112444563200), ([3,13,19], -14419624665600), ([3,13,22], -187484399020800), ([3,13,23], -131757147244800), ([3,14,15], -50557612976640), ([3,14,16], -113949179688960), ([3,14,17], -55689635232000), ([3,14,19], -19140986541600), ([3,14,22], -142434823557600), ([3,14,23], -78908563087200), ([3,15,16], -47474572400640), ([3,15,17], -65495766067200), ([3,15,22], -76534790976000), ([3,16,17], -60192635596800), ([3,22,22], -1237887504000), ([4,7,8], -59598363686400), ([4,7,9], -4556595597312), ([4,8,9], -67472520192000), ([4,9,10], -9582231859200), ([4,9,11], -43714741137408), ([4,9,16], -68844915293472), ([4,9,17], -53186806186272), ([4,9,18], -24177145978656), ([4,9,19], -112060063029024), ([4,9,20], -59101181628192), ([4,9,21], -179542384151328), ([4,9,22], -83023734604800), ([4,9,23], -145051353243648), ([4,10,11], -109999668024576), ([4,10,12], -125541146475360), ([4,10,13], -120929670889632), ([4,10,14], -111045909740832), ([4,10,15], -86375141996832), ([4,10,16], -73526884499232), ([4,10,17], -50745888544032), ([4,10,18], -13346105499936), ([4,10,19], -91571663725344), ([4,10,20], -28955423499552), ([4,10,21], -137204795220768), ([4,10,22], -173778526732800), ([4,10,23], -227771812505088), ([4,11,12], -53640653552640), ([4,11,13], -115514620119360), ([4,11,14], -121223429148096), ([4,11,15], -85326141237696), ([4,11,16], -64334404149696), ([4,11,17], -33409928604096), ([4,11,19], -59462502340032), ([4,11,21], -91836190125504), ([4,11,22], -264935278502400), ([4,11,23], -234563558980608), ([4,12,13], -53640653552640), ([4,12,14], -120131207602560), ([4,12,15], -87154171675776), ([4,12,16], -56998362254976), ([4,12,17], -16909814376576), ([4,12,19], -15397879128192), ([4,12,21], -10970693610624), ([4,12,22], -219044091432960), ([4,12,23], -166583577397248), ([4,13,14], -53640653552640), ([4,13,15], -110876770287360), ([4,13,16], -81385657516800), ([4,13,17], -31112444563200), ([4,13,19], -14419624665600), ([4,13,22], -187484399020800), ([4,13,23], -131757147244800), ([4,14,15], -50557612976640), ([4,14,16], -113949179688960), ([4,14,17], -55689635232000), ([4,14,19], -19140986541600), ([4,14,22], -142434823557600), ([4,14,23], -78908563087200), ([4,15,16], -47474572400640), ([4,15,17], -65495766067200), ([4,15,22], -76534790976000), ([4,16,17], -60192635596800), ([4,22,22], -1237887504000), ([5,7,8], -59598363686400), ([5,7,9], -4556595597312), ([5,8,9], -67472520192000), ([5,9,10], -9582231859200), ([5,9,11], -43714741137408), ([5,9,16], -68844915293472), ([5,9,17], -53186806186272), ([5,9,18], -24177145978656), ([5,9,19], -112060063029024), ([5,9,20], -59101181628192), ([5,9,21], -179542384151328), ([5,9,22], -83023734604800), ([5,9,23], -145051353243648), ([5,10,11], -109999668024576), ([5,10,12], -125541146475360), ([5,10,13], -120929670889632), ([5,10,14], -111045909740832), ([5,10,15], -86375141996832), ([5,10,16], -73526884499232), ([5,10,17], -50745888544032), ([5,10,18], -13346105499936), ([5,10,19], -91571663725344), ([5,10,20], -28955423499552), ([5,10,21], -137204795220768), ([5,10,22], -173778526732800), ([5,10,23], -227771812505088), ([5,11,12], -53640653552640), ([5,11,13], -115514620119360), ([5,11,14], -121223429148096), ([5,11,15], -85326141237696), ([5,11,16], -64334404149696), ([5,11,17], -33409928604096), ([5,11,19], -59462502340032), ([5,11,21], -91836190125504), ([5,11,22], -264935278502400), ([5,11,23], -234563558980608), ([5,12,13], -53640653552640), ([5,12,14], -120131207602560), ([5,12,15], -87154171675776), ([5,12,16], -56998362254976), ([5,12,17], -16909814376576), ([5,12,19], -15397879128192), ([5,12,21], -10970693610624), ([5,12,22], -219044091432960), ([5,12,23], -166583577397248), ([5,13,14], -53640653552640), ([5,13,15], -110876770287360), ([5,13,16], -81385657516800), ([5,13,17], -31112444563200), ([5,13,19], -14419624665600), ([5,13,22], -187484399020800), ([5,13,23], -131757147244800), ([5,14,15], -50557612976640), ([5,14,16], -113949179688960), ([5,14,17], -55689635232000), ([5,14,19], -19140986541600), ([5,14,22], -142434823557600), ([5,14,23], -78908563087200), ([5,15,16], -47474572400640), ([5,15,17], -65495766067200), ([5,15,22], -76534790976000), ([5,16,17], -60192635596800), ([5,22,22], -1237887504000), ([6,7,8], -59598363686400), ([6,7,9], -4556595597312), ([6,8,9], -67472520192000), ([6,9,10], -9582231859200), ([6,9,11], -43714741137408), ([6,9,16], -68844915293472), ([6,9,17], -53186806186272), ([6,9,18], -24177145978656), ([6,9,19], -112060063029024), ([6,9,20], -59101181628192), ([6,9,21], -179542384151328), ([6,9,22], -83023734604800), ([6,9,23], -145051353243648), ([6,10,11], -109999668024576), ([6,10,12], -125541146475360), ([6,10,13], -120929670889632), ([6,10,14], -111045909740832), ([6,10,15], -86375141996832), ([6,10,16], -73526884499232), ([6,10,17], -50745888544032), ([6,10,18], -13346105499936), ([6,10,19], -91571663725344), ([6,10,20], -28955423499552), ([6,10,21], -137204795220768), ([6,10,22], -173778526732800), ([6,10,23], -227771812505088), ([6,11,12], -53640653552640), ([6,11,13], -115514620119360), ([6,11,14], -121223429148096), ([6,11,15], -85326141237696), ([6,11,16], -64334404149696), ([6,11,17], -33409928604096), ([6,11,19], -59462502340032), ([6,11,21], -91836190125504), ([6,11,22], -264935278502400), ([6,11,23], -234563558980608), ([6,12,13], -53640653552640), ([6,12,14], -120131207602560), ([6,12,15], -87154171675776), ([6,12,16], -56998362254976), ([6,12,17], -16909814376576), ([6,12,19], -15397879128192), ([6,12,21], -10970693610624), ([6,12,22], -219044091432960), ([6,12,23], -166583577397248), ([6,13,14], -53640653552640), ([6,13,15], -110876770287360), ([6,13,16], -81385657516800), ([6,13,17], -31112444563200), ([6,13,19], -14419624665600), ([6,13,22], -187484399020800), ([6,13,23], -131757147244800), ([6,14,15], -50557612976640), ([6,14,16], -113949179688960), ([6,14,17], -55689635232000), ([6,14,19], -19140986541600), ([6,14,22], -142434823557600), ([6,14,23], -78908563087200), ([6,15,16], -47474572400640), ([6,15,17], -65495766067200), ([6,15,22], -76534790976000), ([6,16,17], -60192635596800), ([6,22,22], -1237887504000), ([7,7,8], -59598363686400), ([7,7,9], -4556595597312), ([7,8,8], -59598363686400), ([7,8,9], -131627479475712), ([7,8,10], -59598363686400), ([7,8,11], -59598363686400), ([7,8,12], -59598363686400), ([7,8,13], -59598363686400), ([7,8,14], -59598363686400), ([7,8,15], -59598363686400), ([7,8,16], -59598363686400), ([7,8,17], -59598363686400), ([7,8,18], -52148568225600), ([7,8,19], -37248977304000), ([7,8,20], -7449795460800), ([7,8,21], 7449795460800), ([7,8,22], 37248977304000), ([7,8,23], 67048159147200), ([7,9,9], -4556595597312), ([7,9,10], -14138827456512), ([7,9,11], -48271336734720), ([7,9,12], -4556595597312), ([7,9,13], -4556595597312), ([7,9,14], -4556595597312), ([7,9,15], -4556595597312), ([7,9,16], -73401510890784), ([7,9,17], -57743401783584), ([7,9,18], -28164167126304), ([7,9,19], -114907935277344), ([7,9,20], -59670756077856), ([7,9,21], -178972809701664), ([7,9,22], -80175862356480), ([7,9,23], -139925183196672), ([7,10,11], -109999668024576), ([7,10,12], -125541146475360), ([7,10,13], -120929670889632), ([7,10,14], -111045909740832), ([7,10,15], -86375141996832), ([7,10,16], -73526884499232), ([7,10,17], -50745888544032), ([7,10,18], -13346105499936), ([7,10,19], -91571663725344), ([7,10,20], -28955423499552), ([7,10,21], -137204795220768), ([7,10,22], -173778526732800), ([7,10,23], -227771812505088), ([7,11,12], -53640653552640), ([7,11,13], -115514620119360), ([7,11,14], -121223429148096), ([7,11,15], -85326141237696), ([7,11,16], -64334404149696), ([7,11,17], -33409928604096), ([7,11,19], -59462502340032), ([7,11,21], -91836190125504), ([7,11,22], -264935278502400), ([7,11,23], -234563558980608), ([7,12,13], -53640653552640), ([7,12,14], -120131207602560), ([7,12,15], -87154171675776), ([7,12,16], -56998362254976), ([7,12,17], -16909814376576), ([7,12,19], -15397879128192), ([7,12,21], -10970693610624), ([7,12,22], -219044091432960), ([7,12,23], -166583577397248), ([7,13,14], -53640653552640), ([7,13,15], -110876770287360), ([7,13,16], -81385657516800), ([7,13,17], -31112444563200), ([7,13,19], -14419624665600), ([7,13,22], -187484399020800), ([7,13,23], -131757147244800), ([7,14,15], -50557612976640), ([7,14,16], -113949179688960), ([7,14,17], -55689635232000), ([7,14,19], -19140986541600), ([7,14,22], -142434823557600), ([7,14,23], -78908563087200), ([7,15,16], -47474572400640), ([7,15,17], -65495766067200), ([7,15,22], -76534790976000), ([7,16,17], -60192635596800), ([7,22,22], -1237887504000), ([8,8,9], -67472520192000), ([8,9,9], -67472520192000), ([8,9,10], -77054752051200), ([8,9,11], -111187261329408), ([8,9,12], -67472520192000), ([8,9,13], -67472520192000), ([8,9,14], -67472520192000), ([8,9,15], -67472520192000), ([8,9,16], -136317435485472), ([8,9,17], -120659326378272), ([8,9,18], -83215601146656), ([8,9,19], -154230388149024), ([8,9,20], -67535246652192), ([8,9,21], -171108319127328), ([8,9,22], -40853409484800), ([8,9,23], -69144768027648), ([8,10,11], -109999668024576), ([8,10,12], -125541146475360), ([8,10,13], -120929670889632), ([8,10,14], -111045909740832), ([8,10,15], -86375141996832), ([8,10,16], -73526884499232), ([8,10,17], -50745888544032), ([8,10,18], -13346105499936), ([8,10,19], -91571663725344), ([8,10,20], -28955423499552), ([8,10,21], -137204795220768), ([8,10,22], -173778526732800), ([8,10,23], -227771812505088), ([8,11,12], -53640653552640), ([8,11,13], -115514620119360), ([8,11,14], -121223429148096), ([8,11,15], -85326141237696), ([8,11,16], -64334404149696), ([8,11,17], -33409928604096), ([8,11,19], -59462502340032), ([8,11,21], -91836190125504), ([8,11,22], -264935278502400), ([8,11,23], -234563558980608), ([8,12,13], -53640653552640), ([8,12,14], -120131207602560), ([8,12,15], -87154171675776), ([8,12,16], -56998362254976), ([8,12,17], -16909814376576), ([8,12,19], -15397879128192), ([8,12,21], -10970693610624), ([8,12,22], -219044091432960), ([8,12,23], -166583577397248), ([8,13,14], -53640653552640), ([8,13,15], -110876770287360), ([8,13,16], -81385657516800), ([8,13,17], -31112444563200), ([8,13,19], -14419624665600), ([8,13,22], -187484399020800), ([8,13,23], -131757147244800), ([8,14,15], -50557612976640), ([8,14,16], -113949179688960), ([8,14,17], -55689635232000), ([8,14,19], -19140986541600), ([8,14,22], -142434823557600), ([8,14,23], -78908563087200), ([8,15,16], -47474572400640), ([8,15,17], -65495766067200), ([8,15,22], -76534790976000), ([8,16,17], -60192635596800), ([8,22,22], -1237887504000), ([9,9,10], -9582231859200), ([9,9,11], -43714741137408), ([9,9,16], -68844915293472), ([9,9,17], -53186806186272), ([9,9,18], -24177145978656), ([9,9,19], -112060063029024), ([9,9,20], -59101181628192), ([9,9,21], -179542384151328), ([9,9,22], -83023734604800), ([9,9,23], -145051353243648), ([9,10,10], -9582231859200), ([9,10,11], -163296641021184), ([9,10,12], -135123378334560), ([9,10,13], -130511902748832), ([9,10,14], -120628141600032), ([9,10,15], -95957373856032), ([9,10,16], -151954031651904), ([9,10,17], -113514926589504), ([9,10,18], -45907704355392), ([9,10,19], -209620621666368), ([9,10,20], -89254384110144), ([9,10,21], -315549400389696), ([9,10,22], -250813366425600), ([9,10,23], -362043154907136), ([9,11,11], -43714741137408), ([9,11,12], -97355394690048), ([9,11,13], -159229361256768), ([9,11,14], -164938170285504), ([9,11,15], -129040882375104), ([9,11,16], -176894060580576), ([9,11,17], -130311475927776), ([9,11,18], -62427544473888), ([9,11,19], -198844278579936), ([9,11,20], -64565524270368), ([9,11,21], -265914231634656), ([9,11,22], -320637299896320), ([9,11,23], -330435828444672), ([9,12,13], -53640653552640), ([9,12,14], -120131207602560), ([9,12,15], -87154171675776), ([9,12,16], -125843277548448), ([9,12,17], -70096620562848), ([9,12,18], -24177145978656), ([9,12,19], -127457942157216), ([9,12,20], -59101181628192), ([9,12,21], -190513077761952), ([9,12,22], -302067826037760), ([9,12,23], -311634930640896), ([9,13,14], -53640653552640), ([9,13,15], -110876770287360), ([9,13,16], -150230572810272), ([9,13,17], -84299250749472), ([9,13,18], -24177145978656), ([9,13,19], -126479687694624), ([9,13,20], -59101181628192), ([9,13,21], -179542384151328), ([9,13,22], -270508133625600), ([9,13,23], -276808500488448), ([9,14,15], -50557612976640), ([9,14,16], -182794094982432), ([9,14,17], -108876441418272), ([9,14,18], -24177145978656), ([9,14,19], -131201049570624), ([9,14,20], -59101181628192), ([9,14,21], -179542384151328), ([9,14,22], -225458558162400), ([9,14,23], -223959916330848), ([9,15,16], -116319487694112), ([9,15,17], -118682572253472), ([9,15,18], -24177145978656), ([9,15,19], -112060063029024), ([9,15,20], -59101181628192), ([9,15,21], -179542384151328), ([9,15,22], -159558525580800), ([9,15,23], -145051353243648), ([9,16,16], -68844915293472), ([9,16,17], -182224357076544), ([9,16,18], -58599603625392), ([9,16,19], -112060063029024), ([9,16,20], -24678723981456), ([9,16,21], -127908697681224), ([9,16,22], -14178819311328), ([9,16,23], -67600823538492), ([9,17,17], -53186806186272), ([9,17,18], -50770549071792), ([9,17,19], -112060063029024), ([9,17,20], -32507778535056), ([9,17,21], -139652279511624), ([9,17,22], -29836928418528), ([9,17,23], -85216196284092), ([9,18,18], -12088572989328), ([9,18,19], -56030031514512), ([9,18,20], -17462017824768), ([9,18,21], -71638332591672), ([9,18,22], -17334721323744), ([9,18,23], -45326387395836), ([9,19,20], 56030031514512), ([9,19,21], 84045047271768), ([9,19,22], 112060063029024), ([9,19,23], 126067570907652), ([9,20,20], 29550590814096), ([9,20,21], 134097078296808), ([9,20,22], 100613048930592), ([9,20,23], 139014505953540), ([9,21,21], 134656788113496), ([9,21,22], 241810185104928), ([9,21,23], 310773697102980), ([9,22,22], 81785847100800), ([9,22,23], 238453054674048), ([9,23,23], 163182772399104), ([10,10,11], -109999668024576), ([10,10,12], -125541146475360), ([10,10,13], -120929670889632), ([10,10,14], -111045909740832), ([10,10,15], -86375141996832), ([10,10,16], -73526884499232), ([10,10,17], -50745888544032), ([10,10,18], -13346105499936), ([10,10,19], -91571663725344), ([10,10,20], -28955423499552), ([10,10,21], -137204795220768), ([10,10,22], -173778526732800), ([10,10,23], -227771812505088), ([10,11,11], -109999668024576), ([10,11,12], -289181468052576), ([10,11,13], -346443959033568), ([10,11,14], -342269006913504), ([10,11,15], -281700951259104), ([10,11,16], -247860956673504), ([10,11,17], -194155485172704), ([10,11,18], -89480569939200), ([10,11,19], -186258550110336), ([10,11,20], -9179973532224), ([10,11,21], -181765618372800), ([10,11,22], -349848767637600), ([10,11,23], -338585744958048), ([10,12,12], -125541146475360), ([10,12,13], -300111470917632), ([10,12,14], -356718263818752), ([10,12,15], -299070460147968), ([10,12,16], -256066393229568), ([10,12,17], -193196849395968), ([10,12,18], -76116678737616), ([10,12,19], -106969542853536), ([10,12,20], 33815149738128), ([10,12,21], -54019628974872), ([10,12,22], -267281471690400), ([10,12,23], -253121600117556), ([10,13,13], -120929670889632), ([10,13,14], -285616234183104), ([10,13,15], -318181583173824), ([10,13,16], -275842212905664), ([10,13,17], -202788003996864), ([10,13,18], -73810940944752), ([10,13,19], -105991288390944), ([10,13,20], 31509411945264), ([10,13,21], -46507542053544), ([10,13,22], -240333254863968), ([10,13,23], -223483079999052), ([10,14,14], -111045909740832), ([10,14,15], -247978664714304), ([10,14,16], -298521973929024), ([10,14,17], -217481433516864), ([10,14,18], -68869060370352), ([10,14,19], -110712650266944), ([10,14,20], 26567531370864), ([10,14,21], -53920362915144), ([10,14,22], -205167440549568), ([10,14,23], -181753727133852), ([10,15,15], -86375141996832), ([10,15,16], -207376598896704), ([10,15,17], -202616796608064), ([10,15,18], -56533676498352), ([10,15,19], -91571663725344), ([10,15,20], 14232147498864), ([10,15,21], -72423438723144), ([10,15,22], -163938175711968), ([10,15,23], -130599777758652), ([10,16,16], -73526884499232), ([10,16,17], -184465408640064), ([10,16,18], -50109547749552), ([10,16,19], -91571663725344), ([10,16,20], 7808018750064), ([10,16,21], -82059631846344), ([10,16,22], -100251642233568), ([10,16,23], -145054067443452), ([10,17,17], -50745888544032), ([10,17,18], -38719049771952), ([10,17,19], -91571663725344), ([10,17,20], -3582479227536), ([10,17,21], -99145378812744), ([10,17,22], -123032638188768), ([10,17,23], -170682687893052), ([10,18,18], -6673052749968), ([10,18,19], -45785831862672), ([10,18,20], -7804658999808), ([10,18,21], -58592818485432), ([10,18,22], -73543157866464), ([10,18,23], -98871537565116), ([10,19,20], 45785831862672), ([10,19,21], 68678747794008), ([10,19,22], 91571663725344), ([10,19,23], 103018121691012), ([10,20,20], 14477711749776), ([10,20,21], 90318965235048), ([10,20,22], 115844686865952), ([10,20,23], 146460757689540), ([10,21,21], 102903596415576), ([10,21,22], 267538690270368), ([10,21,23], 325184254002180), ([10,22,22], 172540639228800), ([10,22,23], 423272655079488), ([10,23,23], 256243289068224), ([11,11,12], -53640653552640), ([11,11,13], -115514620119360), ([11,11,14], -121223429148096), ([11,11,15], -85326141237696), ([11,11,16], -64334404149696), ([11,11,17], -33409928604096), ([11,11,19], -59462502340032), ([11,11,21], -91836190125504), ([11,11,22], -264935278502400), ([11,11,23], -234563558980608), ([11,12,12], -53640653552640), ([11,12,13], -222795927224640), ([11,12,14], -294995290303296), ([11,12,15], -226120966466112), ([11,12,16], -174973419957312), ([11,12,17], -103960396533312), ([11,12,18], -26820326776320), ([11,12,19], -74860381468224), ([11,12,20], 26820326776320), ([11,12,21], -62576393571648), ([11,12,22], -430338716382720), ([11,12,23], -340801401131136), ([11,13,13], -115514620119360), ([11,13,14], -290378702820096), ([11,13,15], -311717531644416), ([11,13,16], -261234681785856), ([11,13,17], -180036993286656), ([11,13,18], -57757310059680), ([11,13,19], -73882127005632), ([11,13,20], 57757310059680), ([11,13,21], -5200225035984), ([11,13,22], -336905057403840), ([11,13,23], -236366758591128), ([11,14,14], -121223429148096), ([11,14,15], -257107183362432), ([11,14,16], -299507012986752), ([11,14,17], -210322992984192), ([11,14,18], -60611714574048), ([11,14,19], -78603488881632), ([11,14,20], 60611714574048), ([11,14,21], -918618264432), ([11,14,22], -286146672911904), ([11,14,23], -177095764276200), ([11,15,15], -85326141237696), ([11,15,16], -197135117788032), ([11,15,17], -184231835908992), ([11,15,18], -42663070618848), ([11,15,19], -59462502340032), ([11,15,20], 42663070618848), ([11,15,21], -27841584197232), ([11,15,22], -256143928240704), ([11,15,23], -138571650088200), ([11,16,16], -64334404149696), ([11,16,17], -157936968350592), ([11,16,18], -32167202074848), ([11,16,19], -59462502340032), ([11,16,20], 32167202074848), ([11,16,21], -43585387013232), ([11,16,22], -200600874352704), ([11,16,23], -162187354312200), ([11,17,17], -33409928604096), ([11,17,18], -16704964302048), ([11,17,19], -59462502340032), ([11,17,20], 16704964302048), ([11,17,21], -66778743672432), ([11,17,22], -231525349898304), ([11,17,23], -196977389301000), ([11,18,19], -29731251170016), ([11,18,21], -45918095062752), ([11,18,22], -132467639251200), ([11,18,23], -117281779490304), ([11,19,20], 29731251170016), ([11,19,21], 44596876755024), ([11,19,22], 59462502340032), ([11,19,23], 66895315132536), ([11,20,21], 45918095062752), ([11,20,22], 132467639251200), ([11,20,23], 117281779490304), ([11,21,21], 68877142594128), ([11,21,22], 290537649002304), ([11,21,23], 279238383126648), ([11,22,22], 263697390998400), ([11,22,23], 532615747295808), ([11,23,23], 263884003853184), ([12,12,13], -53640653552640), ([12,12,14], -120131207602560), ([12,12,15], -87154171675776), ([12,12,16], -56998362254976), ([12,12,17], -16909814376576), ([12,12,19], -15397879128192), ([12,12,21], -10970693610624), ([12,12,22], -219044091432960), ([12,12,23], -166583577397248), ([12,13,13], -53640653552640), ([12,13,14], -227412514707840), ([12,13,15], -251671595515776), ([12,13,16], -192024673324416), ([12,13,17], -101662912492416), ([12,13,18], -26820326776320), ([12,13,19], -29817503793792), ([12,13,20], 26820326776320), ([12,13,21], 29259796553856), ([12,13,22], -352887836901120), ([12,13,23], -237994989395328), ([12,14,14], -120131207602560), ([12,14,15], -257842992254976), ([12,14,16], -291078749546496), ([12,14,17], -192730657211136), ([12,14,18], -60065603801280), ([12,14,19], -34538865669792), ([12,14,20], 60065603801280), ([12,14,21], 79127712091296), ([12,14,22], -241347707388000), ([12,14,23], -110344531931568), ([12,15,15], -87154171675776), ([12,15,16], -191627106331392), ([12,15,17], -169559752119552), ([12,15,18], -43577085837888), ([12,15,19], -15397879128192), ([12,15,20], 43577085837888), ([12,15,21], 54394935146208), ([12,15,22], -208424710733184), ([12,15,23], -68535134262000), ([12,16,16], -56998362254976), ([12,16,17], -134100812228352), ([12,16,18], -28499181127488), ([12,16,19], -15397879128192), ([12,16,20], 28499181127488), ([12,16,21], 31778078080608), ([12,16,22], -162045729177984), ([12,16,23], -102460419860400), ([12,17,17], -16909814376576), ([12,17,18], -8454907188288), ([12,17,19], -15397879128192), ([12,17,20], 8454907188288), ([12,17,21], 1711667171808), ([12,17,22], -202134277056384), ([12,17,23], -147560036223600), ([12,18,19], -7698939564096), ([12,18,21], -5485346805312), ([12,18,22], -109522045716480), ([12,18,23], -83291788698624), ([12,19,20], 7698939564096), ([12,19,21], 11548409346144), ([12,19,22], 15397879128192), ([12,19,23], 17322614019216), ([12,20,21], 5485346805312), ([12,20,22], 109522045716480), ([12,20,23], 83291788698624), ([12,21,21], 8228020207968), ([12,21,22], 175253762185344), ([12,21,23], 137279713359888), ([12,22,22], 217806203928960), ([12,22,23], 413008180259328), ([12,23,23], 187406524571904), ([13,13,14], -53640653552640), ([13,13,15], -110876770287360), ([13,13,16], -81385657516800), ([13,13,17], -31112444563200), ([13,13,19], -14419624665600), ([13,13,22], -187484399020800), ([13,13,23], -131757147244800), ([13,14,14], -53640653552640), ([13,14,15], -215075036816640), ([13,14,16], -248975490758400), ([13,14,17], -140442733347840), ([13,14,18], -26820326776320), ([13,14,19], -33560611207200), ([13,14,20], 26820326776320), ([13,14,21], 40230490164480), ([13,14,22], -276278569025760), ([13,14,23], -150319975085280), ([13,15,15], -110876770287360), ([13,15,16], -239737000204800), ([13,15,17], -207484980917760), ([13,15,18], -55438385143680), ([13,15,19], -14419624665600), ([13,15,20], 55438385143680), ([13,15,21], 83157577715520), ([13,15,22], -153142419709440), ([13,15,23], -7020780671520), ([13,16,16], -81385657516800), ([13,16,17], -172690737676800), ([13,16,18], -40692828758400), ([13,16,19], -14419624665600), ([13,16,20], 40692828758400), ([13,16,21], 61039243137600), ([13,16,22], -106098741504000), ([13,16,23], -40198282538400), ([13,17,17], -31112444563200), ([13,17,18], -15556222281600), ([13,17,19], -14419624665600), ([13,17,20], 15556222281600), ([13,17,21], 23334333422400), ([13,17,22], -156371954457600), ([13,17,23], -96755647111200), ([13,18,19], -7209812332800), ([13,18,22], -93742199510400), ([13,18,23], -65878573622400), ([13,19,20], 7209812332800), ([13,19,21], 10814718499200), ([13,19,22], 14419624665600), ([13,19,23], 16222077748800), ([13,20,22], 93742199510400), ([13,20,23], 65878573622400), ([13,21,22], 140613299265600), ([13,21,23], 98817860433600), ([13,22,22], 186246511516800), ([13,22,23], 342677096143200), ([13,23,23], 148226790650400), ([14,14,15], -50557612976640), ([14,14,16], -113949179688960), ([14,14,17], -55689635232000), ([14,14,19], -19140986541600), ([14,14,22], -142434823557600), ([14,14,23], -78908563087200), ([14,15,15], -50557612976640), ([14,15,16], -211981365066240), ([14,15,17], -171743014275840), ([14,15,18], -25278806488320), ([14,15,19], -19140986541600), ([14,15,20], 25278806488320), ([14,15,21], 37918209732480), ([14,15,22], -168412001556960), ([14,15,23], -22031248488480), ([14,16,16], -113949179688960), ([14,16,17], -229831450517760), ([14,16,18], -56974589844480), ([14,16,19], -19140986541600), ([14,16,20], 56974589844480), ([14,16,21], 85461884766720), ([14,16,22], -28485643868640), ([14,16,23], 49284264062880), ([14,17,17], -55689635232000), ([14,17,18], -27844817616000), ([14,17,19], -19140986541600), ([14,17,20], 27844817616000), ([14,17,21], 41767226424000), ([14,17,22], -86745188325600), ([14,17,23], -16257723451200), ([14,18,19], -9570493270800), ([14,18,22], -71217411778800), ([14,18,23], -39454281543600), ([14,19,20], 9570493270800), ([14,19,21], 14355739906200), ([14,19,22], 19140986541600), ([14,19,23], 21533609859300), ([14,20,22], 71217411778800), ([14,20,23], 39454281543600), ([14,21,22], 106826117668200), ([14,21,23], 59181422315400), ([14,22,22], 141196936053600), ([14,22,23], 239147739589500), ([14,23,23], 88772133473100), ([15,15,16], -47474572400640), ([15,15,17], -65495766067200), ([15,15,22], -76534790976000), ([15,16,16], -47474572400640), ([15,16,17], -173162974064640), ([15,16,18], -23737286200320), ([15,16,20], 23737286200320), ([15,16,21], 35605929300480), ([15,16,22], -29060218575360), ([15,16,23], 53408893950720), ([15,17,17], -65495766067200), ([15,17,18], -32747883033600), ([15,17,20], 32747883033600), ([15,17,21], 49121824550400), ([15,17,22], -11039024908800), ([15,17,23], 73682736825600), ([15,18,22], -38267395488000), ([15,20,22], 38267395488000), ([15,21,22], 57401093232000), ([15,22,22], 75296903472000), ([15,22,23], 86101639848000), ([16,16,17], -60192635596800), ([16,17,17], -60192635596800), ([16,17,18], -30096317798400), ([16,17,20], 30096317798400), ([16,17,21], 45144476697600), ([16,17,22], 60192635596800), ([16,17,23], 67716715046400), ([16,22,22], -1237887504000), ([17,22,22], -1237887504000), ([18,22,22], -618943752000), ([20,22,22], 618943752000), ([21,22,22], 928415628000), ([22,22,22], 1237887504000), ([22,22,23], 1392623442000)]
theorem block004_data : block004 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4302807205842 : Int) atom0129) (SparsePolynomial.scale (3324175386642 : Int) atom0130)) (SparsePolynomial.merge (SparsePolynomial.scale (1511071623666 : Int) atom0131) (SparsePolynomial.merge (SparsePolynomial.scale (7003753939314 : Int) atom0132) (SparsePolynomial.scale (3693823851762 : Int) atom0133)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11221399009458 : Int) atom0134) (SparsePolynomial.scale (5188983412800 : Int) atom0135)) (SparsePolynomial.merge (SparsePolynomial.scale (9065709577728 : Int) atom0136) (SparsePolynomial.merge (SparsePolynomial.scale (3352540847040 : Int) atom0137) (SparsePolynomial.scale (7846321654710 : Int) atom0138))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7558104430602 : Int) atom0139) (SparsePolynomial.scale (6940369358802 : Int) atom0140)) (SparsePolynomial.merge (SparsePolynomial.scale (5398446374802 : Int) atom0141) (SparsePolynomial.merge (SparsePolynomial.scale (4595430281202 : Int) atom0142) (SparsePolynomial.scale (3171618034002 : Int) atom0143)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (834131593746 : Int) atom0144) (SparsePolynomial.scale (5723228982834 : Int) atom0145)) (SparsePolynomial.merge (SparsePolynomial.scale (1809713968722 : Int) atom0146) (SparsePolynomial.merge (SparsePolynomial.scale (8575299701298 : Int) atom0147) (SparsePolynomial.scale (10861157920800 : Int) atom0148)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14235738281568 : Int) atom0149) (SparsePolynomial.scale (3352540847040 : Int) atom0150)) (SparsePolynomial.merge (SparsePolynomial.scale (7219663757460 : Int) atom0151) (SparsePolynomial.merge (SparsePolynomial.scale (7576464321756 : Int) atom0152) (SparsePolynomial.scale (5332883827356 : Int) atom0153)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4020900259356 : Int) atom0154) (SparsePolynomial.scale (2088120537756 : Int) atom0155)) (SparsePolynomial.merge (SparsePolynomial.scale (3716406396252 : Int) atom0156) (SparsePolynomial.merge (SparsePolynomial.scale (5739761882844 : Int) atom0157) (SparsePolynomial.scale (16558454906400 : Int) atom0158))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14660222436288 : Int) atom0159) (SparsePolynomial.scale (3352540847040 : Int) atom0160)) (SparsePolynomial.merge (SparsePolynomial.scale (7508200475160 : Int) atom0161) (SparsePolynomial.merge (SparsePolynomial.scale (5447135729736 : Int) atom0162) (SparsePolynomial.scale (3562397640936 : Int) atom0163)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1056863398536 : Int) atom0164) (SparsePolynomial.scale (962367445512 : Int) atom0165)) (SparsePolynomial.merge (SparsePolynomial.scale (685668350664 : Int) atom0166) (SparsePolynomial.merge (SparsePolynomial.scale (13690255714560 : Int) atom0167) (SparsePolynomial.scale (10411473587328 : Int) atom0168))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3352540847040 : Int) atom0169) (SparsePolynomial.scale (6929798142960 : Int) atom0170)) (SparsePolynomial.merge (SparsePolynomial.scale (5086603594800 : Int) atom0171) (SparsePolynomial.merge (SparsePolynomial.scale (1944527785200 : Int) atom0172) (SparsePolynomial.scale (901226541600 : Int) atom0173)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11717774938800 : Int) atom0174) (SparsePolynomial.scale (8234821702800 : Int) atom0175)) (SparsePolynomial.merge (SparsePolynomial.scale (3159850811040 : Int) atom0176) (SparsePolynomial.merge (SparsePolynomial.scale (7121823730560 : Int) atom0177) (SparsePolynomial.scale (3480602202000 : Int) atom0178))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1196311658850 : Int) atom0179) (SparsePolynomial.scale (8902176472350 : Int) atom0180)) (SparsePolynomial.merge (SparsePolynomial.scale (4931785192950 : Int) atom0181) (SparsePolynomial.merge (SparsePolynomial.scale (2967160775040 : Int) atom0182) (SparsePolynomial.scale (4093485379200 : Int) atom0183)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4783424436000 : Int) atom0184) (SparsePolynomial.scale (3762039724800 : Int) atom0185)) (SparsePolynomial.merge (SparsePolynomial.scale (77367969000 : Int) atom0186) (SparsePolynomial.merge (SparsePolynomial.scale (813284841600 : Int) atom0187) (SparsePolynomial.scale (1198664913600 : Int) atom0188)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1584044985600 : Int) atom0189) (SparsePolynomial.scale (1969425057600 : Int) atom0190)) (SparsePolynomial.merge (SparsePolynomial.scale (1494443412000 : Int) atom0191) (SparsePolynomial.merge (SparsePolynomial.scale (2740185201600 : Int) atom0192) (SparsePolynomial.scale (3125565273600 : Int) atom0193)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3510945345600 : Int) atom0194) (SparsePolynomial.scale (3144852786834 : Int) atom0195)) (SparsePolynomial.merge (SparsePolynomial.scale (1324795729554 : Int) atom0196) (SparsePolynomial.merge (SparsePolynomial.scale (78928416000 : Int) atom0197) (SparsePolynomial.scale (1635670612800 : Int) atom0198))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1950820502400 : Int) atom0199) (SparsePolynomial.scale (1084379788800 : Int) atom0200)) (SparsePolynomial.merge (SparsePolynomial.scale (1242961473600 : Int) atom0201) (SparsePolynomial.merge (SparsePolynomial.scale (1511620110000 : Int) atom0202) (SparsePolynomial.scale (3724897730400 : Int) atom0203)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (284787224832 : Int) atom0204) (SparsePolynomial.scale (4217032512000 : Int) atom0205)) (SparsePolynomial.merge (SparsePolynomial.scale (598889491200 : Int) atom0206) (SparsePolynomial.merge (SparsePolynomial.scale (2732171321088 : Int) atom0207) (SparsePolynomial.scale (3522438404496 : Int) atom0208)))))))) := by decide +kernel
theorem block004_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block004 := by
  rw [block004_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0129_nonneg g hg hA hB) (atom0130_nonneg g hg hA hB)) (add_nonneg (atom0131_nonneg g hg hA hB) (add_nonneg (atom0132_nonneg g hg hA hB) (atom0133_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0134_nonneg g hg hA hB) (atom0135_nonneg g hg hA hB)) (add_nonneg (atom0136_nonneg g hg hA hB) (add_nonneg (atom0137_nonneg g hg hA hB) (atom0138_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0139_nonneg g hg hA hB) (atom0140_nonneg g hg hA hB)) (add_nonneg (atom0141_nonneg g hg hA hB) (add_nonneg (atom0142_nonneg g hg hA hB) (atom0143_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0144_nonneg g hg hA hB) (atom0145_nonneg g hg hA hB)) (add_nonneg (atom0146_nonneg g hg hA hB) (add_nonneg (atom0147_nonneg g hg hA hB) (atom0148_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0149_nonneg g hg hA hB) (atom0150_nonneg g hg hA hB)) (add_nonneg (atom0151_nonneg g hg hA hB) (add_nonneg (atom0152_nonneg g hg hA hB) (atom0153_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0154_nonneg g hg hA hB) (atom0155_nonneg g hg hA hB)) (add_nonneg (atom0156_nonneg g hg hA hB) (add_nonneg (atom0157_nonneg g hg hA hB) (atom0158_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0159_nonneg g hg hA hB) (atom0160_nonneg g hg hA hB)) (add_nonneg (atom0161_nonneg g hg hA hB) (add_nonneg (atom0162_nonneg g hg hA hB) (atom0163_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0164_nonneg g hg hA hB) (atom0165_nonneg g hg hA hB)) (add_nonneg (atom0166_nonneg g hg hA hB) (add_nonneg (atom0167_nonneg g hg hA hB) (atom0168_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0169_nonneg g hg hA hB) (atom0170_nonneg g hg hA hB)) (add_nonneg (atom0171_nonneg g hg hA hB) (add_nonneg (atom0172_nonneg g hg hA hB) (atom0173_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0174_nonneg g hg hA hB) (atom0175_nonneg g hg hA hB)) (add_nonneg (atom0176_nonneg g hg hA hB) (add_nonneg (atom0177_nonneg g hg hA hB) (atom0178_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0179_nonneg g hg hA hB) (atom0180_nonneg g hg hA hB)) (add_nonneg (atom0181_nonneg g hg hA hB) (add_nonneg (atom0182_nonneg g hg hA hB) (atom0183_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0184_nonneg g hg hA hB) (atom0185_nonneg g hg hA hB)) (add_nonneg (atom0186_nonneg g hg hA hB) (add_nonneg (atom0187_nonneg g hg hA hB) (atom0188_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0189_nonneg g hg hA hB) (atom0190_nonneg g hg hA hB)) (add_nonneg (atom0191_nonneg g hg hA hB) (add_nonneg (atom0192_nonneg g hg hA hB) (atom0193_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0194_nonneg g hg hA hB) (atom0195_nonneg g hg hA hB)) (add_nonneg (atom0196_nonneg g hg hA hB) (add_nonneg (atom0197_nonneg g hg hA hB) (atom0198_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0199_nonneg g hg hA hB) (atom0200_nonneg g hg hA hB)) (add_nonneg (atom0201_nonneg g hg hA hB) (add_nonneg (atom0202_nonneg g hg hA hB) (atom0203_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0204_nonneg g hg hA hB) (atom0205_nonneg g hg hA hB)) (add_nonneg (atom0206_nonneg g hg hA hB) (add_nonneg (atom0207_nonneg g hg hA hB) (atom0208_nonneg g hg hA hB))))))))

end APPT.Finite24
