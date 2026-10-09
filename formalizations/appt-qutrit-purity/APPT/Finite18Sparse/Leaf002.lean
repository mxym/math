import APPT.Finite18Sparse.Base08
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0095 : SparsePolynomial.Poly := [([0,2,17], -8), ([1,2,17], -12), ([2,2,17], -16), ([2,3,17], -16), ([2,4,17], -16), ([2,5,17], -16), ([2,6,17], -16), ([2,7,17], -16), ([2,8,17], -16), ([2,9,17], -16), ([2,10,17], -16), ([2,11,17], -16), ([2,12,17], -14), ([2,13,17], -10), ([2,14,17], -2), ([2,15,17], 2), ([2,16,17], 10), ([2,17,17], 18)]
theorem atom0095_data : atom0095 = SparsePolynomial.monoTimes [2,17] 1 base08 := by decide +kernel
theorem eval_atom0095 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0095 = (quadB (outer g) ![2,2,1] * g 2 * g 17) := by
  rw [atom0095_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0095_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38808000 : Int) atom0095) := by
  rw [SparsePolynomial.eval_scale, eval_atom0095]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 2 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -16), ([4,4,4], -16), ([4,4,5], -16), ([4,4,6], -16), ([4,4,7], -16), ([4,4,8], -16), ([4,4,9], -16), ([4,4,10], -16), ([4,4,11], -16), ([4,4,12], -14), ([4,4,13], -10), ([4,4,14], -2), ([4,4,15], 2), ([4,4,16], 10), ([4,4,17], 18)]
theorem atom0096_data : atom0096 = SparsePolynomial.monoTimes [4,4] 1 base08 := by decide +kernel
theorem eval_atom0096 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0096 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0096_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0096_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (77518560 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097 : SparsePolynomial.Poly := [([0,4,5], -8), ([1,4,5], -12), ([2,4,5], -16), ([3,4,5], -16), ([4,4,5], -16), ([4,5,5], -16), ([4,5,6], -16), ([4,5,7], -16), ([4,5,8], -16), ([4,5,9], -16), ([4,5,10], -16), ([4,5,11], -16), ([4,5,12], -14), ([4,5,13], -10), ([4,5,14], -2), ([4,5,15], 2), ([4,5,16], 10), ([4,5,17], 18)]
theorem atom0097_data : atom0097 = SparsePolynomial.monoTimes [4,5] 1 base08 := by decide +kernel
theorem eval_atom0097 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0097 = (quadB (outer g) ![2,2,1] * g 4 * g 5) := by
  rw [atom0097_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0097_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8654952 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098 : SparsePolynomial.Poly := [([0,5,5], -8), ([1,5,5], -12), ([2,5,5], -16), ([3,5,5], -16), ([4,5,5], -16), ([5,5,5], -16), ([5,5,6], -16), ([5,5,7], -16), ([5,5,8], -16), ([5,5,9], -16), ([5,5,10], -16), ([5,5,11], -16), ([5,5,12], -14), ([5,5,13], -10), ([5,5,14], -2), ([5,5,15], 2), ([5,5,16], 10), ([5,5,17], 18)]
theorem atom0098_data : atom0098 = SparsePolynomial.monoTimes [5,5] 1 base08 := by decide +kernel
theorem eval_atom0098 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0098 = (quadB (outer g) ![2,2,1] * g 5 * g 5) := by
  rw [atom0098_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0098_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (74370240 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099 : SparsePolynomial.Poly := [([0,5,6], -8), ([1,5,6], -12), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -16), ([5,6,10], -16), ([5,6,11], -16), ([5,6,12], -14), ([5,6,13], -10), ([5,6,14], -2), ([5,6,15], 2), ([5,6,16], 10), ([5,6,17], 18)]
theorem atom0099_data : atom0099 = SparsePolynomial.monoTimes [5,6] 1 base08 := by decide +kernel
theorem eval_atom0099 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0099 = (quadB (outer g) ![2,2,1] * g 5 * g 6) := by
  rw [atom0099_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0099_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47881872 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100 : SparsePolynomial.Poly := [([0,6,7], -8), ([1,6,7], -12), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -16), ([6,7,10], -16), ([6,7,11], -16), ([6,7,12], -14), ([6,7,13], -10), ([6,7,14], -2), ([6,7,15], 2), ([6,7,16], 10), ([6,7,17], 18)]
theorem atom0100_data : atom0100 = SparsePolynomial.monoTimes [6,7] 1 base08 := by decide +kernel
theorem eval_atom0100 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0100 = (quadB (outer g) ![2,2,1] * g 6 * g 7) := by
  rw [atom0100_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0100_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91894392 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101 : SparsePolynomial.Poly := [([0,7,7], -8), ([1,7,7], -12), ([2,7,7], -16), ([3,7,7], -16), ([4,7,7], -16), ([5,7,7], -16), ([6,7,7], -16), ([7,7,7], -16), ([7,7,8], -16), ([7,7,9], -16), ([7,7,10], -16), ([7,7,11], -16), ([7,7,12], -14), ([7,7,13], -10), ([7,7,14], -2), ([7,7,15], 2), ([7,7,16], 10), ([7,7,17], 18)]
theorem atom0101_data : atom0101 = SparsePolynomial.monoTimes [7,7] 1 base08 := by decide +kernel
theorem eval_atom0101 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0101 = (quadB (outer g) ![2,2,1] * g 7 * g 7) := by
  rw [atom0101_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0101_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8139420 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102 : SparsePolynomial.Poly := [([0,7,8], -8), ([1,7,8], -12), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -14), ([7,8,13], -10), ([7,8,14], -2), ([7,8,15], 2), ([7,8,16], 10), ([7,8,17], 18)]
theorem atom0102_data : atom0102 = SparsePolynomial.monoTimes [7,8] 1 base08 := by decide +kernel
theorem eval_atom0102 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0102 = (quadB (outer g) ![2,2,1] * g 7 * g 8) := by
  rw [atom0102_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0102_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (108513552 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103 : SparsePolynomial.Poly := [([0,8,8], -8), ([1,8,8], -12), ([2,8,8], -16), ([3,8,8], -16), ([4,8,8], -16), ([5,8,8], -16), ([6,8,8], -16), ([7,8,8], -16), ([8,8,8], -16), ([8,8,9], -16), ([8,8,10], -16), ([8,8,11], -16), ([8,8,12], -14), ([8,8,13], -10), ([8,8,14], -2), ([8,8,15], 2), ([8,8,16], 10), ([8,8,17], 18)]
theorem atom0103_data : atom0103 = SparsePolynomial.monoTimes [8,8] 1 base08 := by decide +kernel
theorem eval_atom0103 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0103 = (quadB (outer g) ![2,2,1] * g 8 * g 8) := by
  rw [atom0103_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0103_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83536500 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104 : SparsePolynomial.Poly := [([0,8,9], -8), ([1,8,9], -12), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -14), ([8,9,13], -10), ([8,9,14], -2), ([8,9,15], 2), ([8,9,16], 10), ([8,9,17], 18)]
theorem atom0104_data : atom0104 = SparsePolynomial.monoTimes [8,9] 1 base08 := by decide +kernel
theorem eval_atom0104 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0104 = (quadB (outer g) ![2,2,1] * g 8 * g 9) := by
  rw [atom0104_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0104_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (188493600 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105 : SparsePolynomial.Poly := [([0,8,10], -8), ([1,8,10], -12), ([2,8,10], -16), ([3,8,10], -16), ([4,8,10], -16), ([5,8,10], -16), ([6,8,10], -16), ([7,8,10], -16), ([8,8,10], -16), ([8,9,10], -16), ([8,10,10], -16), ([8,10,11], -16), ([8,10,12], -14), ([8,10,13], -10), ([8,10,14], -2), ([8,10,15], 2), ([8,10,16], 10), ([8,10,17], 18)]
theorem atom0105_data : atom0105 = SparsePolynomial.monoTimes [8,10] 1 base08 := by decide +kernel
theorem eval_atom0105 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0105 = (quadB (outer g) ![2,2,1] * g 8 * g 10) := by
  rw [atom0105_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0105_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10726368 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106 : SparsePolynomial.Poly := [([0,9,9], -8), ([1,9,9], -12), ([2,9,9], -16), ([3,9,9], -16), ([4,9,9], -16), ([5,9,9], -16), ([6,9,9], -16), ([7,9,9], -16), ([8,9,9], -16), ([9,9,9], -16), ([9,9,10], -16), ([9,9,11], -16), ([9,9,12], -14), ([9,9,13], -10), ([9,9,14], -2), ([9,9,15], 2), ([9,9,16], 10), ([9,9,17], 18)]
theorem atom0106_data : atom0106 = SparsePolynomial.monoTimes [9,9] 1 base08 := by decide +kernel
theorem eval_atom0106 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0106 = (quadB (outer g) ![2,2,1] * g 9 * g 9) := by
  rw [atom0106_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0106_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (175867680 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107 : SparsePolynomial.Poly := [([0,9,10], -8), ([1,9,10], -12), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -14), ([9,10,13], -10), ([9,10,14], -2), ([9,10,15], 2), ([9,10,16], 10), ([9,10,17], 18)]
theorem atom0107_data : atom0107 = SparsePolynomial.monoTimes [9,10] 1 base08 := by decide +kernel
theorem eval_atom0107 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0107 = (quadB (outer g) ![2,2,1] * g 9 * g 10) := by
  rw [atom0107_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0107_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (203546880 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108 : SparsePolynomial.Poly := [([0,9,11], -8), ([1,9,11], -12), ([2,9,11], -16), ([3,9,11], -16), ([4,9,11], -16), ([5,9,11], -16), ([6,9,11], -16), ([7,9,11], -16), ([8,9,11], -16), ([9,9,11], -16), ([9,10,11], -16), ([9,11,11], -16), ([9,11,12], -14), ([9,11,13], -10), ([9,11,14], -2), ([9,11,15], 2), ([9,11,16], 10), ([9,11,17], 18)]
theorem atom0108_data : atom0108 = SparsePolynomial.monoTimes [9,11] 1 base08 := by decide +kernel
theorem eval_atom0108 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0108 = (quadB (outer g) ![2,2,1] * g 9 * g 11) := by
  rw [atom0108_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0108_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46651680 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109 : SparsePolynomial.Poly := [([0,10,10], -8), ([1,10,10], -12), ([2,10,10], -16), ([3,10,10], -16), ([4,10,10], -16), ([5,10,10], -16), ([6,10,10], -16), ([7,10,10], -16), ([8,10,10], -16), ([9,10,10], -16), ([10,10,10], -16), ([10,10,11], -16), ([10,10,12], -14), ([10,10,13], -10), ([10,10,14], -2), ([10,10,15], 2), ([10,10,16], 10), ([10,10,17], 18)]
theorem atom0109_data : atom0109 = SparsePolynomial.monoTimes [10,10] 1 base08 := by decide +kernel
theorem eval_atom0109 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0109 = (quadB (outer g) ![2,2,1] * g 10 * g 10) := by
  rw [atom0109_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0109_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (170358240 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110 : SparsePolynomial.Poly := [([0,10,11], -8), ([1,10,11], -12), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -14), ([10,11,13], -10), ([10,11,14], -2), ([10,11,15], 2), ([10,11,16], 10), ([10,11,17], 18)]
theorem atom0110_data : atom0110 = SparsePolynomial.monoTimes [10,11] 1 base08 := by decide +kernel
theorem eval_atom0110 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0110 = (quadB (outer g) ![2,2,1] * g 10 * g 11) := by
  rw [atom0110_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0110_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (221921760 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111 : SparsePolynomial.Poly := [([0,11,11], -8), ([1,11,11], -12), ([2,11,11], -16), ([3,11,11], -16), ([4,11,11], -16), ([5,11,11], -16), ([6,11,11], -16), ([7,11,11], -16), ([8,11,11], -16), ([9,11,11], -16), ([10,11,11], -16), ([11,11,11], -16), ([11,11,12], -14), ([11,11,13], -10), ([11,11,14], -2), ([11,11,15], 2), ([11,11,16], 10), ([11,11,17], 18)]
theorem atom0111_data : atom0111 = SparsePolynomial.monoTimes [11,11] 1 base08 := by decide +kernel
theorem eval_atom0111 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0111 = (quadB (outer g) ![2,2,1] * g 11 * g 11) := by
  rw [atom0111_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0111_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (166440960 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112 : SparsePolynomial.Poly := [([0,11,12], -8), ([1,11,12], -12), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -14), ([11,12,13], -10), ([11,12,14], -2), ([11,12,15], 2), ([11,12,16], 10), ([11,12,17], 18)]
theorem atom0112_data : atom0112 = SparsePolynomial.monoTimes [11,12] 1 base08 := by decide +kernel
theorem eval_atom0112 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0112 = (quadB (outer g) ![2,2,1] * g 11 * g 12) := by
  rw [atom0112_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0112_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16773120 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113 : SparsePolynomial.Poly := [([0,13,13], -8), ([1,13,13], -12), ([2,13,13], -16), ([3,13,13], -16), ([4,13,13], -16), ([5,13,13], -16), ([6,13,13], -16), ([7,13,13], -16), ([8,13,13], -16), ([9,13,13], -16), ([10,13,13], -16), ([11,13,13], -16), ([12,13,13], -14), ([13,13,13], -10), ([13,13,14], -2), ([13,13,15], 2), ([13,13,16], 10), ([13,13,17], 18)]
theorem atom0113_data : atom0113 = SparsePolynomial.monoTimes [13,13] 1 base08 := by decide +kernel
theorem eval_atom0113 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0113 = (quadB (outer g) ![2,2,1] * g 13 * g 13) := by
  rw [atom0113_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0113_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49932288 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114 : SparsePolynomial.Poly := [([0,0,12], 1)]
theorem eval_atom0114 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0114 = ((g 0) * (g 0) * (g 12)) := by
  norm_num [atom0114, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0114_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (409651200 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 0) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115 : SparsePolynomial.Poly := [([0,0,13], 1)]
theorem eval_atom0115 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0115 = ((g 0) * (g 0) * (g 13)) := by
  norm_num [atom0115, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0115_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (305786880 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 0) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116 : SparsePolynomial.Poly := [([0,0,14], 1)]
theorem eval_atom0116 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0116 = ((g 0) * (g 0) * (g 14)) := by
  norm_num [atom0116, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0116_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (201922560 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 0) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117 : SparsePolynomial.Poly := [([0,0,15], 1)]
theorem eval_atom0117 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0117 = ((g 0) * (g 0) * (g 15)) := by
  norm_num [atom0117, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0117_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (98058240 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 0) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118 : SparsePolynomial.Poly := [([0,1,1], 1)]
theorem eval_atom0118 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0118 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0118, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0118_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (248236800 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119 : SparsePolynomial.Poly := [([0,1,2], 1)]
theorem eval_atom0119 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0119 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0119, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0119_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1455068160 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120 : SparsePolynomial.Poly := [([0,1,3], 1)]
theorem eval_atom0120 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0120 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0120, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0120_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1453455360 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121 : SparsePolynomial.Poly := [([0,1,4], 1)]
theorem eval_atom0121 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0121 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0121, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0121_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1451842560 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122 : SparsePolynomial.Poly := [([0,1,5], 1)]
theorem eval_atom0122 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0122 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0122, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0122_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1450229760 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123 : SparsePolynomial.Poly := [([0,1,6], 1)]
theorem eval_atom0123 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0123 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0123, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0123_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1448616960 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124 : SparsePolynomial.Poly := [([0,1,7], 1)]
theorem eval_atom0124 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0124 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0124, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0124_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1447004160 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125 : SparsePolynomial.Poly := [([0,1,8], 1)]
theorem eval_atom0125 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0125 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0125, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0125_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1471008000 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126 : SparsePolynomial.Poly := [([0,1,9], 1)]
theorem eval_atom0126 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0126 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0126, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0126_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1464879360 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127 : SparsePolynomial.Poly := [([0,1,10], 1)]
theorem eval_atom0127 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0127 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0127, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0127_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1471330560 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128 : SparsePolynomial.Poly := [([0,1,11], 1)]
theorem eval_atom0128 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0128 = ((g 0) * (g 1) * (g 11)) := by
  norm_num [atom0128, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0128_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1512465920 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129 : SparsePolynomial.Poly := [([0,1,12], 1)]
theorem eval_atom0129 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0129 = ((g 0) * (g 1) * (g 12)) := by
  norm_num [atom0129, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0129_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2885621760 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130 : SparsePolynomial.Poly := [([0,1,13], 1)]
theorem eval_atom0130 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0130 = ((g 0) * (g 1) * (g 13)) := by
  norm_num [atom0130, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0130_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1132241600 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131 : SparsePolynomial.Poly := [([0,1,14], 1)]
theorem eval_atom0131 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0131 = ((g 0) * (g 1) * (g 14)) := by
  norm_num [atom0131, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0131_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (457390080 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132 : SparsePolynomial.Poly := [([0,1,15], 1)]
theorem eval_atom0132 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0132 = ((g 0) * (g 1) * (g 15)) := by
  norm_num [atom0132, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0132_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (225565760 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133 : SparsePolynomial.Poly := [([0,1,16], 1)]
theorem eval_atom0133 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0133 = ((g 0) * (g 1) * (g 16)) := by
  norm_num [atom0133, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0133_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (180255040 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134 : SparsePolynomial.Poly := [([0,2,2], 1)]
theorem eval_atom0134 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0134 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0134, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0134_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1619251200 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135 : SparsePolynomial.Poly := [([0,2,3], 1)]
theorem eval_atom0135 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0135 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0135, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0135_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3339141120 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136 : SparsePolynomial.Poly := [([0,2,4], 1)]
theorem eval_atom0136 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0136 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0136, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0136_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3439779840 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137 : SparsePolynomial.Poly := [([0,2,5], 1)]
theorem eval_atom0137 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0137 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0137, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0137_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3540418560 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138 : SparsePolynomial.Poly := [([0,2,6], 1)]
theorem eval_atom0138 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0138 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0138, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0138_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3641057280 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139 : SparsePolynomial.Poly := [([0,2,7], 1)]
theorem eval_atom0139 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0139 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0139, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0139_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3741696000 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140 : SparsePolynomial.Poly := [([0,2,8], 1)]
theorem eval_atom0140 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0140 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0140, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0140_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3842334720 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141 : SparsePolynomial.Poly := [([0,2,9], 1)]
theorem eval_atom0141 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0141 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0141, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0141_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3942973440 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142 : SparsePolynomial.Poly := [([0,2,10], 1)]
theorem eval_atom0142 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0142 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0142, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0142_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4043612160 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143 : SparsePolynomial.Poly := [([0,2,11], 1)]
theorem eval_atom0143 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0143 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0143, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0143_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4144250880 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144 : SparsePolynomial.Poly := [([0,2,12], 1)]
theorem eval_atom0144 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0144 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0144, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0144_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4982100480 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145 : SparsePolynomial.Poly := [([0,2,13], 1)]
theorem eval_atom0145 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0145 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0145, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0145_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2934167040 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146 : SparsePolynomial.Poly := [([0,2,14], 1)]
theorem eval_atom0146 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0146 = ((g 0) * (g 2) * (g 14)) := by
  norm_num [atom0146, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0146_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2444907240 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147 : SparsePolynomial.Poly := [([0,2,15], 1)]
theorem eval_atom0147 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0147 = ((g 0) * (g 2) * (g 15)) := by
  norm_num [atom0147, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0147_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (450777600 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148 : SparsePolynomial.Poly := [([0,2,16], 1)]
theorem eval_atom0148 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0148 = ((g 0) * (g 2) * (g 16)) := by
  norm_num [atom0148, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0148_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (643184640 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149 : SparsePolynomial.Poly := [([0,3,3], 1)]
theorem eval_atom0149 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0149 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0149, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0149_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1616025600 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150 : SparsePolynomial.Poly := [([0,3,4], 1)]
theorem eval_atom0150 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0150 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0150, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0150_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3383009280 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151 : SparsePolynomial.Poly := [([0,3,5], 1)]
theorem eval_atom0151 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0151 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0151, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0151_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3533967360 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152 : SparsePolynomial.Poly := [([0,3,6], 1)]
theorem eval_atom0152 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0152 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0152, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0152_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3684925440 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153 : SparsePolynomial.Poly := [([0,3,7], 1)]
theorem eval_atom0153 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0153 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0153, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0153_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3835883520 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154 : SparsePolynomial.Poly := [([0,3,8], 1)]
theorem eval_atom0154 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0154 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0154, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0154_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3986841600 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155 : SparsePolynomial.Poly := [([0,3,9], 1)]
theorem eval_atom0155 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0155 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0155, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0155_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4137799680 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156 : SparsePolynomial.Poly := [([0,3,10], 1)]
theorem eval_atom0156 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0156 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0156, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0156_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4288757760 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157 : SparsePolynomial.Poly := [([0,3,11], 1)]
theorem eval_atom0157 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0157 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0157, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0157_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4480035840 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158 : SparsePolynomial.Poly := [([0,3,12], 1)]
theorem eval_atom0158 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0158 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0158, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0158_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5301918720 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159 : SparsePolynomial.Poly := [([0,3,13], 1)]
theorem eval_atom0159 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0159 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0159, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0159_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3349463040 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160 : SparsePolynomial.Poly := [([0,3,14], 1)]
theorem eval_atom0160 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0160 = ((g 0) * (g 3) * (g 14)) := by
  norm_num [atom0160, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0160_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2709567720 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161 : SparsePolynomial.Poly := [([0,3,15], 1)]
theorem eval_atom0161 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0161 = ((g 0) * (g 3) * (g 15)) := by
  norm_num [atom0161, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0161_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (867686400 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162 : SparsePolynomial.Poly := [([0,3,16], 1)]
theorem eval_atom0162 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0162 = ((g 0) * (g 3) * (g 16)) := by
  norm_num [atom0162, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0162_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1104122880 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163 : SparsePolynomial.Poly := [([0,3,17], 1)]
theorem eval_atom0163 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0163 = ((g 0) * (g 3) * (g 17)) := by
  norm_num [atom0163, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0163_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56125440 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164 : SparsePolynomial.Poly := [([0,4,4], 1)]
theorem eval_atom0164 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0164 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0164, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0164_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2283267840 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165 : SparsePolynomial.Poly := [([0,4,5], 1)]
theorem eval_atom0165 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0165 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0165, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0165_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3957442368 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0166 : SparsePolynomial.Poly := [([0,4,6], 1)]
theorem eval_atom0166 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0166 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0166, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0166_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3881051040 : Int) atom0166) := by
  rw [SparsePolynomial.eval_scale, eval_atom0166]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0167 : SparsePolynomial.Poly := [([0,4,7], 1)]
theorem eval_atom0167 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0167 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0167, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0167_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3958523520 : Int) atom0167) := by
  rw [SparsePolynomial.eval_scale, eval_atom0167]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0168 : SparsePolynomial.Poly := [([0,4,8], 1)]
theorem eval_atom0168 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0168 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0168, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0168_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4131348480 : Int) atom0168) := by
  rw [SparsePolynomial.eval_scale, eval_atom0168]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0169 : SparsePolynomial.Poly := [([0,4,9], 1)]
theorem eval_atom0169 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0169 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0169, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0169_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4332625920 : Int) atom0169) := by
  rw [SparsePolynomial.eval_scale, eval_atom0169]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0170 : SparsePolynomial.Poly := [([0,4,10], 1)]
theorem eval_atom0170 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0170 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0170, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0170_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4533903360 : Int) atom0170) := by
  rw [SparsePolynomial.eval_scale, eval_atom0170]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0171 : SparsePolynomial.Poly := [([0,4,11], 1)]
theorem eval_atom0171 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0171 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0171, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0171_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4753795200 : Int) atom0171) := by
  rw [SparsePolynomial.eval_scale, eval_atom0171]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0172 : SparsePolynomial.Poly := [([0,4,12], 1)]
theorem eval_atom0172 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0172 = ((g 0) * (g 4) * (g 12)) := by
  norm_num [atom0172, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0172_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5621736960 : Int) atom0172) := by
  rw [SparsePolynomial.eval_scale, eval_atom0172]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0173 : SparsePolynomial.Poly := [([0,4,13], 1)]
theorem eval_atom0173 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0173 = ((g 0) * (g 4) * (g 13)) := by
  norm_num [atom0173, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0173_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3713534160 : Int) atom0173) := by
  rw [SparsePolynomial.eval_scale, eval_atom0173]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0174 : SparsePolynomial.Poly := [([0,4,14], 1)]
theorem eval_atom0174 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0174 = ((g 0) * (g 4) * (g 14)) := by
  norm_num [atom0174, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0174_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2974228200 : Int) atom0174) := by
  rw [SparsePolynomial.eval_scale, eval_atom0174]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block002 : SparsePolynomial.Poly := [([0,0,12], 409651200), ([0,0,13], 305786880), ([0,0,14], 201922560), ([0,0,15], 98058240), ([0,1,1], 248236800), ([0,1,2], 1455068160), ([0,1,3], 1453455360), ([0,1,4], 1451842560), ([0,1,5], 1450229760), ([0,1,6], 1448616960), ([0,1,7], 1447004160), ([0,1,8], 1471008000), ([0,1,9], 1464879360), ([0,1,10], 1471330560), ([0,1,11], 1512465920), ([0,1,12], 2885621760), ([0,1,13], 1132241600), ([0,1,14], 457390080), ([0,1,15], 225565760), ([0,1,16], 180255040), ([0,2,2], 1619251200), ([0,2,3], 3339141120), ([0,2,4], 3439779840), ([0,2,5], 3540418560), ([0,2,6], 3641057280), ([0,2,7], 3741696000), ([0,2,8], 3842334720), ([0,2,9], 3942973440), ([0,2,10], 4043612160), ([0,2,11], 4144250880), ([0,2,12], 4982100480), ([0,2,13], 2934167040), ([0,2,14], 2444907240), ([0,2,15], 450777600), ([0,2,16], 643184640), ([0,2,17], -310464000), ([0,3,3], 1616025600), ([0,3,4], 3383009280), ([0,3,5], 3533967360), ([0,3,6], 3684925440), ([0,3,7], 3835883520), ([0,3,8], 3986841600), ([0,3,9], 4137799680), ([0,3,10], 4288757760), ([0,3,11], 4480035840), ([0,3,12], 5301918720), ([0,3,13], 3349463040), ([0,3,14], 2709567720), ([0,3,15], 867686400), ([0,3,16], 1104122880), ([0,3,17], 56125440), ([0,4,4], 1663119360), ([0,4,5], 3888202752), ([0,4,6], 3881051040), ([0,4,7], 3958523520), ([0,4,8], 4131348480), ([0,4,9], 4332625920), ([0,4,10], 4533903360), ([0,4,11], 4753795200), ([0,4,12], 5621736960), ([0,4,13], 3713534160), ([0,4,14], 2974228200), ([0,5,5], -594961920), ([0,5,6], -383054976), ([0,6,7], -735155136), ([0,7,7], -65115360), ([0,7,8], -868108416), ([0,8,8], -668292000), ([0,8,9], -1507948800), ([0,8,10], -85810944), ([0,9,9], -1406941440), ([0,9,10], -1628375040), ([0,9,11], -373213440), ([0,10,10], -1362865920), ([0,10,11], -1775374080), ([0,11,11], -1331527680), ([0,11,12], -134184960), ([0,13,13], -399458304), ([1,2,17], -465696000), ([1,4,4], -930222720), ([1,4,5], -103859424), ([1,5,5], -892442880), ([1,5,6], -574582464), ([1,6,7], -1102732704), ([1,7,7], -97673040), ([1,7,8], -1302162624), ([1,8,8], -1002438000), ([1,8,9], -2261923200), ([1,8,10], -128716416), ([1,9,9], -2110412160), ([1,9,10], -2442562560), ([1,9,11], -559820160), ([1,10,10], -2044298880), ([1,10,11], -2663061120), ([1,11,11], -1997291520), ([1,11,12], -201277440), ([1,13,13], -599187456), ([2,2,17], -620928000), ([2,3,17], -620928000), ([2,4,4], -1240296960), ([2,4,5], -138479232), ([2,4,17], -620928000), ([2,5,5], -1189923840), ([2,5,6], -766109952), ([2,5,17], -620928000), ([2,6,7], -1470310272), ([2,6,17], -620928000), ([2,7,7], -130230720), ([2,7,8], -1736216832), ([2,7,17], -620928000), ([2,8,8], -1336584000), ([2,8,9], -3015897600), ([2,8,10], -171621888), ([2,8,17], -620928000), ([2,9,9], -2813882880), ([2,9,10], -3256750080), ([2,9,11], -746426880), ([2,9,17], -620928000), ([2,10,10], -2725731840), ([2,10,11], -3550748160), ([2,10,17], -620928000), ([2,11,11], -2663055360), ([2,11,12], -268369920), ([2,11,17], -620928000), ([2,12,17], -543312000), ([2,13,13], -798916608), ([2,13,17], -388080000), ([2,14,17], -77616000), ([2,15,17], 77616000), ([2,16,17], 388080000), ([2,17,17], 698544000), ([3,4,4], -1240296960), ([3,4,5], -138479232), ([3,5,5], -1189923840), ([3,5,6], -766109952), ([3,6,7], -1470310272), ([3,7,7], -130230720), ([3,7,8], -1736216832), ([3,8,8], -1336584000), ([3,8,9], -3015897600), ([3,8,10], -171621888), ([3,9,9], -2813882880), ([3,9,10], -3256750080), ([3,9,11], -746426880), ([3,10,10], -2725731840), ([3,10,11], -3550748160), ([3,11,11], -2663055360), ([3,11,12], -268369920), ([3,13,13], -798916608), ([4,4,4], -1240296960), ([4,4,5], -1378776192), ([4,4,6], -1240296960), ([4,4,7], -1240296960), ([4,4,8], -1240296960), ([4,4,9], -1240296960), ([4,4,10], -1240296960), ([4,4,11], -1240296960), ([4,4,12], -1085259840), ([4,4,13], -775185600), ([4,4,14], -155037120), ([4,4,15], 155037120), ([4,4,16], 775185600), ([4,4,17], 1395334080), ([4,5,5], -1328403072), ([4,5,6], -904589184), ([4,5,7], -138479232), ([4,5,8], -138479232), ([4,5,9], -138479232), ([4,5,10], -138479232), ([4,5,11], -138479232), ([4,5,12], -121169328), ([4,5,13], -86549520), ([4,5,14], -17309904), ([4,5,15], 17309904), ([4,5,16], 86549520), ([4,5,17], 155789136), ([4,6,7], -1470310272), ([4,7,7], -130230720), ([4,7,8], -1736216832), ([4,8,8], -1336584000), ([4,8,9], -3015897600), ([4,8,10], -171621888), ([4,9,9], -2813882880), ([4,9,10], -3256750080), ([4,9,11], -746426880), ([4,10,10], -2725731840), ([4,10,11], -3550748160), ([4,11,11], -2663055360), ([4,11,12], -268369920), ([4,13,13], -798916608), ([5,5,5], -1189923840), ([5,5,6], -1956033792), ([5,5,7], -1189923840), ([5,5,8], -1189923840), ([5,5,9], -1189923840), ([5,5,10], -1189923840), ([5,5,11], -1189923840), ([5,5,12], -1041183360), ([5,5,13], -743702400), ([5,5,14], -148740480), ([5,5,15], 148740480), ([5,5,16], 743702400), ([5,5,17], 1338664320), ([5,6,6], -766109952), ([5,6,7], -2236420224), ([5,6,8], -766109952), ([5,6,9], -766109952), ([5,6,10], -766109952), ([5,6,11], -766109952), ([5,6,12], -670346208), ([5,6,13], -478818720), ([5,6,14], -95763744), ([5,6,15], 95763744), ([5,6,16], 478818720), ([5,6,17], 861873696), ([5,7,7], -130230720), ([5,7,8], -1736216832), ([5,8,8], -1336584000), ([5,8,9], -3015897600), ([5,8,10], -171621888), ([5,9,9], -2813882880), ([5,9,10], -3256750080), ([5,9,11], -746426880), ([5,10,10], -2725731840), ([5,10,11], -3550748160), ([5,11,11], -2663055360), ([5,11,12], -268369920), ([5,13,13], -798916608), ([6,6,7], -1470310272), ([6,7,7], -1600540992), ([6,7,8], -3206527104), ([6,7,9], -1470310272), ([6,7,10], -1470310272), ([6,7,11], -1470310272), ([6,7,12], -1286521488), ([6,7,13], -918943920), ([6,7,14], -183788784), ([6,7,15], 183788784), ([6,7,16], 918943920), ([6,7,17], 1654099056), ([6,8,8], -1336584000), ([6,8,9], -3015897600), ([6,8,10], -171621888), ([6,9,9], -2813882880), ([6,9,10], -3256750080), ([6,9,11], -746426880), ([6,10,10], -2725731840), ([6,10,11], -3550748160), ([6,11,11], -2663055360), ([6,11,12], -268369920), ([6,13,13], -798916608), ([7,7,7], -130230720), ([7,7,8], -1866447552), ([7,7,9], -130230720), ([7,7,10], -130230720), ([7,7,11], -130230720), ([7,7,12], -113951880), ([7,7,13], -81394200), ([7,7,14], -16278840), ([7,7,15], 16278840), ([7,7,16], 81394200), ([7,7,17], 146509560), ([7,8,8], -3072800832), ([7,8,9], -4752114432), ([7,8,10], -1907838720), ([7,8,11], -1736216832), ([7,8,12], -1519189728), ([7,8,13], -1085135520), ([7,8,14], -217027104), ([7,8,15], 217027104), ([7,8,16], 1085135520), ([7,8,17], 1953243936), ([7,9,9], -2813882880), ([7,9,10], -3256750080), ([7,9,11], -746426880), ([7,10,10], -2725731840), ([7,10,11], -3550748160), ([7,11,11], -2663055360), ([7,11,12], -268369920), ([7,13,13], -798916608), ([8,8,8], -1336584000), ([8,8,9], -4352481600), ([8,8,10], -1508205888), ([8,8,11], -1336584000), ([8,8,12], -1169511000), ([8,8,13], -835365000), ([8,8,14], -167073000), ([8,8,15], 167073000), ([8,8,16], 835365000), ([8,8,17], 1503657000), ([8,9,9], -5829780480), ([8,9,10], -6444269568), ([8,9,11], -3762324480), ([8,9,12], -2638910400), ([8,9,13], -1884936000), ([8,9,14], -376987200), ([8,9,15], 376987200), ([8,9,16], 1884936000), ([8,9,17], 3392884800), ([8,10,10], -2897353728), ([8,10,11], -3722370048), ([8,10,12], -150169152), ([8,10,13], -107263680), ([8,10,14], -21452736), ([8,10,15], 21452736), ([8,10,16], 107263680), ([8,10,17], 193074624), ([8,11,11], -2663055360), ([8,11,12], -268369920), ([8,13,13], -798916608), ([9,9,9], -2813882880), ([9,9,10], -6070632960), ([9,9,11], -3560309760), ([9,9,12], -2462147520), ([9,9,13], -1758676800), ([9,9,14], -351735360), ([9,9,15], 351735360), ([9,9,16], 1758676800), ([9,9,17], 3165618240), ([9,10,10], -5982481920), ([9,10,11], -7553925120), ([9,10,12], -2849656320), ([9,10,13], -2035468800), ([9,10,14], -407093760), ([9,10,15], 407093760), ([9,10,16], 2035468800), ([9,10,17], 3663843840), ([9,11,11], -3409482240), ([9,11,12], -921493440), ([9,11,13], -466516800), ([9,11,14], -93303360), ([9,11,15], 93303360), ([9,11,16], 466516800), ([9,11,17], 839730240), ([9,13,13], -798916608), ([10,10,10], -2725731840), ([10,10,11], -6276480000), ([10,10,12], -2385015360), ([10,10,13], -1703582400), ([10,10,14], -340716480), ([10,10,15], 340716480), ([10,10,16], 1703582400), ([10,10,17], 3066448320), ([10,11,11], -6213803520), ([10,11,12], -3375274560), ([10,11,13], -2219217600), ([10,11,14], -443843520), ([10,11,15], 443843520), ([10,11,16], 2219217600), ([10,11,17], 3994591680), ([10,13,13], -798916608), ([11,11,11], -2663055360), ([11,11,12], -2598543360), ([11,11,13], -1664409600), ([11,11,14], -332881920), ([11,11,15], 332881920), ([11,11,16], 1664409600), ([11,11,17], 2995937280), ([11,12,12], -234823680), ([11,12,13], -167731200), ([11,12,14], -33546240), ([11,12,15], 33546240), ([11,12,16], 167731200), ([11,12,17], 301916160), ([11,13,13], -798916608), ([12,13,13], -699052032), ([13,13,13], -499322880), ([13,13,14], -99864576), ([13,13,15], 99864576), ([13,13,16], 499322880), ([13,13,17], 898781184)]
theorem block002_data : block002 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (38808000 : Int) atom0095) (SparsePolynomial.scale (77518560 : Int) atom0096)) (SparsePolynomial.merge (SparsePolynomial.scale (8654952 : Int) atom0097) (SparsePolynomial.merge (SparsePolynomial.scale (74370240 : Int) atom0098) (SparsePolynomial.scale (47881872 : Int) atom0099)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (91894392 : Int) atom0100) (SparsePolynomial.scale (8139420 : Int) atom0101)) (SparsePolynomial.merge (SparsePolynomial.scale (108513552 : Int) atom0102) (SparsePolynomial.merge (SparsePolynomial.scale (83536500 : Int) atom0103) (SparsePolynomial.scale (188493600 : Int) atom0104))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10726368 : Int) atom0105) (SparsePolynomial.scale (175867680 : Int) atom0106)) (SparsePolynomial.merge (SparsePolynomial.scale (203546880 : Int) atom0107) (SparsePolynomial.merge (SparsePolynomial.scale (46651680 : Int) atom0108) (SparsePolynomial.scale (170358240 : Int) atom0109)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (221921760 : Int) atom0110) (SparsePolynomial.scale (166440960 : Int) atom0111)) (SparsePolynomial.merge (SparsePolynomial.scale (16773120 : Int) atom0112) (SparsePolynomial.merge (SparsePolynomial.scale (49932288 : Int) atom0113) (SparsePolynomial.scale (409651200 : Int) atom0114)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (305786880 : Int) atom0115) (SparsePolynomial.scale (201922560 : Int) atom0116)) (SparsePolynomial.merge (SparsePolynomial.scale (98058240 : Int) atom0117) (SparsePolynomial.merge (SparsePolynomial.scale (248236800 : Int) atom0118) (SparsePolynomial.scale (1455068160 : Int) atom0119)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1453455360 : Int) atom0120) (SparsePolynomial.scale (1451842560 : Int) atom0121)) (SparsePolynomial.merge (SparsePolynomial.scale (1450229760 : Int) atom0122) (SparsePolynomial.merge (SparsePolynomial.scale (1448616960 : Int) atom0123) (SparsePolynomial.scale (1447004160 : Int) atom0124))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1471008000 : Int) atom0125) (SparsePolynomial.scale (1464879360 : Int) atom0126)) (SparsePolynomial.merge (SparsePolynomial.scale (1471330560 : Int) atom0127) (SparsePolynomial.merge (SparsePolynomial.scale (1512465920 : Int) atom0128) (SparsePolynomial.scale (2885621760 : Int) atom0129)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1132241600 : Int) atom0130) (SparsePolynomial.scale (457390080 : Int) atom0131)) (SparsePolynomial.merge (SparsePolynomial.scale (225565760 : Int) atom0132) (SparsePolynomial.merge (SparsePolynomial.scale (180255040 : Int) atom0133) (SparsePolynomial.scale (1619251200 : Int) atom0134))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3339141120 : Int) atom0135) (SparsePolynomial.scale (3439779840 : Int) atom0136)) (SparsePolynomial.merge (SparsePolynomial.scale (3540418560 : Int) atom0137) (SparsePolynomial.merge (SparsePolynomial.scale (3641057280 : Int) atom0138) (SparsePolynomial.scale (3741696000 : Int) atom0139)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3842334720 : Int) atom0140) (SparsePolynomial.scale (3942973440 : Int) atom0141)) (SparsePolynomial.merge (SparsePolynomial.scale (4043612160 : Int) atom0142) (SparsePolynomial.merge (SparsePolynomial.scale (4144250880 : Int) atom0143) (SparsePolynomial.scale (4982100480 : Int) atom0144))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2934167040 : Int) atom0145) (SparsePolynomial.scale (2444907240 : Int) atom0146)) (SparsePolynomial.merge (SparsePolynomial.scale (450777600 : Int) atom0147) (SparsePolynomial.merge (SparsePolynomial.scale (643184640 : Int) atom0148) (SparsePolynomial.scale (1616025600 : Int) atom0149)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3383009280 : Int) atom0150) (SparsePolynomial.scale (3533967360 : Int) atom0151)) (SparsePolynomial.merge (SparsePolynomial.scale (3684925440 : Int) atom0152) (SparsePolynomial.merge (SparsePolynomial.scale (3835883520 : Int) atom0153) (SparsePolynomial.scale (3986841600 : Int) atom0154)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4137799680 : Int) atom0155) (SparsePolynomial.scale (4288757760 : Int) atom0156)) (SparsePolynomial.merge (SparsePolynomial.scale (4480035840 : Int) atom0157) (SparsePolynomial.merge (SparsePolynomial.scale (5301918720 : Int) atom0158) (SparsePolynomial.scale (3349463040 : Int) atom0159)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2709567720 : Int) atom0160) (SparsePolynomial.scale (867686400 : Int) atom0161)) (SparsePolynomial.merge (SparsePolynomial.scale (1104122880 : Int) atom0162) (SparsePolynomial.merge (SparsePolynomial.scale (56125440 : Int) atom0163) (SparsePolynomial.scale (2283267840 : Int) atom0164))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3957442368 : Int) atom0165) (SparsePolynomial.scale (3881051040 : Int) atom0166)) (SparsePolynomial.merge (SparsePolynomial.scale (3958523520 : Int) atom0167) (SparsePolynomial.merge (SparsePolynomial.scale (4131348480 : Int) atom0168) (SparsePolynomial.scale (4332625920 : Int) atom0169)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4533903360 : Int) atom0170) (SparsePolynomial.scale (4753795200 : Int) atom0171)) (SparsePolynomial.merge (SparsePolynomial.scale (5621736960 : Int) atom0172) (SparsePolynomial.merge (SparsePolynomial.scale (3713534160 : Int) atom0173) (SparsePolynomial.scale (2974228200 : Int) atom0174)))))))) := by decide +kernel
theorem block002_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block002 := by
  rw [block002_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0095_nonneg g hg hA hB) (atom0096_nonneg g hg hA hB)) (add_nonneg (atom0097_nonneg g hg hA hB) (add_nonneg (atom0098_nonneg g hg hA hB) (atom0099_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0100_nonneg g hg hA hB) (atom0101_nonneg g hg hA hB)) (add_nonneg (atom0102_nonneg g hg hA hB) (add_nonneg (atom0103_nonneg g hg hA hB) (atom0104_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0105_nonneg g hg hA hB) (atom0106_nonneg g hg hA hB)) (add_nonneg (atom0107_nonneg g hg hA hB) (add_nonneg (atom0108_nonneg g hg hA hB) (atom0109_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0110_nonneg g hg hA hB) (atom0111_nonneg g hg hA hB)) (add_nonneg (atom0112_nonneg g hg hA hB) (add_nonneg (atom0113_nonneg g hg hA hB) (atom0114_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0115_nonneg g hg hA hB) (atom0116_nonneg g hg hA hB)) (add_nonneg (atom0117_nonneg g hg hA hB) (add_nonneg (atom0118_nonneg g hg hA hB) (atom0119_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0120_nonneg g hg hA hB) (atom0121_nonneg g hg hA hB)) (add_nonneg (atom0122_nonneg g hg hA hB) (add_nonneg (atom0123_nonneg g hg hA hB) (atom0124_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0125_nonneg g hg hA hB) (atom0126_nonneg g hg hA hB)) (add_nonneg (atom0127_nonneg g hg hA hB) (add_nonneg (atom0128_nonneg g hg hA hB) (atom0129_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0130_nonneg g hg hA hB) (atom0131_nonneg g hg hA hB)) (add_nonneg (atom0132_nonneg g hg hA hB) (add_nonneg (atom0133_nonneg g hg hA hB) (atom0134_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0135_nonneg g hg hA hB) (atom0136_nonneg g hg hA hB)) (add_nonneg (atom0137_nonneg g hg hA hB) (add_nonneg (atom0138_nonneg g hg hA hB) (atom0139_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0140_nonneg g hg hA hB) (atom0141_nonneg g hg hA hB)) (add_nonneg (atom0142_nonneg g hg hA hB) (add_nonneg (atom0143_nonneg g hg hA hB) (atom0144_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0145_nonneg g hg hA hB) (atom0146_nonneg g hg hA hB)) (add_nonneg (atom0147_nonneg g hg hA hB) (add_nonneg (atom0148_nonneg g hg hA hB) (atom0149_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0150_nonneg g hg hA hB) (atom0151_nonneg g hg hA hB)) (add_nonneg (atom0152_nonneg g hg hA hB) (add_nonneg (atom0153_nonneg g hg hA hB) (atom0154_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0155_nonneg g hg hA hB) (atom0156_nonneg g hg hA hB)) (add_nonneg (atom0157_nonneg g hg hA hB) (add_nonneg (atom0158_nonneg g hg hA hB) (atom0159_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0160_nonneg g hg hA hB) (atom0161_nonneg g hg hA hB)) (add_nonneg (atom0162_nonneg g hg hA hB) (add_nonneg (atom0163_nonneg g hg hA hB) (atom0164_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0165_nonneg g hg hA hB) (atom0166_nonneg g hg hA hB)) (add_nonneg (atom0167_nonneg g hg hA hB) (add_nonneg (atom0168_nonneg g hg hA hB) (atom0169_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0170_nonneg g hg hA hB) (atom0171_nonneg g hg hA hB)) (add_nonneg (atom0172_nonneg g hg hA hB) (add_nonneg (atom0173_nonneg g hg hA hB) (atom0174_nonneg g hg hA hB))))))))

end APPT.Finite18
