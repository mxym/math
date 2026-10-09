import APPT.Finite21Sparse.Base06
import APPT.Finite21Sparse.Base07
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0096 : SparsePolynomial.Poly := [([0,9,20], -4), ([1,9,20], -8), ([2,9,20], -16), ([3,9,20], -16), ([4,9,20], -16), ([5,9,20], -16), ([6,9,20], -16), ([7,9,20], -16), ([8,9,20], -16), ([9,9,20], -16), ([9,10,20], -16), ([9,11,20], -16), ([9,12,20], -16), ([9,13,20], -16), ([9,14,20], -16), ([9,15,20], -8), ([9,17,20], 8), ([9,18,20], 12), ([9,19,20], 16), ([9,20,20], 18)]
theorem atom0096_data : atom0096 = SparsePolynomial.monoTimes [9,20] 1 base06 := by decide +kernel
theorem eval_atom0096 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0096 = (quadB (outer g) ![1,2,2] * g 9 * g 20) := by
  rw [atom0096_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0096_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1251556516350 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097 : SparsePolynomial.Poly := [([0,10,11], -4), ([1,10,11], -8), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -16), ([10,11,13], -16), ([10,11,14], -16), ([10,11,15], -8), ([10,11,17], 8), ([10,11,18], 12), ([10,11,19], 16), ([10,11,20], 18)]
theorem atom0097_data : atom0097 = SparsePolynomial.monoTimes [10,11] 1 base06 := by decide +kernel
theorem eval_atom0097 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0097 = (quadB (outer g) ![1,2,2] * g 10 * g 11) := by
  rw [atom0097_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0097_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (417466889280 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098 : SparsePolynomial.Poly := [([0,10,12], -4), ([1,10,12], -8), ([2,10,12], -16), ([3,10,12], -16), ([4,10,12], -16), ([5,10,12], -16), ([6,10,12], -16), ([7,10,12], -16), ([8,10,12], -16), ([9,10,12], -16), ([10,10,12], -16), ([10,11,12], -16), ([10,12,12], -16), ([10,12,13], -16), ([10,12,14], -16), ([10,12,15], -8), ([10,12,17], 8), ([10,12,18], 12), ([10,12,19], 16), ([10,12,20], 18)]
theorem atom0098_data : atom0098 = SparsePolynomial.monoTimes [10,12] 1 base06 := by decide +kernel
theorem eval_atom0098 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0098 = (quadB (outer g) ![1,2,2] * g 10 * g 12) := by
  rw [atom0098_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0098_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (906380102880 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099 : SparsePolynomial.Poly := [([0,10,13], -4), ([1,10,13], -8), ([2,10,13], -16), ([3,10,13], -16), ([4,10,13], -16), ([5,10,13], -16), ([6,10,13], -16), ([7,10,13], -16), ([8,10,13], -16), ([9,10,13], -16), ([10,10,13], -16), ([10,11,13], -16), ([10,12,13], -16), ([10,13,13], -16), ([10,13,14], -16), ([10,13,15], -8), ([10,13,17], 8), ([10,13,18], 12), ([10,13,19], 16), ([10,13,20], 18)]
theorem atom0099_data : atom0099 = SparsePolynomial.monoTimes [10,13] 1 base06 := by decide +kernel
theorem eval_atom0099 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0099 = (quadB (outer g) ![1,2,2] * g 10 * g 13) := by
  rw [atom0099_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0099_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (644978048400 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100 : SparsePolynomial.Poly := [([0,10,14], -4), ([1,10,14], -8), ([2,10,14], -16), ([3,10,14], -16), ([4,10,14], -16), ([5,10,14], -16), ([6,10,14], -16), ([7,10,14], -16), ([8,10,14], -16), ([9,10,14], -16), ([10,10,14], -16), ([10,11,14], -16), ([10,12,14], -16), ([10,13,14], -16), ([10,14,14], -16), ([10,14,15], -8), ([10,14,17], 8), ([10,14,18], 12), ([10,14,19], 16), ([10,14,20], 18)]
theorem atom0100_data : atom0100 = SparsePolynomial.monoTimes [10,14] 1 base06 := by decide +kernel
theorem eval_atom0100 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0100 = (quadB (outer g) ![1,2,2] * g 10 * g 14) := by
  rw [atom0100_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0100_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (317707009200 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101 : SparsePolynomial.Poly := [([0,10,16], -4), ([1,10,16], -8), ([2,10,16], -16), ([3,10,16], -16), ([4,10,16], -16), ([5,10,16], -16), ([6,10,16], -16), ([7,10,16], -16), ([8,10,16], -16), ([9,10,16], -16), ([10,10,16], -16), ([10,11,16], -16), ([10,12,16], -16), ([10,13,16], -16), ([10,14,16], -16), ([10,15,16], -8), ([10,16,17], 8), ([10,16,18], 12), ([10,16,19], 16), ([10,16,20], 18)]
theorem atom0101_data : atom0101 = SparsePolynomial.monoTimes [10,16] 1 base06 := by decide +kernel
theorem eval_atom0101 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0101 = (quadB (outer g) ![1,2,2] * g 10 * g 16) := by
  rw [atom0101_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0101_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241725824550 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102 : SparsePolynomial.Poly := [([0,10,18], -4), ([1,10,18], -8), ([2,10,18], -16), ([3,10,18], -16), ([4,10,18], -16), ([5,10,18], -16), ([6,10,18], -16), ([7,10,18], -16), ([8,10,18], -16), ([9,10,18], -16), ([10,10,18], -16), ([10,11,18], -16), ([10,12,18], -16), ([10,13,18], -16), ([10,14,18], -16), ([10,15,18], -8), ([10,17,18], 8), ([10,18,18], 12), ([10,18,19], 16), ([10,18,20], 18)]
theorem atom0102_data : atom0102 = SparsePolynomial.monoTimes [10,18] 1 base06 := by decide +kernel
theorem eval_atom0102 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0102 = (quadB (outer g) ![1,2,2] * g 10 * g 18) := by
  rw [atom0102_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0102_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229660045650 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 18) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103 : SparsePolynomial.Poly := [([0,10,19], -4), ([1,10,19], -8), ([2,10,19], -16), ([3,10,19], -16), ([4,10,19], -16), ([5,10,19], -16), ([6,10,19], -16), ([7,10,19], -16), ([8,10,19], -16), ([9,10,19], -16), ([10,10,19], -16), ([10,11,19], -16), ([10,12,19], -16), ([10,13,19], -16), ([10,14,19], -16), ([10,15,19], -8), ([10,17,19], 8), ([10,18,19], 12), ([10,19,19], 16), ([10,19,20], 18)]
theorem atom0103_data : atom0103 = SparsePolynomial.monoTimes [10,19] 1 base06 := by decide +kernel
theorem eval_atom0103 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0103 = (quadB (outer g) ![1,2,2] * g 10 * g 19) := by
  rw [atom0103_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0103_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1443556935450 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104 : SparsePolynomial.Poly := [([0,10,20], -4), ([1,10,20], -8), ([2,10,20], -16), ([3,10,20], -16), ([4,10,20], -16), ([5,10,20], -16), ([6,10,20], -16), ([7,10,20], -16), ([8,10,20], -16), ([9,10,20], -16), ([10,10,20], -16), ([10,11,20], -16), ([10,12,20], -16), ([10,13,20], -16), ([10,14,20], -16), ([10,15,20], -8), ([10,17,20], 8), ([10,18,20], 12), ([10,19,20], 16), ([10,20,20], 18)]
theorem atom0104_data : atom0104 = SparsePolynomial.monoTimes [10,20] 1 base06 := by decide +kernel
theorem eval_atom0104 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0104 = (quadB (outer g) ![1,2,2] * g 10 * g 20) := by
  rw [atom0104_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0104_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (997540913250 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105 : SparsePolynomial.Poly := [([0,11,12], -4), ([1,11,12], -8), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -16), ([11,12,13], -16), ([11,12,14], -16), ([11,12,15], -8), ([11,12,17], 8), ([11,12,18], 12), ([11,12,19], 16), ([11,12,20], 18)]
theorem atom0105_data : atom0105 = SparsePolynomial.monoTimes [11,12] 1 base06 := by decide +kernel
theorem eval_atom0105 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0105 = (quadB (outer g) ![1,2,2] * g 11 * g 12) := by
  rw [atom0105_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0105_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (390768144480 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106 : SparsePolynomial.Poly := [([0,11,13], -4), ([1,11,13], -8), ([2,11,13], -16), ([3,11,13], -16), ([4,11,13], -16), ([5,11,13], -16), ([6,11,13], -16), ([7,11,13], -16), ([8,11,13], -16), ([9,11,13], -16), ([10,11,13], -16), ([11,11,13], -16), ([11,12,13], -16), ([11,13,13], -16), ([11,13,14], -16), ([11,13,15], -8), ([11,13,17], 8), ([11,13,18], 12), ([11,13,19], 16), ([11,13,20], 18)]
theorem atom0106_data : atom0106 = SparsePolynomial.monoTimes [11,13] 1 base06 := by decide +kernel
theorem eval_atom0106 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0106 = (quadB (outer g) ![1,2,2] * g 11 * g 13) := by
  rw [atom0106_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0106_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (821585116800 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107 : SparsePolynomial.Poly := [([0,11,14], -4), ([1,11,14], -8), ([2,11,14], -16), ([3,11,14], -16), ([4,11,14], -16), ([5,11,14], -16), ([6,11,14], -16), ([7,11,14], -16), ([8,11,14], -16), ([9,11,14], -16), ([10,11,14], -16), ([11,11,14], -16), ([11,12,14], -16), ([11,13,14], -16), ([11,14,14], -16), ([11,14,15], -8), ([11,14,17], 8), ([11,14,18], 12), ([11,14,19], 16), ([11,14,20], 18)]
theorem atom0107_data : atom0107 = SparsePolynomial.monoTimes [11,14] 1 base06 := by decide +kernel
theorem eval_atom0107 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0107 = (quadB (outer g) ![1,2,2] * g 11 * g 14) := by
  rw [atom0107_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0107_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (405398800800 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108 : SparsePolynomial.Poly := [([0,11,16], -4), ([1,11,16], -8), ([2,11,16], -16), ([3,11,16], -16), ([4,11,16], -16), ([5,11,16], -16), ([6,11,16], -16), ([7,11,16], -16), ([8,11,16], -16), ([9,11,16], -16), ([10,11,16], -16), ([11,11,16], -16), ([11,12,16], -16), ([11,13,16], -16), ([11,14,16], -16), ([11,15,16], -8), ([11,16,17], 8), ([11,16,18], 12), ([11,16,19], 16), ([11,16,20], 18)]
theorem atom0108_data : atom0108 = SparsePolynomial.monoTimes [11,16] 1 base06 := by decide +kernel
theorem eval_atom0108 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0108 = (quadB (outer g) ![1,2,2] * g 11 * g 16) := by
  rw [atom0108_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0108_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164356819200 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109 : SparsePolynomial.Poly := [([0,11,19], -4), ([1,11,19], -8), ([2,11,19], -16), ([3,11,19], -16), ([4,11,19], -16), ([5,11,19], -16), ([6,11,19], -16), ([7,11,19], -16), ([8,11,19], -16), ([9,11,19], -16), ([10,11,19], -16), ([11,11,19], -16), ([11,12,19], -16), ([11,13,19], -16), ([11,14,19], -16), ([11,15,19], -8), ([11,17,19], 8), ([11,18,19], 12), ([11,19,19], 16), ([11,19,20], 18)]
theorem atom0109_data : atom0109 = SparsePolynomial.monoTimes [11,19] 1 base06 := by decide +kernel
theorem eval_atom0109 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0109 = (quadB (outer g) ![1,2,2] * g 11 * g 19) := by
  rw [atom0109_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0109_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1156414996800 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110 : SparsePolynomial.Poly := [([0,11,20], -4), ([1,11,20], -8), ([2,11,20], -16), ([3,11,20], -16), ([4,11,20], -16), ([5,11,20], -16), ([6,11,20], -16), ([7,11,20], -16), ([8,11,20], -16), ([9,11,20], -16), ([10,11,20], -16), ([11,11,20], -16), ([11,12,20], -16), ([11,13,20], -16), ([11,14,20], -16), ([11,15,20], -8), ([11,17,20], 8), ([11,18,20], 12), ([11,19,20], 16), ([11,20,20], 18)]
theorem atom0110_data : atom0110 = SparsePolynomial.monoTimes [11,20] 1 base06 := by decide +kernel
theorem eval_atom0110 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0110 = (quadB (outer g) ![1,2,2] * g 11 * g 20) := by
  rw [atom0110_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0110_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (638510040000 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111 : SparsePolynomial.Poly := [([0,12,13], -4), ([1,12,13], -8), ([2,12,13], -16), ([3,12,13], -16), ([4,12,13], -16), ([5,12,13], -16), ([6,12,13], -16), ([7,12,13], -16), ([8,12,13], -16), ([9,12,13], -16), ([10,12,13], -16), ([11,12,13], -16), ([12,12,13], -16), ([12,13,13], -16), ([12,13,14], -16), ([12,13,15], -8), ([12,13,17], 8), ([12,13,18], 12), ([12,13,19], 16), ([12,13,20], 18)]
theorem atom0111_data : atom0111 = SparsePolynomial.monoTimes [12,13] 1 base06 := by decide +kernel
theorem eval_atom0111 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0111 = (quadB (outer g) ![1,2,2] * g 12 * g 13) := by
  rw [atom0111_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0111_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (330801340800 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112 : SparsePolynomial.Poly := [([0,12,14], -4), ([1,12,14], -8), ([2,12,14], -16), ([3,12,14], -16), ([4,12,14], -16), ([5,12,14], -16), ([6,12,14], -16), ([7,12,14], -16), ([8,12,14], -16), ([9,12,14], -16), ([10,12,14], -16), ([11,12,14], -16), ([12,12,14], -16), ([12,13,14], -16), ([12,14,14], -16), ([12,14,15], -8), ([12,14,17], 8), ([12,14,18], 12), ([12,14,19], 16), ([12,14,20], 18)]
theorem atom0112_data : atom0112 = SparsePolynomial.monoTimes [12,14] 1 base06 := by decide +kernel
theorem eval_atom0112 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0112 = (quadB (outer g) ![1,2,2] * g 12 * g 14) := by
  rw [atom0112_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0112_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (650421156000 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113 : SparsePolynomial.Poly := [([0,12,16], -4), ([1,12,16], -8), ([2,12,16], -16), ([3,12,16], -16), ([4,12,16], -16), ([5,12,16], -16), ([6,12,16], -16), ([7,12,16], -16), ([8,12,16], -16), ([9,12,16], -16), ([10,12,16], -16), ([11,12,16], -16), ([12,12,16], -16), ([12,13,16], -16), ([12,14,16], -16), ([12,15,16], -8), ([12,16,17], 8), ([12,16,18], 12), ([12,16,19], 16), ([12,16,20], 18)]
theorem atom0113_data : atom0113 = SparsePolynomial.monoTimes [12,16] 1 base06 := by decide +kernel
theorem eval_atom0113 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0113 = (quadB (outer g) ![1,2,2] * g 12 * g 16) := by
  rw [atom0113_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0113_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (271117319200 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114 : SparsePolynomial.Poly := [([0,12,19], -4), ([1,12,19], -8), ([2,12,19], -16), ([3,12,19], -16), ([4,12,19], -16), ([5,12,19], -16), ([6,12,19], -16), ([7,12,19], -16), ([8,12,19], -16), ([9,12,19], -16), ([10,12,19], -16), ([11,12,19], -16), ([12,12,19], -16), ([12,13,19], -16), ([12,14,19], -16), ([12,15,19], -8), ([12,17,19], 8), ([12,18,19], 12), ([12,19,19], 16), ([12,19,20], 18)]
theorem atom0114_data : atom0114 = SparsePolynomial.monoTimes [12,19] 1 base06 := by decide +kernel
theorem eval_atom0114 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0114 = (quadB (outer g) ![1,2,2] * g 12 * g 19) := by
  rw [atom0114_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0114_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (808085588800 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115 : SparsePolynomial.Poly := [([0,12,20], -4), ([1,12,20], -8), ([2,12,20], -16), ([3,12,20], -16), ([4,12,20], -16), ([5,12,20], -16), ([6,12,20], -16), ([7,12,20], -16), ([8,12,20], -16), ([9,12,20], -16), ([10,12,20], -16), ([11,12,20], -16), ([12,12,20], -16), ([12,13,20], -16), ([12,14,20], -16), ([12,15,20], -8), ([12,17,20], 8), ([12,18,20], 12), ([12,19,20], 16), ([12,20,20], 18)]
theorem atom0115_data : atom0115 = SparsePolynomial.monoTimes [12,20] 1 base06 := by decide +kernel
theorem eval_atom0115 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0115 = (quadB (outer g) ![1,2,2] * g 12 * g 20) := by
  rw [atom0115_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0115_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (224744637600 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116 : SparsePolynomial.Poly := [([0,13,15], -4), ([1,13,15], -8), ([2,13,15], -16), ([3,13,15], -16), ([4,13,15], -16), ([5,13,15], -16), ([6,13,15], -16), ([7,13,15], -16), ([8,13,15], -16), ([9,13,15], -16), ([10,13,15], -16), ([11,13,15], -16), ([12,13,15], -16), ([13,13,15], -16), ([13,14,15], -16), ([13,15,15], -8), ([13,15,17], 8), ([13,15,18], 12), ([13,15,19], 16), ([13,15,20], 18)]
theorem atom0116_data : atom0116 = SparsePolynomial.monoTimes [13,15] 1 base06 := by decide +kernel
theorem eval_atom0116 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0116 = (quadB (outer g) ![1,2,2] * g 13 * g 15) := by
  rw [atom0116_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0116_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49939337700 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117 : SparsePolynomial.Poly := [([0,13,16], -4), ([1,13,16], -8), ([2,13,16], -16), ([3,13,16], -16), ([4,13,16], -16), ([5,13,16], -16), ([6,13,16], -16), ([7,13,16], -16), ([8,13,16], -16), ([9,13,16], -16), ([10,13,16], -16), ([11,13,16], -16), ([12,13,16], -16), ([13,13,16], -16), ([13,14,16], -16), ([13,15,16], -8), ([13,16,17], 8), ([13,16,18], 12), ([13,16,19], 16), ([13,16,20], 18)]
theorem atom0117_data : atom0117 = SparsePolynomial.monoTimes [13,16] 1 base06 := by decide +kernel
theorem eval_atom0117 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0117 = (quadB (outer g) ![1,2,2] * g 13 * g 16) := by
  rw [atom0117_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0117_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (194120325900 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118 : SparsePolynomial.Poly := [([0,13,19], -4), ([1,13,19], -8), ([2,13,19], -16), ([3,13,19], -16), ([4,13,19], -16), ([5,13,19], -16), ([6,13,19], -16), ([7,13,19], -16), ([8,13,19], -16), ([9,13,19], -16), ([10,13,19], -16), ([11,13,19], -16), ([12,13,19], -16), ([13,13,19], -16), ([13,14,19], -16), ([13,15,19], -8), ([13,17,19], 8), ([13,18,19], 12), ([13,19,19], 16), ([13,19,20], 18)]
theorem atom0118_data : atom0118 = SparsePolynomial.monoTimes [13,19] 1 base06 := by decide +kernel
theorem eval_atom0118 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0118 = (quadB (outer g) ![1,2,2] * g 13 * g 19) := by
  rw [atom0118_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0118_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (292376711700 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119 : SparsePolynomial.Poly := [([0,14,15], -4), ([1,14,15], -8), ([2,14,15], -16), ([3,14,15], -16), ([4,14,15], -16), ([5,14,15], -16), ([6,14,15], -16), ([7,14,15], -16), ([8,14,15], -16), ([9,14,15], -16), ([10,14,15], -16), ([11,14,15], -16), ([12,14,15], -16), ([13,14,15], -16), ([14,14,15], -16), ([14,15,15], -8), ([14,15,17], 8), ([14,15,18], 12), ([14,15,19], 16), ([14,15,20], 18)]
theorem atom0119_data : atom0119 = SparsePolynomial.monoTimes [14,15] 1 base06 := by decide +kernel
theorem eval_atom0119 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0119 = (quadB (outer g) ![1,2,2] * g 14 * g 15) := by
  rw [atom0119_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0119_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10631174400 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -16), ([0,1,4], -16), ([0,1,5], -16), ([0,1,6], -16), ([0,1,7], -16), ([0,1,8], -16), ([0,1,9], -16), ([0,1,10], -16), ([0,1,11], -16), ([0,1,12], -16), ([0,1,13], -16), ([0,1,14], -16), ([0,1,15], -14), ([0,1,16], -10), ([0,1,17], -2), ([0,1,18], 2), ([0,1,19], 10), ([0,1,20], 18)]
theorem atom0120_data : atom0120 = SparsePolynomial.monoTimes [0,1] 1 base07 := by decide +kernel
theorem eval_atom0120 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0120 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0120_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0120_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113801889600 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -16), ([0,2,4], -16), ([0,2,5], -16), ([0,2,6], -16), ([0,2,7], -16), ([0,2,8], -16), ([0,2,9], -16), ([0,2,10], -16), ([0,2,11], -16), ([0,2,12], -16), ([0,2,13], -16), ([0,2,14], -16), ([0,2,15], -14), ([0,2,16], -10), ([0,2,17], -2), ([0,2,18], 2), ([0,2,19], 10), ([0,2,20], 18)]
theorem atom0121_data : atom0121 = SparsePolynomial.monoTimes [0,2] 1 base07 := by decide +kernel
theorem eval_atom0121 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0121 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0121_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0121_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167199379200 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122 : SparsePolynomial.Poly := [([0,0,3], -8), ([0,1,3], -12), ([0,2,3], -16), ([0,3,3], -16), ([0,3,4], -16), ([0,3,5], -16), ([0,3,6], -16), ([0,3,7], -16), ([0,3,8], -16), ([0,3,9], -16), ([0,3,10], -16), ([0,3,11], -16), ([0,3,12], -16), ([0,3,13], -16), ([0,3,14], -16), ([0,3,15], -14), ([0,3,16], -10), ([0,3,17], -2), ([0,3,18], 2), ([0,3,19], 10), ([0,3,20], 18)]
theorem atom0122_data : atom0122 = SparsePolynomial.monoTimes [0,3] 1 base07 := by decide +kernel
theorem eval_atom0122 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0122 = (quadB (outer g) ![2,2,1] * g 0 * g 3) := by
  rw [atom0122_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0122_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220596868800 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123 : SparsePolynomial.Poly := [([0,0,4], -8), ([0,1,4], -12), ([0,2,4], -16), ([0,3,4], -16), ([0,4,4], -16), ([0,4,5], -16), ([0,4,6], -16), ([0,4,7], -16), ([0,4,8], -16), ([0,4,9], -16), ([0,4,10], -16), ([0,4,11], -16), ([0,4,12], -16), ([0,4,13], -16), ([0,4,14], -16), ([0,4,15], -14), ([0,4,16], -10), ([0,4,17], -2), ([0,4,18], 2), ([0,4,19], 10), ([0,4,20], 18)]
theorem atom0123_data : atom0123 = SparsePolynomial.monoTimes [0,4] 1 base07 := by decide +kernel
theorem eval_atom0123 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0123 = (quadB (outer g) ![2,2,1] * g 0 * g 4) := by
  rw [atom0123_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0123_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (273994358400 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124 : SparsePolynomial.Poly := [([0,0,5], -8), ([0,1,5], -12), ([0,2,5], -16), ([0,3,5], -16), ([0,4,5], -16), ([0,5,5], -16), ([0,5,6], -16), ([0,5,7], -16), ([0,5,8], -16), ([0,5,9], -16), ([0,5,10], -16), ([0,5,11], -16), ([0,5,12], -16), ([0,5,13], -16), ([0,5,14], -16), ([0,5,15], -14), ([0,5,16], -10), ([0,5,17], -2), ([0,5,18], 2), ([0,5,19], 10), ([0,5,20], 18)]
theorem atom0124_data : atom0124 = SparsePolynomial.monoTimes [0,5] 1 base07 := by decide +kernel
theorem eval_atom0124 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0124 = (quadB (outer g) ![2,2,1] * g 0 * g 5) := by
  rw [atom0124_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0124_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140969602656 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125 : SparsePolynomial.Poly := [([0,0,6], -8), ([0,1,6], -12), ([0,2,6], -16), ([0,3,6], -16), ([0,4,6], -16), ([0,5,6], -16), ([0,6,6], -16), ([0,6,7], -16), ([0,6,8], -16), ([0,6,9], -16), ([0,6,10], -16), ([0,6,11], -16), ([0,6,12], -16), ([0,6,13], -16), ([0,6,14], -16), ([0,6,15], -14), ([0,6,16], -10), ([0,6,17], -2), ([0,6,18], 2), ([0,6,19], 10), ([0,6,20], 18)]
theorem atom0125_data : atom0125 = SparsePolynomial.monoTimes [0,6] 1 base07 := by decide +kernel
theorem eval_atom0125 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0125 = (quadB (outer g) ![2,2,1] * g 0 * g 6) := by
  rw [atom0125_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0125_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137701468800 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126 : SparsePolynomial.Poly := [([0,0,7], -8), ([0,1,7], -12), ([0,2,7], -16), ([0,3,7], -16), ([0,4,7], -16), ([0,5,7], -16), ([0,6,7], -16), ([0,7,7], -16), ([0,7,8], -16), ([0,7,9], -16), ([0,7,10], -16), ([0,7,11], -16), ([0,7,12], -16), ([0,7,13], -16), ([0,7,14], -16), ([0,7,15], -14), ([0,7,16], -10), ([0,7,17], -2), ([0,7,18], 2), ([0,7,19], 10), ([0,7,20], 18)]
theorem atom0126_data : atom0126 = SparsePolynomial.monoTimes [0,7] 1 base07 := by decide +kernel
theorem eval_atom0126 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0126 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0126_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0126_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9374417712 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127 : SparsePolynomial.Poly := [([0,0,11], -8), ([0,1,11], -12), ([0,2,11], -16), ([0,3,11], -16), ([0,4,11], -16), ([0,5,11], -16), ([0,6,11], -16), ([0,7,11], -16), ([0,8,11], -16), ([0,9,11], -16), ([0,10,11], -16), ([0,11,11], -16), ([0,11,12], -16), ([0,11,13], -16), ([0,11,14], -16), ([0,11,15], -14), ([0,11,16], -10), ([0,11,17], -2), ([0,11,18], 2), ([0,11,19], 10), ([0,11,20], 18)]
theorem atom0127_data : atom0127 = SparsePolynomial.monoTimes [0,11] 1 base07 := by decide +kernel
theorem eval_atom0127 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0127 = (quadB (outer g) ![2,2,1] * g 0 * g 11) := by
  rw [atom0127_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0127_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38990448000 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128 : SparsePolynomial.Poly := [([0,0,12], -8), ([0,1,12], -12), ([0,2,12], -16), ([0,3,12], -16), ([0,4,12], -16), ([0,5,12], -16), ([0,6,12], -16), ([0,7,12], -16), ([0,8,12], -16), ([0,9,12], -16), ([0,10,12], -16), ([0,11,12], -16), ([0,12,12], -16), ([0,12,13], -16), ([0,12,14], -16), ([0,12,15], -14), ([0,12,16], -10), ([0,12,17], -2), ([0,12,18], 2), ([0,12,19], 10), ([0,12,20], 18)]
theorem atom0128_data : atom0128 = SparsePolynomial.monoTimes [0,12] 1 base07 := by decide +kernel
theorem eval_atom0128 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0128 = (quadB (outer g) ![2,2,1] * g 0 * g 12) := by
  rw [atom0128_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0128_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (334175038400 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129 : SparsePolynomial.Poly := [([0,0,13], -8), ([0,1,13], -12), ([0,2,13], -16), ([0,3,13], -16), ([0,4,13], -16), ([0,5,13], -16), ([0,6,13], -16), ([0,7,13], -16), ([0,8,13], -16), ([0,9,13], -16), ([0,10,13], -16), ([0,11,13], -16), ([0,12,13], -16), ([0,13,13], -16), ([0,13,14], -16), ([0,13,15], -14), ([0,13,16], -10), ([0,13,17], -2), ([0,13,18], 2), ([0,13,19], 10), ([0,13,20], 18)]
theorem atom0129_data : atom0129 = SparsePolynomial.monoTimes [0,13] 1 base07 := by decide +kernel
theorem eval_atom0129 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0129 = (quadB (outer g) ![2,2,1] * g 0 * g 13) := by
  rw [atom0129_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0129_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411474772800 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130 : SparsePolynomial.Poly := [([0,0,14], -8), ([0,1,14], -12), ([0,2,14], -16), ([0,3,14], -16), ([0,4,14], -16), ([0,5,14], -16), ([0,6,14], -16), ([0,7,14], -16), ([0,8,14], -16), ([0,9,14], -16), ([0,10,14], -16), ([0,11,14], -16), ([0,12,14], -16), ([0,13,14], -16), ([0,14,14], -16), ([0,14,15], -14), ([0,14,16], -10), ([0,14,17], -2), ([0,14,18], 2), ([0,14,19], 10), ([0,14,20], 18)]
theorem atom0130_data : atom0130 = SparsePolynomial.monoTimes [0,14] 1 base07 := by decide +kernel
theorem eval_atom0130 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0130 = (quadB (outer g) ![2,2,1] * g 0 * g 14) := by
  rw [atom0130_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0130_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379098014400 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131 : SparsePolynomial.Poly := [([0,0,19], -8), ([0,1,19], -12), ([0,2,19], -16), ([0,3,19], -16), ([0,4,19], -16), ([0,5,19], -16), ([0,6,19], -16), ([0,7,19], -16), ([0,8,19], -16), ([0,9,19], -16), ([0,10,19], -16), ([0,11,19], -16), ([0,12,19], -16), ([0,13,19], -16), ([0,14,19], -16), ([0,15,19], -14), ([0,16,19], -10), ([0,17,19], -2), ([0,18,19], 2), ([0,19,19], 10), ([0,19,20], 18)]
theorem atom0131_data : atom0131 = SparsePolynomial.monoTimes [0,19] 1 base07 := by decide +kernel
theorem eval_atom0131 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0131 = (quadB (outer g) ![2,2,1] * g 0 * g 19) := by
  rw [atom0131_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0131_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130231886400 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -16), ([1,1,7], -16), ([1,1,8], -16), ([1,1,9], -16), ([1,1,10], -16), ([1,1,11], -16), ([1,1,12], -16), ([1,1,13], -16), ([1,1,14], -16), ([1,1,15], -14), ([1,1,16], -10), ([1,1,17], -2), ([1,1,18], 2), ([1,1,19], 10), ([1,1,20], 18)]
theorem atom0132_data : atom0132 = SparsePolynomial.monoTimes [1,1] 1 base07 := by decide +kernel
theorem eval_atom0132 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0132 = (quadB (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0132_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0132_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151735852800 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133 : SparsePolynomial.Poly := [([0,1,20], -8), ([1,1,20], -12), ([1,2,20], -16), ([1,3,20], -16), ([1,4,20], -16), ([1,5,20], -16), ([1,6,20], -16), ([1,7,20], -16), ([1,8,20], -16), ([1,9,20], -16), ([1,10,20], -16), ([1,11,20], -16), ([1,12,20], -16), ([1,13,20], -16), ([1,14,20], -16), ([1,15,20], -14), ([1,16,20], -10), ([1,17,20], -2), ([1,18,20], 2), ([1,19,20], 10), ([1,20,20], 18)]
theorem atom0133_data : atom0133 = SparsePolynomial.monoTimes [1,20] 1 base07 := by decide +kernel
theorem eval_atom0133 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0133 = (quadB (outer g) ![2,2,1] * g 1 * g 20) := by
  rw [atom0133_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0133_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159185728800 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134 : SparsePolynomial.Poly := [([0,2,20], -8), ([1,2,20], -12), ([2,2,20], -16), ([2,3,20], -16), ([2,4,20], -16), ([2,5,20], -16), ([2,6,20], -16), ([2,7,20], -16), ([2,8,20], -16), ([2,9,20], -16), ([2,10,20], -16), ([2,11,20], -16), ([2,12,20], -16), ([2,13,20], -16), ([2,14,20], -16), ([2,15,20], -14), ([2,16,20], -10), ([2,17,20], -2), ([2,18,20], 2), ([2,19,20], 10), ([2,20,20], 18)]
theorem atom0134_data : atom0134 = SparsePolynomial.monoTimes [2,20] 1 base07 := by decide +kernel
theorem eval_atom0134 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0134 = (quadB (outer g) ![2,2,1] * g 2 * g 20) := by
  rw [atom0134_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0134_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188220110400 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 2 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -16), ([4,4,4], -16), ([4,4,5], -16), ([4,4,6], -16), ([4,4,7], -16), ([4,4,8], -16), ([4,4,9], -16), ([4,4,10], -16), ([4,4,11], -16), ([4,4,12], -16), ([4,4,13], -16), ([4,4,14], -16), ([4,4,15], -14), ([4,4,16], -10), ([4,4,17], -2), ([4,4,18], 2), ([4,4,19], 10), ([4,4,20], 18)]
theorem atom0135_data : atom0135 = SparsePolynomial.monoTimes [4,4] 1 base07 := by decide +kernel
theorem eval_atom0135 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0135 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0135_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0135_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32234743800 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136 : SparsePolynomial.Poly := [([0,5,5], -8), ([1,5,5], -12), ([2,5,5], -16), ([3,5,5], -16), ([4,5,5], -16), ([5,5,5], -16), ([5,5,6], -16), ([5,5,7], -16), ([5,5,8], -16), ([5,5,9], -16), ([5,5,10], -16), ([5,5,11], -16), ([5,5,12], -16), ([5,5,13], -16), ([5,5,14], -16), ([5,5,15], -14), ([5,5,16], -10), ([5,5,17], -2), ([5,5,18], 2), ([5,5,19], 10), ([5,5,20], 18)]
theorem atom0136_data : atom0136 = SparsePolynomial.monoTimes [5,5] 1 base07 := by decide +kernel
theorem eval_atom0136 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0136 = (quadB (outer g) ![2,2,1] * g 5 * g 5) := by
  rw [atom0136_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0136_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68482848960 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137 : SparsePolynomial.Poly := [([0,5,6], -8), ([1,5,6], -12), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -16), ([5,6,10], -16), ([5,6,11], -16), ([5,6,12], -16), ([5,6,13], -16), ([5,6,14], -16), ([5,6,15], -14), ([5,6,16], -10), ([5,6,17], -2), ([5,6,18], 2), ([5,6,19], 10), ([5,6,20], 18)]
theorem atom0137_data : atom0137 = SparsePolynomial.monoTimes [5,6] 1 base07 := by decide +kernel
theorem eval_atom0137 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0137 = (quadB (outer g) ![2,2,1] * g 5 * g 6) := by
  rw [atom0137_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0137_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34806427776 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138 : SparsePolynomial.Poly := [([0,6,7], -8), ([1,6,7], -12), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -16), ([6,7,10], -16), ([6,7,11], -16), ([6,7,12], -16), ([6,7,13], -16), ([6,7,14], -16), ([6,7,15], -14), ([6,7,16], -10), ([6,7,17], -2), ([6,7,18], 2), ([6,7,19], 10), ([6,7,20], 18)]
theorem atom0138_data : atom0138 = SparsePolynomial.monoTimes [6,7] 1 base07 := by decide +kernel
theorem eval_atom0138 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0138 = (quadB (outer g) ![2,2,1] * g 6 * g 7) := by
  rw [atom0138_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0138_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278634473856 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139 : SparsePolynomial.Poly := [([0,7,7], -8), ([1,7,7], -12), ([2,7,7], -16), ([3,7,7], -16), ([4,7,7], -16), ([5,7,7], -16), ([6,7,7], -16), ([7,7,7], -16), ([7,7,8], -16), ([7,7,9], -16), ([7,7,10], -16), ([7,7,11], -16), ([7,7,12], -16), ([7,7,13], -16), ([7,7,14], -16), ([7,7,15], -14), ([7,7,16], -10), ([7,7,17], -2), ([7,7,18], 2), ([7,7,19], 10), ([7,7,20], 18)]
theorem atom0139_data : atom0139 = SparsePolynomial.monoTimes [7,7] 1 base07 := by decide +kernel
theorem eval_atom0139 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0139 = (quadB (outer g) ![2,2,1] * g 7 * g 7) := by
  rw [atom0139_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0139_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (231712335936 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140 : SparsePolynomial.Poly := [([0,7,8], -8), ([1,7,8], -12), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -16), ([7,8,13], -16), ([7,8,14], -16), ([7,8,15], -14), ([7,8,16], -10), ([7,8,17], -2), ([7,8,18], 2), ([7,8,19], 10), ([7,8,20], 18)]
theorem atom0140_data : atom0140 = SparsePolynomial.monoTimes [7,8] 1 base07 := by decide +kernel
theorem eval_atom0140 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0140 = (quadB (outer g) ![2,2,1] * g 7 * g 8) := by
  rw [atom0140_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0140_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (335369083176 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141 : SparsePolynomial.Poly := [([0,8,8], -8), ([1,8,8], -12), ([2,8,8], -16), ([3,8,8], -16), ([4,8,8], -16), ([5,8,8], -16), ([6,8,8], -16), ([7,8,8], -16), ([8,8,8], -16), ([8,8,9], -16), ([8,8,10], -16), ([8,8,11], -16), ([8,8,12], -16), ([8,8,13], -16), ([8,8,14], -16), ([8,8,15], -14), ([8,8,16], -10), ([8,8,17], -2), ([8,8,18], 2), ([8,8,19], 10), ([8,8,20], 18)]
theorem atom0141_data : atom0141 = SparsePolynomial.monoTimes [8,8] 1 base07 := by decide +kernel
theorem eval_atom0141 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0141 = (quadB (outer g) ![2,2,1] * g 8 * g 8) := by
  rw [atom0141_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0141_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (380934243900 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142 : SparsePolynomial.Poly := [([0,8,9], -8), ([1,8,9], -12), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -16), ([8,9,13], -16), ([8,9,14], -16), ([8,9,15], -14), ([8,9,16], -10), ([8,9,17], -2), ([8,9,18], 2), ([8,9,19], 10), ([8,9,20], 18)]
theorem atom0142_data : atom0142 = SparsePolynomial.monoTimes [8,9] 1 base07 := by decide +kernel
theorem eval_atom0142 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0142 = (quadB (outer g) ![2,2,1] * g 8 * g 9) := by
  rw [atom0142_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0142_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (488307156120 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143 : SparsePolynomial.Poly := [([0,9,9], -8), ([1,9,9], -12), ([2,9,9], -16), ([3,9,9], -16), ([4,9,9], -16), ([5,9,9], -16), ([6,9,9], -16), ([7,9,9], -16), ([8,9,9], -16), ([9,9,9], -16), ([9,9,10], -16), ([9,9,11], -16), ([9,9,12], -16), ([9,9,13], -16), ([9,9,14], -16), ([9,9,15], -14), ([9,9,16], -10), ([9,9,17], -2), ([9,9,18], 2), ([9,9,19], 10), ([9,9,20], 18)]
theorem atom0143_data : atom0143 = SparsePolynomial.monoTimes [9,9] 1 base07 := by decide +kernel
theorem eval_atom0143 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0143 = (quadB (outer g) ![2,2,1] * g 9 * g 9) := by
  rw [atom0143_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0143_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (697449337200 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144 : SparsePolynomial.Poly := [([0,9,10], -8), ([1,9,10], -12), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -16), ([9,10,13], -16), ([9,10,14], -16), ([9,10,15], -14), ([9,10,16], -10), ([9,10,17], -2), ([9,10,18], 2), ([9,10,19], 10), ([9,10,20], 18)]
theorem atom0144_data : atom0144 = SparsePolynomial.monoTimes [9,10] 1 base07 := by decide +kernel
theorem eval_atom0144 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0144 = (quadB (outer g) ![2,2,1] * g 9 * g 10) := by
  rw [atom0144_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0144_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (611260312320 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145 : SparsePolynomial.Poly := [([0,10,10], -8), ([1,10,10], -12), ([2,10,10], -16), ([3,10,10], -16), ([4,10,10], -16), ([5,10,10], -16), ([6,10,10], -16), ([7,10,10], -16), ([8,10,10], -16), ([9,10,10], -16), ([10,10,10], -16), ([10,10,11], -16), ([10,10,12], -16), ([10,10,13], -16), ([10,10,14], -16), ([10,10,15], -14), ([10,10,16], -10), ([10,10,17], -2), ([10,10,18], 2), ([10,10,19], 10), ([10,10,20], 18)]
theorem atom0145_data : atom0145 = SparsePolynomial.monoTimes [10,10] 1 base07 := by decide +kernel
theorem eval_atom0145 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0145 = (quadB (outer g) ![2,2,1] * g 10 * g 10) := by
  rw [atom0145_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0145_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (742269402000 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146 : SparsePolynomial.Poly := [([0,10,11], -8), ([1,10,11], -12), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -16), ([10,11,13], -16), ([10,11,14], -16), ([10,11,15], -14), ([10,11,16], -10), ([10,11,17], -2), ([10,11,18], 2), ([10,11,19], 10), ([10,11,20], 18)]
theorem atom0146_data : atom0146 = SparsePolynomial.monoTimes [10,11] 1 base07 := by decide +kernel
theorem eval_atom0146 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0146 = (quadB (outer g) ![2,2,1] * g 10 * g 11) := by
  rw [atom0146_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0146_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (690133061520 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147 : SparsePolynomial.Poly := [([0,10,12], -8), ([1,10,12], -12), ([2,10,12], -16), ([3,10,12], -16), ([4,10,12], -16), ([5,10,12], -16), ([6,10,12], -16), ([7,10,12], -16), ([8,10,12], -16), ([9,10,12], -16), ([10,10,12], -16), ([10,11,12], -16), ([10,12,12], -16), ([10,12,13], -16), ([10,12,14], -16), ([10,12,15], -14), ([10,12,16], -10), ([10,12,17], -2), ([10,12,18], 2), ([10,12,19], 10), ([10,12,20], 18)]
theorem atom0147_data : atom0147 = SparsePolynomial.monoTimes [10,12] 1 base07 := by decide +kernel
theorem eval_atom0147 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0147 = (quadB (outer g) ![2,2,1] * g 10 * g 12) := by
  rw [atom0147_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0147_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11030738320 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148 : SparsePolynomial.Poly := [([0,11,11], -8), ([1,11,11], -12), ([2,11,11], -16), ([3,11,11], -16), ([4,11,11], -16), ([5,11,11], -16), ([6,11,11], -16), ([7,11,11], -16), ([8,11,11], -16), ([9,11,11], -16), ([10,11,11], -16), ([11,11,11], -16), ([11,11,12], -16), ([11,11,13], -16), ([11,11,14], -16), ([11,11,15], -14), ([11,11,16], -10), ([11,11,17], -2), ([11,11,18], 2), ([11,11,19], 10), ([11,11,20], 18)]
theorem atom0148_data : atom0148 = SparsePolynomial.monoTimes [11,11] 1 base07 := by decide +kernel
theorem eval_atom0148 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0148 = (quadB (outer g) ![2,2,1] * g 11 * g 11) := by
  rw [atom0148_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0148_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (776322086400 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149 : SparsePolynomial.Poly := [([0,11,12], -8), ([1,11,12], -12), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -16), ([11,12,13], -16), ([11,12,14], -16), ([11,12,15], -14), ([11,12,16], -10), ([11,12,17], -2), ([11,12,18], 2), ([11,12,19], 10), ([11,12,20], 18)]
theorem atom0149_data : atom0149 = SparsePolynomial.monoTimes [11,12] 1 base07 := by decide +kernel
theorem eval_atom0149 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0149 = (quadB (outer g) ![2,2,1] * g 11 * g 12) := by
  rw [atom0149_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0149_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (792165041920 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150 : SparsePolynomial.Poly := [([0,12,12], -8), ([1,12,12], -12), ([2,12,12], -16), ([3,12,12], -16), ([4,12,12], -16), ([5,12,12], -16), ([6,12,12], -16), ([7,12,12], -16), ([8,12,12], -16), ([9,12,12], -16), ([10,12,12], -16), ([11,12,12], -16), ([12,12,12], -16), ([12,12,13], -16), ([12,12,14], -16), ([12,12,15], -14), ([12,12,16], -10), ([12,12,17], -2), ([12,12,18], 2), ([12,12,19], 10), ([12,12,20], 18)]
theorem atom0150_data : atom0150 = SparsePolynomial.monoTimes [12,12] 1 base07 := by decide +kernel
theorem eval_atom0150 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0150 = (quadB (outer g) ![2,2,1] * g 12 * g 12) := by
  rw [atom0150_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0150_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (844301382400 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151 : SparsePolynomial.Poly := [([0,12,13], -8), ([1,12,13], -12), ([2,12,13], -16), ([3,12,13], -16), ([4,12,13], -16), ([5,12,13], -16), ([6,12,13], -16), ([7,12,13], -16), ([8,12,13], -16), ([9,12,13], -16), ([10,12,13], -16), ([11,12,13], -16), ([12,12,13], -16), ([12,13,13], -16), ([12,13,14], -16), ([12,13,15], -14), ([12,13,16], -10), ([12,13,17], -2), ([12,13,18], 2), ([12,13,19], 10), ([12,13,20], 18)]
theorem atom0151_data : atom0151 = SparsePolynomial.monoTimes [12,13] 1 base07 := by decide +kernel
theorem eval_atom0151 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0151 = (quadB (outer g) ![2,2,1] * g 12 * g 13) := by
  rw [atom0151_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0151_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (870328967200 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152 : SparsePolynomial.Poly := [([0,12,14], -8), ([1,12,14], -12), ([2,12,14], -16), ([3,12,14], -16), ([4,12,14], -16), ([5,12,14], -16), ([6,12,14], -16), ([7,12,14], -16), ([8,12,14], -16), ([9,12,14], -16), ([10,12,14], -16), ([11,12,14], -16), ([12,12,14], -16), ([12,13,14], -16), ([12,14,14], -16), ([12,14,15], -14), ([12,14,16], -10), ([12,14,17], -2), ([12,14,18], 2), ([12,14,19], 10), ([12,14,20], 18)]
theorem atom0152_data : atom0152 = SparsePolynomial.monoTimes [12,14] 1 base07 := by decide +kernel
theorem eval_atom0152 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0152 = (quadB (outer g) ![2,2,1] * g 12 * g 14) := by
  rw [atom0152_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0152_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35097193600 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153 : SparsePolynomial.Poly := [([0,13,13], -8), ([1,13,13], -12), ([2,13,13], -16), ([3,13,13], -16), ([4,13,13], -16), ([5,13,13], -16), ([6,13,13], -16), ([7,13,13], -16), ([8,13,13], -16), ([9,13,13], -16), ([10,13,13], -16), ([11,13,13], -16), ([12,13,13], -16), ([13,13,13], -16), ([13,13,14], -16), ([13,13,15], -14), ([13,13,16], -10), ([13,13,17], -2), ([13,13,18], 2), ([13,13,19], 10), ([13,13,20], 18)]
theorem atom0153_data : atom0153 = SparsePolynomial.monoTimes [13,13] 1 base07 := by decide +kernel
theorem eval_atom0153 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0153 = (quadB (outer g) ![2,2,1] * g 13 * g 13) := by
  rw [atom0153_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0153_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (776300090400 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154 : SparsePolynomial.Poly := [([0,13,14], -8), ([1,13,14], -12), ([2,13,14], -16), ([3,13,14], -16), ([4,13,14], -16), ([5,13,14], -16), ([6,13,14], -16), ([7,13,14], -16), ([8,13,14], -16), ([9,13,14], -16), ([10,13,14], -16), ([11,13,14], -16), ([12,13,14], -16), ([13,13,14], -16), ([13,14,14], -16), ([13,14,15], -14), ([13,14,16], -10), ([13,14,17], -2), ([13,14,18], 2), ([13,14,19], 10), ([13,14,20], 18)]
theorem atom0154_data : atom0154 = SparsePolynomial.monoTimes [13,14] 1 base07 := by decide +kernel
theorem eval_atom0154 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0154 = (quadB (outer g) ![2,2,1] * g 13 * g 14) := by
  rw [atom0154_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0154_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (853893856800 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155 : SparsePolynomial.Poly := [([0,14,14], -8), ([1,14,14], -12), ([2,14,14], -16), ([3,14,14], -16), ([4,14,14], -16), ([5,14,14], -16), ([6,14,14], -16), ([7,14,14], -16), ([8,14,14], -16), ([9,14,14], -16), ([10,14,14], -16), ([11,14,14], -16), ([12,14,14], -16), ([13,14,14], -16), ([14,14,14], -16), ([14,14,15], -14), ([14,14,16], -10), ([14,14,17], -2), ([14,14,18], 2), ([14,14,19], 10), ([14,14,20], 18)]
theorem atom0155_data : atom0155 = SparsePolynomial.monoTimes [14,14] 1 base07 := by decide +kernel
theorem eval_atom0155 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0155 = (quadB (outer g) ![2,2,1] * g 14 * g 14) := by
  rw [atom0155_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0155_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (638836934400 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156 : SparsePolynomial.Poly := [([0,16,16], -8), ([1,16,16], -12), ([2,16,16], -16), ([3,16,16], -16), ([4,16,16], -16), ([5,16,16], -16), ([6,16,16], -16), ([7,16,16], -16), ([8,16,16], -16), ([9,16,16], -16), ([10,16,16], -16), ([11,16,16], -16), ([12,16,16], -16), ([13,16,16], -16), ([14,16,16], -16), ([15,16,16], -14), ([16,16,16], -10), ([16,16,17], -2), ([16,16,18], 2), ([16,16,19], 10), ([16,16,20], 18)]
theorem atom0156_data : atom0156 = SparsePolynomial.monoTimes [16,16] 1 base07 := by decide +kernel
theorem eval_atom0156 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0156 = (quadB (outer g) ![2,2,1] * g 16 * g 16) := by
  rw [atom0156_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0156_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153088911360 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 16 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157 : SparsePolynomial.Poly := [([0,0,15], 1)]
theorem eval_atom0157 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0157 = ((g 0) * (g 0) * (g 15)) := by
  norm_num [atom0157, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0157_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1633334976000 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 0) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158 : SparsePolynomial.Poly := [([0,0,16], 1)]
theorem eval_atom0158 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0158 = ((g 0) * (g 0) * (g 16)) := by
  norm_num [atom0158, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0158_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1206155059200 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 0) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159 : SparsePolynomial.Poly := [([0,0,17], 1)]
theorem eval_atom0159 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0159 = ((g 0) * (g 0) * (g 17)) := by
  norm_num [atom0159, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0159_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (778975142400 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 0) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160 : SparsePolynomial.Poly := [([0,0,18], 1)]
theorem eval_atom0160 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0160 = ((g 0) * (g 0) * (g 18)) := by
  norm_num [atom0160, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0160_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (351795225600 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 0) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161 : SparsePolynomial.Poly := [([0,1,1], 1)]
theorem eval_atom0161 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0161 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0161, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0161_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (331499347200 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162 : SparsePolynomial.Poly := [([0,1,2], 1)]
theorem eval_atom0162 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0162 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0162, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0162_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7169277427200 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163 : SparsePolynomial.Poly := [([0,1,3], 1)]
theorem eval_atom0163 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0163 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0163, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0163_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7123853318400 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164 : SparsePolynomial.Poly := [([0,1,4], 1)]
theorem eval_atom0164 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0164 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0164, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0164_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7078429209600 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165 : SparsePolynomial.Poly := [([0,1,5], 1)]
theorem eval_atom0165 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0165 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0165, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0165_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7778694082176 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0166 : SparsePolynomial.Poly := [([0,1,6], 1)]
theorem eval_atom0166 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0166 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0166, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0166_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7959932467200 : Int) atom0166) := by
  rw [SparsePolynomial.eval_scale, eval_atom0166]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0167 : SparsePolynomial.Poly := [([0,1,7], 1)]
theorem eval_atom0167 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0167 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0167, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0167_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8641406521152 : Int) atom0167) := by
  rw [SparsePolynomial.eval_scale, eval_atom0167]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0168 : SparsePolynomial.Poly := [([0,1,8], 1)]
theorem eval_atom0168 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0168 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0168, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0168_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8847070041600 : Int) atom0168) := by
  rw [SparsePolynomial.eval_scale, eval_atom0168]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0169 : SparsePolynomial.Poly := [([0,1,9], 1)]
theorem eval_atom0169 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0169 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0169, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0169_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9015235891200 : Int) atom0169) := by
  rw [SparsePolynomial.eval_scale, eval_atom0169]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0170 : SparsePolynomial.Poly := [([0,1,10], 1)]
theorem eval_atom0170 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0170 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0170, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0170_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9183401740800 : Int) atom0170) := by
  rw [SparsePolynomial.eval_scale, eval_atom0170]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0171 : SparsePolynomial.Poly := [([0,1,11], 1)]
theorem eval_atom0171 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0171 = ((g 0) * (g 1) * (g 11)) := by
  norm_num [atom0171, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0171_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9195605798400 : Int) atom0171) := by
  rw [SparsePolynomial.eval_scale, eval_atom0171]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0172 : SparsePolynomial.Poly := [([0,1,12], 1)]
theorem eval_atom0172 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0172 = ((g 0) * (g 1) * (g 12)) := by
  norm_num [atom0172, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0172_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8183033286400 : Int) atom0172) := by
  rw [SparsePolynomial.eval_scale, eval_atom0172]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0173 : SparsePolynomial.Poly := [([0,1,13], 1)]
theorem eval_atom0173 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0173 = ((g 0) * (g 1) * (g 13)) := by
  norm_num [atom0173, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0173_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8042000198400 : Int) atom0173) := by
  rw [SparsePolynomial.eval_scale, eval_atom0173]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0174 : SparsePolynomial.Poly := [([0,1,14], 1)]
theorem eval_atom0174 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0174 = ((g 0) * (g 1) * (g 14)) := by
  norm_num [atom0174, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0174_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8339673081600 : Int) atom0174) := by
  rw [SparsePolynomial.eval_scale, eval_atom0174]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0175 : SparsePolynomial.Poly := [([0,1,15], 1)]
theorem eval_atom0175 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0175 = ((g 0) * (g 1) * (g 15)) := by
  norm_num [atom0175, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0175_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13063297161600 : Int) atom0175) := by
  rw [SparsePolynomial.eval_scale, eval_atom0175]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block003 : SparsePolynomial.Poly := [([0,0,1], -910415116800), ([0,0,2], -1337595033600), ([0,0,3], -1764774950400), ([0,0,4], -2191954867200), ([0,0,5], -1127756821248), ([0,0,6], -1101611750400), ([0,0,7], -74995341696), ([0,0,11], -311923584000), ([0,0,12], -2673400307200), ([0,0,13], -3291798182400), ([0,0,14], -3032784115200), ([0,0,15], 1633334976000), ([0,0,16], 1206155059200), ([0,0,17], 778975142400), ([0,0,18], 351795225600), ([0,0,19], -1041855091200), ([0,1,1], -2248010150400), ([0,1,2], 3342054643200), ([0,1,3], 2655860659200), ([0,1,4], 1969666675200), ([0,1,5], 4266228616704), ([0,1,6], 4486684608000), ([0,1,7], 6708083275008), ([0,1,8], 7026239808000), ([0,1,9], 7194405657600), ([0,1,10], 7362571507200), ([0,1,11], 6906890188800), ([0,1,12], 2352102592000), ([0,1,13], 1283472691200), ([0,1,14], 1969666675200), ([0,1,15], 11470070707200), ([0,1,16], -1138018896000), ([0,1,17], -227603779200), ([0,1,18], 227603779200), ([0,1,19], -424763740800), ([0,1,20], 774948182400), ([0,2,2], -2675190067200), ([0,2,3], -6204739968000), ([0,2,4], -7059099801600), ([0,2,5], -4930703709696), ([0,2,6], -4878413568000), ([0,2,7], -2825180750592), ([0,2,8], -2675190067200), ([0,2,9], -2675190067200), ([0,2,10], -2675190067200), ([0,2,11], -3299037235200), ([0,2,12], -8021990681600), ([0,2,13], -9258786432000), ([0,2,14], -8740758297600), ([0,2,15], -2340791308800), ([0,2,16], -1671993792000), ([0,2,17], -334398758400), ([0,2,18], 334398758400), ([0,2,19], -411716390400), ([0,2,20], 1503827942400), ([0,3,3], -3529549900800), ([0,3,4], -7913459635200), ([0,3,5], -5785063543296), ([0,3,6], -5732773401600), ([0,3,7], -3679540584192), ([0,3,8], -3529549900800), ([0,3,9], -3529549900800), ([0,3,10], -3529549900800), ([0,3,11], -4153397068800), ([0,3,12], -8876350515200), ([0,3,13], -10113146265600), ([0,3,14], -9595118131200), ([0,3,15], -3088356163200), ([0,3,16], -2205968688000), ([0,3,17], -441193737600), ([0,3,18], 441193737600), ([0,3,19], 122258505600), ([0,3,20], 3970743638400), ([0,4,4], -4641787684800), ([0,4,5], -6639423376896), ([0,4,6], -6587133235200), ([0,4,7], -4533900417792), ([0,4,8], -4383909734400), ([0,4,9], -4383909734400), ([0,4,10], -4383909734400), ([0,4,11], -5007756902400), ([0,4,12], -9730710348800), ([0,4,13], -10967506099200), ([0,4,14], -10449477964800), ([0,4,15], -3835921017600), ([0,4,16], -2739943584000), ([0,4,17], -547988716800), ([0,4,18], 547988716800), ([0,4,19], 656233401600), ([0,4,20], 4931898451200), ([0,5,5], -2803376434176), ([0,5,6], -4737188565504), ([0,5,7], -2405504325888), ([0,5,8], -2255513642496), ([0,5,9], -2255513642496), ([0,5,10], -2255513642496), ([0,5,11], -2879360810496), ([0,5,12], -7602314256896), ([0,5,13], -8839110007296), ([0,5,14], -8321081872896), ([0,5,15], -1973574437184), ([0,5,16], -1409696026560), ([0,5,17], -281939205312), ([0,5,18], 281939205312), ([0,5,19], -674014155840), ([0,5,20], 2537452847808), ([0,6,6], -2203223500800), ([0,6,7], -4582289975040), ([0,6,8], -2203223500800), ([0,6,9], -2203223500800), ([0,6,10], -2203223500800), ([0,6,11], -2827070668800), ([0,6,12], -7550024115200), ([0,6,13], -8786819865600), ([0,6,14], -8268791731200), ([0,6,15], -1927820563200), ([0,6,16], -1377014688000), ([0,6,17], -275402937600), ([0,6,18], 275402937600), ([0,6,19], -706695494400), ([0,6,20], 2478626438400), ([0,7,7], -2003689370880), ([0,7,8], -2832943348800), ([0,7,9], -149990683392), ([0,7,10], -149990683392), ([0,7,11], -773837851392), ([0,7,12], -5496791297792), ([0,7,13], -6733587048192), ([0,7,14], -6215558913792), ([0,7,15], -131241847968), ([0,7,16], -93744177120), ([0,7,17], -18748835424), ([0,7,18], 18748835424), ([0,7,19], -1989966005280), ([0,7,20], 168739518816), ([0,8,8], -3047473951200), ([0,8,9], -3906457248960), ([0,8,11], -623847168000), ([0,8,12], -5346800614400), ([0,8,13], -6583596364800), ([0,8,14], -6065568230400), ([0,8,19], -2083710182400), ([0,9,9], -5579594697600), ([0,9,10], -4890082498560), ([0,9,11], -623847168000), ([0,9,12], -5346800614400), ([0,9,13], -6583596364800), ([0,9,14], -6065568230400), ([0,9,19], -2083710182400), ([0,9,20], -5006226065400), ([0,10,10], -5938155216000), ([0,10,11], -7814779217280), ([0,10,12], -9060566932480), ([0,10,13], -9163508558400), ([0,10,14], -7336396267200), ([0,10,16], -966903298200), ([0,10,18], -918640182600), ([0,10,19], -7857937924200), ([0,10,20], -3990163653000), ([0,11,11], -6834423859200), ([0,11,12], -13871040695680), ([0,11,13], -10493784000000), ([0,11,14], -8311010601600), ([0,11,15], -545866272000), ([0,11,16], -1047331756800), ([0,11,17], -77980896000), ([0,11,18], 77980896000), ([0,11,19], -6319465689600), ([0,11,20], -1852212096000), ([0,12,12], -12101211673600), ([0,12,13], -20216234080000), ([0,12,14], -14294831017600), ([0,12,15], -4678450537600), ([0,12,16], -4426219660800), ([0,12,17], -668350076800), ([0,12,18], 668350076800), ([0,12,19], -1974302153600), ([0,12,20], 5116172140800), ([0,13,13], -12793997088000), ([0,13,14], -19480315449600), ([0,13,15], -5960404170000), ([0,13,16], -4891229031600), ([0,13,17], -822949545600), ([0,13,18], 822949545600), ([0,13,19], 861530698800), ([0,13,20], 7406545910400), ([0,14,14], -11176263705600), ([0,14,15], -5349896899200), ([0,14,16], -3790980144000), ([0,14,17], -758196028800), ([0,14,18], 758196028800), ([0,14,19], 1707269961600), ([0,14,20], 6823764259200), ([0,15,19], -1823246409600), ([0,16,16], -1224711290880), ([0,16,19], -1302318864000), ([0,17,19], -260463772800), ([0,18,19], 260463772800), ([0,19,19], 1302318864000), ([0,19,20], 2344173955200), ([1,1,1], -1820830233600), ([1,1,2], -2427773644800), ([1,1,3], -2427773644800), ([1,1,4], -2427773644800), ([1,1,5], -2427773644800), ([1,1,6], -2427773644800), ([1,1,7], -2427773644800), ([1,1,8], -2427773644800), ([1,1,9], -2427773644800), ([1,1,10], -2427773644800), ([1,1,11], -2427773644800), ([1,1,12], -2427773644800), ([1,1,13], -2427773644800), ([1,1,14], -2427773644800), ([1,1,15], -2124301939200), ([1,1,16], -1517358528000), ([1,1,17], -303471705600), ([1,1,18], 303471705600), ([1,1,19], 1517358528000), ([1,1,20], 821016604800), ([1,2,20], -4805612985600), ([1,3,20], -2546971660800), ([1,4,4], -386816925600), ([1,4,20], -2546971660800), ([1,5,5], -821794187520), ([1,5,6], -417677133312), ([1,5,20], -2546971660800), ([1,6,7], -3343613686272), ([1,6,20], -2546971660800), ([1,7,7], -2780548031232), ([1,7,8], -4024428998112), ([1,7,20], -2546971660800), ([1,8,8], -4571210926800), ([1,8,9], -5859685873440), ([1,8,20], -2546971660800), ([1,9,9], -8369392046400), ([1,9,10], -7335123747840), ([1,9,20], -12559423791600), ([1,10,10], -8907232824000), ([1,10,11], -11621331852480), ([1,10,12], -7383409682880), ([1,10,13], -5159824387200), ([1,10,14], -2541656073600), ([1,10,16], -1933806596400), ([1,10,18], -1837280365200), ([1,10,19], -11548455483600), ([1,10,20], -10527298966800), ([1,11,11], -9315865036800), ([1,11,12], -12632125658880), ([1,11,13], -6572680934400), ([1,11,14], -3243190406400), ([1,11,16], -1314854553600), ([1,11,19], -9251319974400), ([1,11,20], -7655051980800), ([1,12,12], -10131616588800), ([1,12,13], -13090358332800), ([1,12,14], -5624535571200), ([1,12,16], -2168938553600), ([1,12,19], -6464684710400), ([1,12,20], -4344928761600), ([1,13,13], -9315601084800), ([1,13,14], -10246726281600), ([1,13,15], -399514701600), ([1,13,16], -1552962607200), ([1,13,19], -2339013693600), ([1,13,20], -2546971660800), ([1,14,14], -7666043212800), ([1,14,15], -85049395200), ([1,14,20], -2546971660800), ([1,15,20], -2228600203200), ([1,16,16], -1837066936320), ([1,16,20], -1591857288000), ([1,17,20], -318371457600), ([1,18,20], 318371457600), ([1,19,20], 1591857288000), ([1,20,20], 2865343118400), ([2,2,20], -3011521766400), ([2,3,20], -3011521766400), ([2,4,4], -515755900800), ([2,4,20], -3011521766400), ([2,5,5], -1095725583360), ([2,5,6], -556902844416), ([2,5,20], -3011521766400), ([2,6,7], -4458151581696), ([2,6,20], -3011521766400), ([2,7,7], -3707397374976), ([2,7,8], -5365905330816), ([2,7,20], -3011521766400), ([2,8,8], -6094947902400), ([2,8,9], -7812914497920), ([2,8,20], -3011521766400), ([2,9,9], -11159189395200), ([2,9,10], -9780164997120), ([2,9,20], -23036426028000), ([2,10,10], -11876310432000), ([2,10,11], -17721599212800), ([2,10,12], -14678573459200), ([2,10,13], -10319648774400), ([2,10,14], -5083312147200), ([2,10,16], -3867613192800), ([2,10,18], -3674560730400), ([2,10,19], -23096910967200), ([2,10,20], -18972176378400), ([2,11,11], -12421153382400), ([2,11,12], -18926930982400), ([2,11,13], -13145361868800), ([2,11,14], -6486380812800), ([2,11,16], -2629709107200), ([2,11,19], -18502639948800), ([2,11,20], -13227682406400), ([2,12,12], -13508822118400), ([2,12,13], -19218084928000), ([2,12,14], -10968293593600), ([2,12,16], -4337877107200), ([2,12,19], -12929369420800), ([2,12,20], -6607435968000), ([2,13,13], -12420801446400), ([2,13,14], -13662301708800), ([2,13,15], -799029403200), ([2,13,16], -3105925214400), ([2,13,19], -4678027387200), ([2,13,20], -3011521766400), ([2,14,14], -10221390950400), ([2,14,15], -170098790400), ([2,14,20], -3011521766400), ([2,15,20], -2635081545600), ([2,16,16], -2449422581760), ([2,16,20], -1882201104000), ([2,17,20], -376440220800), ([2,18,20], 376440220800), ([2,19,20], 1882201104000), ([2,20,20], 3387961987200), ([3,4,4], -515755900800), ([3,5,5], -1095725583360), ([3,5,6], -556902844416), ([3,6,7], -4458151581696), ([3,7,7], -3707397374976), ([3,7,8], -5365905330816), ([3,8,8], -6094947902400), ([3,8,9], -7812914497920), ([3,9,9], -11159189395200), ([3,9,10], -9780164997120), ([3,9,20], -20024904261600), ([3,10,10], -11876310432000), ([3,10,11], -17721599212800), ([3,10,12], -14678573459200), ([3,10,13], -10319648774400), ([3,10,14], -5083312147200), ([3,10,16], -3867613192800), ([3,10,18], -3674560730400), ([3,10,19], -23096910967200), ([3,10,20], -15960654612000), ([3,11,11], -12421153382400), ([3,11,12], -18926930982400), ([3,11,13], -13145361868800), ([3,11,14], -6486380812800), ([3,11,16], -2629709107200), ([3,11,19], -18502639948800), ([3,11,20], -10216160640000), ([3,12,12], -13508822118400), ([3,12,13], -19218084928000), ([3,12,14], -10968293593600), ([3,12,16], -4337877107200), ([3,12,19], -12929369420800), ([3,12,20], -3595914201600), ([3,13,13], -12420801446400), ([3,13,14], -13662301708800), ([3,13,15], -799029403200), ([3,13,16], -3105925214400), ([3,13,19], -4678027387200), ([3,14,14], -10221390950400), ([3,14,15], -170098790400), ([3,16,16], -2449422581760), ([4,4,4], -515755900800), ([4,4,5], -515755900800), ([4,4,6], -515755900800), ([4,4,7], -515755900800), ([4,4,8], -515755900800), ([4,4,9], -515755900800), ([4,4,10], -515755900800), ([4,4,11], -515755900800), ([4,4,12], -515755900800), ([4,4,13], -515755900800), ([4,4,14], -515755900800), ([4,4,15], -451286413200), ([4,4,16], -322347438000), ([4,4,17], -64469487600), ([4,4,18], 64469487600), ([4,4,19], 322347438000), ([4,4,20], 580225388400), ([4,5,5], -1095725583360), ([4,5,6], -556902844416), ([4,6,7], -4458151581696), ([4,7,7], -3707397374976), ([4,7,8], -5365905330816), ([4,8,8], -6094947902400), ([4,8,9], -7812914497920), ([4,9,9], -11159189395200), ([4,9,10], -9780164997120), ([4,9,20], -20024904261600), ([4,10,10], -11876310432000), ([4,10,11], -17721599212800), ([4,10,12], -14678573459200), ([4,10,13], -10319648774400), ([4,10,14], -5083312147200), ([4,10,16], -3867613192800), ([4,10,18], -3674560730400), ([4,10,19], -23096910967200), ([4,10,20], -15960654612000), ([4,11,11], -12421153382400), ([4,11,12], -18926930982400), ([4,11,13], -13145361868800), ([4,11,14], -6486380812800), ([4,11,16], -2629709107200), ([4,11,19], -18502639948800), ([4,11,20], -10216160640000), ([4,12,12], -13508822118400), ([4,12,13], -19218084928000), ([4,12,14], -10968293593600), ([4,12,16], -4337877107200), ([4,12,19], -12929369420800), ([4,12,20], -3595914201600), ([4,13,13], -12420801446400), ([4,13,14], -13662301708800), ([4,13,15], -799029403200), ([4,13,16], -3105925214400), ([4,13,19], -4678027387200), ([4,14,14], -10221390950400), ([4,14,15], -170098790400), ([4,16,16], -2449422581760), ([5,5,5], -1095725583360), ([5,5,6], -1652628427776), ([5,5,7], -1095725583360), ([5,5,8], -1095725583360), ([5,5,9], -1095725583360), ([5,5,10], -1095725583360), ([5,5,11], -1095725583360), ([5,5,12], -1095725583360), ([5,5,13], -1095725583360), ([5,5,14], -1095725583360), ([5,5,15], -958759885440), ([5,5,16], -684828489600), ([5,5,17], -136965697920), ([5,5,18], 136965697920), ([5,5,19], 684828489600), ([5,5,20], 1232691281280), ([5,6,6], -556902844416), ([5,6,7], -5015054426112), ([5,6,8], -556902844416), ([5,6,9], -556902844416), ([5,6,10], -556902844416), ([5,6,11], -556902844416), ([5,6,12], -556902844416), ([5,6,13], -556902844416), ([5,6,14], -556902844416), ([5,6,15], -487289988864), ([5,6,16], -348064277760), ([5,6,17], -69612855552), ([5,6,18], 69612855552), ([5,6,19], 348064277760), ([5,6,20], 626515699968), ([5,7,7], -3707397374976), ([5,7,8], -5365905330816), ([5,8,8], -6094947902400), ([5,8,9], -7812914497920), ([5,9,9], -11159189395200), ([5,9,10], -9780164997120), ([5,9,20], -20024904261600), ([5,10,10], -11876310432000), ([5,10,11], -17721599212800), ([5,10,12], -14678573459200), ([5,10,13], -10319648774400), ([5,10,14], -5083312147200), ([5,10,16], -3867613192800), ([5,10,18], -3674560730400), ([5,10,19], -23096910967200), ([5,10,20], -15960654612000), ([5,11,11], -12421153382400), ([5,11,12], -18926930982400), ([5,11,13], -13145361868800), ([5,11,14], -6486380812800), ([5,11,16], -2629709107200), ([5,11,19], -18502639948800), ([5,11,20], -10216160640000), ([5,12,12], -13508822118400), ([5,12,13], -19218084928000), ([5,12,14], -10968293593600), ([5,12,16], -4337877107200), ([5,12,19], -12929369420800), ([5,12,20], -3595914201600), ([5,13,13], -12420801446400), ([5,13,14], -13662301708800), ([5,13,15], -799029403200), ([5,13,16], -3105925214400), ([5,13,19], -4678027387200), ([5,14,14], -10221390950400), ([5,14,15], -170098790400), ([5,16,16], -2449422581760), ([6,6,7], -4458151581696), ([6,7,7], -8165548956672), ([6,7,8], -9824056912512), ([6,7,9], -4458151581696), ([6,7,10], -4458151581696), ([6,7,11], -4458151581696), ([6,7,12], -4458151581696), ([6,7,13], -4458151581696), ([6,7,14], -4458151581696), ([6,7,15], -3900882633984), ([6,7,16], -2786344738560), ([6,7,17], -557268947712), ([6,7,18], 557268947712), ([6,7,19], 2786344738560), ([6,7,20], 5015420529408), ([6,8,8], -6094947902400), ([6,8,9], -7812914497920), ([6,9,9], -11159189395200), ([6,9,10], -9780164997120), ([6,9,20], -20024904261600), ([6,10,10], -11876310432000), ([6,10,11], -17721599212800), ([6,10,12], -14678573459200), ([6,10,13], -10319648774400), ([6,10,14], -5083312147200), ([6,10,16], -3867613192800), ([6,10,18], -3674560730400), ([6,10,19], -23096910967200), ([6,10,20], -15960654612000), ([6,11,11], -12421153382400), ([6,11,12], -18926930982400), ([6,11,13], -13145361868800), ([6,11,14], -6486380812800), ([6,11,16], -2629709107200), ([6,11,19], -18502639948800), ([6,11,20], -10216160640000), ([6,12,12], -13508822118400), ([6,12,13], -19218084928000), ([6,12,14], -10968293593600), ([6,12,16], -4337877107200), ([6,12,19], -12929369420800), ([6,12,20], -3595914201600), ([6,13,13], -12420801446400), ([6,13,14], -13662301708800), ([6,13,15], -799029403200), ([6,13,16], -3105925214400), ([6,13,19], -4678027387200), ([6,14,14], -10221390950400), ([6,14,15], -170098790400), ([6,16,16], -2449422581760), ([7,7,7], -3707397374976), ([7,7,8], -9073302705792), ([7,7,9], -3707397374976), ([7,7,10], -3707397374976), ([7,7,11], -3707397374976), ([7,7,12], -3707397374976), ([7,7,13], -3707397374976), ([7,7,14], -3707397374976), ([7,7,15], -3243972703104), ([7,7,16], -2317123359360), ([7,7,17], -463424671872), ([7,7,18], 463424671872), ([7,7,19], 2317123359360), ([7,7,20], 4170822046848), ([7,8,8], -11460853233216), ([7,8,9], -13178819828736), ([7,8,10], -5365905330816), ([7,8,11], -5365905330816), ([7,8,12], -5365905330816), ([7,8,13], -5365905330816), ([7,8,14], -5365905330816), ([7,8,15], -4695167164464), ([7,8,16], -3353690831760), ([7,8,17], -670738166352), ([7,8,18], 670738166352), ([7,8,19], 3353690831760), ([7,8,20], 6036643497168), ([7,9,9], -11159189395200), ([7,9,10], -9780164997120), ([7,9,20], -20024904261600), ([7,10,10], -11876310432000), ([7,10,11], -17721599212800), ([7,10,12], -14678573459200), ([7,10,13], -10319648774400), ([7,10,14], -5083312147200), ([7,10,16], -3867613192800), ([7,10,18], -3674560730400), ([7,10,19], -23096910967200), ([7,10,20], -15960654612000), ([7,11,11], -12421153382400), ([7,11,12], -18926930982400), ([7,11,13], -13145361868800), ([7,11,14], -6486380812800), ([7,11,16], -2629709107200), ([7,11,19], -18502639948800), ([7,11,20], -10216160640000), ([7,12,12], -13508822118400), ([7,12,13], -19218084928000), ([7,12,14], -10968293593600), ([7,12,16], -4337877107200), ([7,12,19], -12929369420800), ([7,12,20], -3595914201600), ([7,13,13], -12420801446400), ([7,13,14], -13662301708800), ([7,13,15], -799029403200), ([7,13,16], -3105925214400), ([7,13,19], -4678027387200), ([7,14,14], -10221390950400), ([7,14,15], -170098790400), ([7,16,16], -2449422581760), ([8,8,8], -6094947902400), ([8,8,9], -13907862400320), ([8,8,10], -6094947902400), ([8,8,11], -6094947902400), ([8,8,12], -6094947902400), ([8,8,13], -6094947902400), ([8,8,14], -6094947902400), ([8,8,15], -5333079414600), ([8,8,16], -3809342439000), ([8,8,17], -761868487800), ([8,8,18], 761868487800), ([8,8,19], 3809342439000), ([8,8,20], 6856816390200), ([8,9,9], -18972103893120), ([8,9,10], -17593079495040), ([8,9,11], -7812914497920), ([8,9,12], -7812914497920), ([8,9,13], -7812914497920), ([8,9,14], -7812914497920), ([8,9,15], -6836300185680), ([8,9,16], -4883071561200), ([8,9,17], -976614312240), ([8,9,18], 976614312240), ([8,9,19], 4883071561200), ([8,9,20], -11235375451440), ([8,10,10], -11876310432000), ([8,10,11], -17721599212800), ([8,10,12], -14678573459200), ([8,10,13], -10319648774400), ([8,10,14], -5083312147200), ([8,10,16], -3867613192800), ([8,10,18], -3674560730400), ([8,10,19], -23096910967200), ([8,10,20], -15960654612000), ([8,11,11], -12421153382400), ([8,11,12], -18926930982400), ([8,11,13], -13145361868800), ([8,11,14], -6486380812800), ([8,11,16], -2629709107200), ([8,11,19], -18502639948800), ([8,11,20], -10216160640000), ([8,12,12], -13508822118400), ([8,12,13], -19218084928000), ([8,12,14], -10968293593600), ([8,12,16], -4337877107200), ([8,12,19], -12929369420800), ([8,12,20], -3595914201600), ([8,13,13], -12420801446400), ([8,13,14], -13662301708800), ([8,13,15], -799029403200), ([8,13,16], -3105925214400), ([8,13,19], -4678027387200), ([8,14,14], -10221390950400), ([8,14,15], -170098790400), ([8,16,16], -2449422581760), ([9,9,9], -11159189395200), ([9,9,10], -20939354392320), ([9,9,11], -11159189395200), ([9,9,12], -11159189395200), ([9,9,13], -11159189395200), ([9,9,14], -11159189395200), ([9,9,15], -9764290720800), ([9,9,16], -6974493372000), ([9,9,17], -1394898674400), ([9,9,18], 1394898674400), ([9,9,19], 6974493372000), ([9,9,20], -7470816192000), ([9,10,10], -21656475429120), ([9,10,11], -27501764209920), ([9,10,12], -24458738456320), ([9,10,13], -20099813771520), ([9,10,14], -14863477144320), ([9,10,15], -8557644372480), ([9,10,16], -9980216316000), ([9,10,17], -1222520624640), ([9,10,18], -2452040105760), ([9,10,19], -16984307844000), ([9,10,20], -24982873251840), ([9,11,11], -12421153382400), ([9,11,12], -18926930982400), ([9,11,13], -13145361868800), ([9,11,14], -6486380812800), ([9,11,16], -2629709107200), ([9,11,19], -18502639948800), ([9,11,20], -30241064901600), ([9,12,12], -13508822118400), ([9,12,13], -19218084928000), ([9,12,14], -10968293593600), ([9,12,16], -4337877107200), ([9,12,19], -12929369420800), ([9,12,20], -23620818463200), ([9,13,13], -12420801446400), ([9,13,14], -13662301708800), ([9,13,15], -799029403200), ([9,13,16], -3105925214400), ([9,13,19], -4678027387200), ([9,13,20], -20024904261600), ([9,14,14], -10221390950400), ([9,14,15], -170098790400), ([9,14,20], -20024904261600), ([9,15,20], -10012452130800), ([9,16,16], -2449422581760), ([9,17,20], 10012452130800), ([9,18,20], 15018678196200), ([9,19,20], 20024904261600), ([9,20,20], 22528017294300), ([10,10,10], -11876310432000), ([10,10,11], -29597909644800), ([10,10,12], -26554883891200), ([10,10,13], -22195959206400), ([10,10,14], -16959622579200), ([10,10,15], -10391771628000), ([10,10,16], -11290307212800), ([10,10,17], -1484538804000), ([10,10,18], -2190021926400), ([10,10,19], -15674216947200), ([10,10,20], -2599805376000), ([10,11,11], -30142752595200), ([10,11,12], -51327103654400), ([10,11,13], -41186609856000), ([10,11,14], -29291292172800), ([10,11,15], -13001597975520), ([10,11,16], -13398652915200), ([10,11,17], 1959468991200), ([10,11,18], 2715308064000), ([10,11,19], -28018750072320), ([10,11,20], -6240016137600), ([10,12,12], -28187395577600), ([10,12,13], -44216307161600), ([10,12,14], -30730179200000), ([10,12,15], -7405471159520), ([10,12,16], -8315797683200), ([10,12,17], 7228979346400), ([10,12,18], 7224061980800), ([10,12,19], -21413891358720), ([10,12,20], -3043173672000), ([10,13,13], -22740450220800), ([10,13,14], -29065262630400), ([10,13,15], -5958853790400), ([10,13,16], -6973538407200), ([10,13,17], 5159824387200), ([10,13,18], 4065175850400), ([10,13,19], -17455289580000), ([10,13,20], -4351049740800), ([10,14,14], -15304703097600), ([10,14,15], -2711754864000), ([10,14,16], -3867613192800), ([10,14,17], 2541656073600), ([10,14,18], 137923380000), ([10,14,19], -18013598820000), ([10,14,20], -10241928446400), ([10,15,16], -1933806596400), ([10,15,18], -1837280365200), ([10,15,19], -11548455483600), ([10,15,20], -7980327306000), ([10,16,16], -2449422581760), ([10,16,17], 1933806596400), ([10,16,18], 2900709894600), ([10,16,19], 3867613192800), ([10,16,20], 4351064841900), ([10,17,18], 1837280365200), ([10,17,19], 11548455483600), ([10,17,20], 7980327306000), ([10,18,18], 2755920547800), ([10,18,19], 20997243955800), ([10,18,20], 16104371780700), ([10,19,19], 23096910967200), ([10,19,20], 41944679450100), ([10,20,20], 17955736438500), ([11,11,11], -12421153382400), ([11,11,12], -31348084364800), ([11,11,13], -25566515251200), ([11,11,14], -18907534195200), ([11,11,15], -10868509209600), ([11,11,16], -10392929971200), ([11,11,17], -1552644172800), ([11,11,18], 1552644172800), ([11,11,19], -10739419084800), ([11,11,20], 3757636915200), ([11,12,12], -32435753100800), ([11,12,13], -51290377779200), ([11,12,14], -36381605388800), ([11,12,15], -14216455742720), ([11,12,16], -14889236633600), ([11,12,17], 1541815072000), ([11,12,18], 6273547817600), ([11,12,19], -17258068638720), ([11,12,20], 7480722513600), ([11,13,13], -25566163315200), ([11,13,14], -33294044390400), ([11,13,15], -7371710337600), ([11,13,16], -5735634321600), ([11,13,17], 6572680934400), ([11,13,18], 9859021401600), ([11,13,19], -10035305467200), ([11,13,20], 4572371462400), ([11,14,14], -16707771763200), ([11,14,15], -3413289196800), ([11,14,16], -2629709107200), ([11,14,17], 3243190406400), ([11,14,18], 4864785609600), ([11,14,19], -12016259136000), ([11,14,20], -2918982225600), ([11,15,16], -1314854553600), ([11,15,19], -9251319974400), ([11,15,20], -5108080320000), ([11,16,16], -2449422581760), ([11,16,17], 1314854553600), ([11,16,18], 1972281830400), ([11,16,19], 2629709107200), ([11,16,20], 2958422745600), ([11,17,19], 9251319974400), ([11,17,20], 5108080320000), ([11,18,19], 13876979961600), ([11,18,20], 7662120480000), ([11,19,19], 18502639948800), ([11,19,20], 31031630582400), ([11,20,20], 11493180720000), ([12,12,12], -13508822118400), ([12,12,13], -32726907046400), ([12,12,14], -24477115712000), ([12,12,15], -11820219353600), ([12,12,16], -12780890931200), ([12,12,17], -1688602764800), ([12,12,18], 1688602764800), ([12,12,19], -4486355596800), ([12,12,20], 11601510681600), ([12,13,13], -31638886374400), ([12,13,14], -43848680230400), ([12,13,15], -15630045670400), ([12,13,16], -16147091993600), ([12,13,17], 905752792000), ([12,13,18], 5710274024000), ([12,13,19], -3611285683200), ([12,13,20], 18024431342400), ([12,14,14], -21189684544000), ([12,14,15], -5864828748800), ([12,14,16], -4688849043200), ([12,14,17], 5133174860800), ([12,14,18], 7875248259200), ([12,14,19], -2171658988800), ([12,14,20], 8743416091200), ([12,15,16], -2168938553600), ([12,15,19], -6464684710400), ([12,15,20], -1797957100800), ([12,16,16], -2449422581760), ([12,16,17], 2168938553600), ([12,16,18], 3253407830400), ([12,16,19], 4337877107200), ([12,16,20], 4880111745600), ([12,17,19], 6464684710400), ([12,17,20], 1797957100800), ([12,18,19], 9697027065600), ([12,18,20], 2696935651200), ([12,19,19], 12929369420800), ([12,19,20], 18141454800000), ([12,20,20], 4045403476800), ([13,13,13], -12420801446400), ([13,13,14], -26083103155200), ([13,13,15], -11667230668800), ([13,13,16], -10868926118400), ([13,13,17], -1552600180800), ([13,13,18], 1552600180800), ([13,13,19], 3084973516800), ([13,13,20], 13973401627200), ([13,14,14], -23883692659200), ([13,14,15], -12923642188800), ([13,14,16], -11644863782400), ([13,14,17], -1707787713600), ([13,14,18], 1707787713600), ([13,14,19], 3860911180800), ([13,14,20], 15370089422400), ([13,15,15], -399514701600), ([13,15,16], -1552962607200), ([13,15,17], 399514701600), ([13,15,18], 599272052400), ([13,15,19], -1539984290400), ([13,15,20], 898908078600), ([13,16,16], -2449422581760), ([13,16,17], 1552962607200), ([13,16,18], 2329443910800), ([13,16,19], 3105925214400), ([13,16,20], 3494165866200), ([13,17,19], 2339013693600), ([13,18,19], 3508520540400), ([13,19,19], 4678027387200), ([13,19,20], 5262780810600), ([14,14,14], -10221390950400), ([14,14,15], -9113815872000), ([14,14,16], -6388369344000), ([14,14,17], -1277673868800), ([14,14,18], 1277673868800), ([14,14,19], 6388369344000), ([14,14,20], 11499064819200), ([14,15,15], -85049395200), ([14,15,17], 85049395200), ([14,15,18], 127574092800), ([14,15,19], 170098790400), ([14,15,20], 191361139200), ([14,16,16], -2449422581760), ([15,16,16], -2143244759040), ([16,16,16], -1530889113600), ([16,16,17], -306177822720), ([16,16,18], 306177822720), ([16,16,19], 1530889113600), ([16,16,20], 2755600404480)]
theorem block003_data : block003 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1251556516350 : Int) atom0096) (SparsePolynomial.scale (417466889280 : Int) atom0097)) (SparsePolynomial.merge (SparsePolynomial.scale (906380102880 : Int) atom0098) (SparsePolynomial.merge (SparsePolynomial.scale (644978048400 : Int) atom0099) (SparsePolynomial.scale (317707009200 : Int) atom0100)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (241725824550 : Int) atom0101) (SparsePolynomial.scale (229660045650 : Int) atom0102)) (SparsePolynomial.merge (SparsePolynomial.scale (1443556935450 : Int) atom0103) (SparsePolynomial.merge (SparsePolynomial.scale (997540913250 : Int) atom0104) (SparsePolynomial.scale (390768144480 : Int) atom0105))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (821585116800 : Int) atom0106) (SparsePolynomial.scale (405398800800 : Int) atom0107)) (SparsePolynomial.merge (SparsePolynomial.scale (164356819200 : Int) atom0108) (SparsePolynomial.merge (SparsePolynomial.scale (1156414996800 : Int) atom0109) (SparsePolynomial.scale (638510040000 : Int) atom0110)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (330801340800 : Int) atom0111) (SparsePolynomial.scale (650421156000 : Int) atom0112)) (SparsePolynomial.merge (SparsePolynomial.scale (271117319200 : Int) atom0113) (SparsePolynomial.merge (SparsePolynomial.scale (808085588800 : Int) atom0114) (SparsePolynomial.scale (224744637600 : Int) atom0115)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (49939337700 : Int) atom0116) (SparsePolynomial.scale (194120325900 : Int) atom0117)) (SparsePolynomial.merge (SparsePolynomial.scale (292376711700 : Int) atom0118) (SparsePolynomial.merge (SparsePolynomial.scale (10631174400 : Int) atom0119) (SparsePolynomial.scale (113801889600 : Int) atom0120)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (167199379200 : Int) atom0121) (SparsePolynomial.scale (220596868800 : Int) atom0122)) (SparsePolynomial.merge (SparsePolynomial.scale (273994358400 : Int) atom0123) (SparsePolynomial.merge (SparsePolynomial.scale (140969602656 : Int) atom0124) (SparsePolynomial.scale (137701468800 : Int) atom0125))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9374417712 : Int) atom0126) (SparsePolynomial.scale (38990448000 : Int) atom0127)) (SparsePolynomial.merge (SparsePolynomial.scale (334175038400 : Int) atom0128) (SparsePolynomial.merge (SparsePolynomial.scale (411474772800 : Int) atom0129) (SparsePolynomial.scale (379098014400 : Int) atom0130)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (130231886400 : Int) atom0131) (SparsePolynomial.scale (151735852800 : Int) atom0132)) (SparsePolynomial.merge (SparsePolynomial.scale (159185728800 : Int) atom0133) (SparsePolynomial.merge (SparsePolynomial.scale (188220110400 : Int) atom0134) (SparsePolynomial.scale (32234743800 : Int) atom0135))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (68482848960 : Int) atom0136) (SparsePolynomial.scale (34806427776 : Int) atom0137)) (SparsePolynomial.merge (SparsePolynomial.scale (278634473856 : Int) atom0138) (SparsePolynomial.merge (SparsePolynomial.scale (231712335936 : Int) atom0139) (SparsePolynomial.scale (335369083176 : Int) atom0140)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (380934243900 : Int) atom0141) (SparsePolynomial.scale (488307156120 : Int) atom0142)) (SparsePolynomial.merge (SparsePolynomial.scale (697449337200 : Int) atom0143) (SparsePolynomial.merge (SparsePolynomial.scale (611260312320 : Int) atom0144) (SparsePolynomial.scale (742269402000 : Int) atom0145))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (690133061520 : Int) atom0146) (SparsePolynomial.scale (11030738320 : Int) atom0147)) (SparsePolynomial.merge (SparsePolynomial.scale (776322086400 : Int) atom0148) (SparsePolynomial.merge (SparsePolynomial.scale (792165041920 : Int) atom0149) (SparsePolynomial.scale (844301382400 : Int) atom0150)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (870328967200 : Int) atom0151) (SparsePolynomial.scale (35097193600 : Int) atom0152)) (SparsePolynomial.merge (SparsePolynomial.scale (776300090400 : Int) atom0153) (SparsePolynomial.merge (SparsePolynomial.scale (853893856800 : Int) atom0154) (SparsePolynomial.scale (638836934400 : Int) atom0155)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (153088911360 : Int) atom0156) (SparsePolynomial.scale (1633334976000 : Int) atom0157)) (SparsePolynomial.merge (SparsePolynomial.scale (1206155059200 : Int) atom0158) (SparsePolynomial.merge (SparsePolynomial.scale (778975142400 : Int) atom0159) (SparsePolynomial.scale (351795225600 : Int) atom0160)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (331499347200 : Int) atom0161) (SparsePolynomial.scale (7169277427200 : Int) atom0162)) (SparsePolynomial.merge (SparsePolynomial.scale (7123853318400 : Int) atom0163) (SparsePolynomial.merge (SparsePolynomial.scale (7078429209600 : Int) atom0164) (SparsePolynomial.scale (7778694082176 : Int) atom0165))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7959932467200 : Int) atom0166) (SparsePolynomial.scale (8641406521152 : Int) atom0167)) (SparsePolynomial.merge (SparsePolynomial.scale (8847070041600 : Int) atom0168) (SparsePolynomial.merge (SparsePolynomial.scale (9015235891200 : Int) atom0169) (SparsePolynomial.scale (9183401740800 : Int) atom0170)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9195605798400 : Int) atom0171) (SparsePolynomial.scale (8183033286400 : Int) atom0172)) (SparsePolynomial.merge (SparsePolynomial.scale (8042000198400 : Int) atom0173) (SparsePolynomial.merge (SparsePolynomial.scale (8339673081600 : Int) atom0174) (SparsePolynomial.scale (13063297161600 : Int) atom0175)))))))) := by decide +kernel
theorem block003_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block003 := by
  rw [block003_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0096_nonneg g hg hA hB) (atom0097_nonneg g hg hA hB)) (add_nonneg (atom0098_nonneg g hg hA hB) (add_nonneg (atom0099_nonneg g hg hA hB) (atom0100_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0101_nonneg g hg hA hB) (atom0102_nonneg g hg hA hB)) (add_nonneg (atom0103_nonneg g hg hA hB) (add_nonneg (atom0104_nonneg g hg hA hB) (atom0105_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0106_nonneg g hg hA hB) (atom0107_nonneg g hg hA hB)) (add_nonneg (atom0108_nonneg g hg hA hB) (add_nonneg (atom0109_nonneg g hg hA hB) (atom0110_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0111_nonneg g hg hA hB) (atom0112_nonneg g hg hA hB)) (add_nonneg (atom0113_nonneg g hg hA hB) (add_nonneg (atom0114_nonneg g hg hA hB) (atom0115_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0116_nonneg g hg hA hB) (atom0117_nonneg g hg hA hB)) (add_nonneg (atom0118_nonneg g hg hA hB) (add_nonneg (atom0119_nonneg g hg hA hB) (atom0120_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0121_nonneg g hg hA hB) (atom0122_nonneg g hg hA hB)) (add_nonneg (atom0123_nonneg g hg hA hB) (add_nonneg (atom0124_nonneg g hg hA hB) (atom0125_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0126_nonneg g hg hA hB) (atom0127_nonneg g hg hA hB)) (add_nonneg (atom0128_nonneg g hg hA hB) (add_nonneg (atom0129_nonneg g hg hA hB) (atom0130_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0131_nonneg g hg hA hB) (atom0132_nonneg g hg hA hB)) (add_nonneg (atom0133_nonneg g hg hA hB) (add_nonneg (atom0134_nonneg g hg hA hB) (atom0135_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0136_nonneg g hg hA hB) (atom0137_nonneg g hg hA hB)) (add_nonneg (atom0138_nonneg g hg hA hB) (add_nonneg (atom0139_nonneg g hg hA hB) (atom0140_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0141_nonneg g hg hA hB) (atom0142_nonneg g hg hA hB)) (add_nonneg (atom0143_nonneg g hg hA hB) (add_nonneg (atom0144_nonneg g hg hA hB) (atom0145_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0146_nonneg g hg hA hB) (atom0147_nonneg g hg hA hB)) (add_nonneg (atom0148_nonneg g hg hA hB) (add_nonneg (atom0149_nonneg g hg hA hB) (atom0150_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0151_nonneg g hg hA hB) (atom0152_nonneg g hg hA hB)) (add_nonneg (atom0153_nonneg g hg hA hB) (add_nonneg (atom0154_nonneg g hg hA hB) (atom0155_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0156_nonneg g hg hA hB) (atom0157_nonneg g hg hA hB)) (add_nonneg (atom0158_nonneg g hg hA hB) (add_nonneg (atom0159_nonneg g hg hA hB) (atom0160_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0161_nonneg g hg hA hB) (atom0162_nonneg g hg hA hB)) (add_nonneg (atom0163_nonneg g hg hA hB) (add_nonneg (atom0164_nonneg g hg hA hB) (atom0165_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0166_nonneg g hg hA hB) (atom0167_nonneg g hg hA hB)) (add_nonneg (atom0168_nonneg g hg hA hB) (add_nonneg (atom0169_nonneg g hg hA hB) (atom0170_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0171_nonneg g hg hA hB) (atom0172_nonneg g hg hA hB)) (add_nonneg (atom0173_nonneg g hg hA hB) (add_nonneg (atom0174_nonneg g hg hA hB) (atom0175_nonneg g hg hA hB))))))))

end APPT.Finite21
