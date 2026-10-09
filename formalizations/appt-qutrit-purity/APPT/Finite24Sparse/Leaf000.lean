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
def block000 : SparsePolynomial.Poly := [([0,1,19], -16797255552000), ([0,1,21], -1091467238400), ([0,1,22], -3119551680000), ([0,1,23], -5333305824000), ([0,3,22], -13295088979200), ([0,4,4], -8647654982400), ([0,4,22], -33627424790400), ([0,5,5], -17473126809600), ([0,5,22], -48041084448000), ([0,5,23], -40036026038400), ([0,6,6], -33169264128000), ([0,6,7], -21911322935040), ([0,6,22], -62113441824000), ([0,6,23], -50998387910400), ([0,7,7], -42486897868800), ([0,7,8], -29634871136640), ([0,7,9], -1882363965768), ([0,7,22], -64803522694400), ([0,7,23], -51195064636800), ([0,8,8], -56302699622400), ([0,8,9], -48035817409536), ([0,8,10], -11275121719224), ([0,8,22], -65175220051200), ([0,8,23], -48783559910400), ([0,9,9], -65116570945536), ([0,9,10], -66253316861952), ([0,9,22], -55311785191680), ([0,9,23], -36638799898752), ([0,10,10], -60047626991616), ([0,10,11], -38856102062976), ([0,10,22], -27812480743680), ([0,10,23], -8100120966912), ([0,11,11], -41489879333760), ([0,11,22], -152392439040), ([1,1,19], -50391766656000), ([1,1,21], -3274401715200), ([1,1,22], -9419220518400), ([1,1,23], -15999917472000), ([1,2,19], -67189022208000), ([1,2,21], -4365868953600), ([1,2,22], -12599337676800), ([1,2,23], -21333223296000), ([1,3,19], -67189022208000), ([1,3,21], -4365868953600), ([1,3,22], -52484604614400), ([1,3,23], -21333223296000), ([1,4,4], -12971482473600), ([1,4,19], -67189022208000), ([1,4,21], -4365868953600), ([1,4,22], -113481612048000), ([1,4,23], -21333223296000), ([1,5,5], -26209690214400), ([1,5,19], -67189022208000), ([1,5,21], -4365868953600), ([1,5,22], -156722591020800), ([1,5,23], -141441301411200), ([1,6,6], -49753896192000), ([1,6,7], -33533559037440), ([1,6,19], -67189022208000), ([1,6,21], -4365868953600), ([1,6,22], -198939663148800), ([1,6,23], -174328387027200), ([1,7,7], -63730346803200), ([1,7,8], -52313528615040), ([1,7,9], -3764727931536), ([1,7,19], -67189022208000), ([1,7,21], -4365868953600), ([1,7,22], -207009905760000), ([1,7,23], -174918417206400), ([1,8,8], -84454049433600), ([1,8,9], -79290012155904), ([1,8,10], -17037665639280), ([1,8,19], -67189022208000), ([1,8,21], -4365868953600), ([1,8,22], -208124997830400), ([1,8,23], -167683903027200), ([1,9,9], -97674856418304), ([1,9,10], -99379975292928), ([1,9,19], -67189022208000), ([1,9,21], -4365868953600), ([1,9,22], -178534693251840), ([1,9,23], -131249622992256), ([1,10,10], -90071440487424), ([1,10,11], -58284153094464), ([1,10,19], -67189022208000), ([1,10,21], -4365868953600), ([1,10,22], -96036779907840), ([1,10,23], -45633586196736), ([1,11,11], -62234819000640), ([1,11,19], -67189022208000), ([1,11,21], -4365868953600), ([1,11,22], -13056514993920), ([1,11,23], -21333223296000), ([1,12,19], -67189022208000), ([1,12,21], -4365868953600), ([1,12,22], -12599337676800), ([1,12,23], -21333223296000), ([1,13,19], -67189022208000), ([1,13,21], -4365868953600), ([1,13,22], -12599337676800), ([1,13,23], -21333223296000), ([1,14,19], -67189022208000), ([1,14,21], -4365868953600), ([1,14,22], -12599337676800), ([1,14,23], -21333223296000), ([1,15,19], -67189022208000), ([1,15,21], -4365868953600), ([1,15,22], -12599337676800), ([1,15,23], -21333223296000), ([1,16,19], -67189022208000), ([1,16,21], -4365868953600), ([1,16,22], -12599337676800), ([1,16,23], -21333223296000), ([1,17,19], -67189022208000), ([1,17,21], -4365868953600), ([1,17,22], -12599337676800), ([1,17,23], -21333223296000), ([1,18,19], -33594511104000), ([1,18,21], -2182934476800), ([1,18,22], -6360234316800), ([1,18,23], -10666611648000), ([1,19,19], -16797255552000), ([1,19,20], 16797255552000), ([1,19,21], 24104416089600), ([1,19,22], 38752456243200), ([1,19,23], 70254344160000), ([1,20,21], 1091467238400), ([1,20,22], 3119551680000), ([1,20,23], 5333305824000), ([1,21,21], 1637200857600), ([1,21,22], 7407995616000), ([1,21,23], 12911561308800), ([1,22,22], 7798879200000), ([1,22,23], 27371247120000), ([1,23,23], 23999876208000), ([2,2,22], -60565478400), ([2,3,22], -53301486873600), ([2,4,4], -17295309964800), ([2,4,22], -134630830118400), ([2,5,5], -34946253619200), ([2,5,22], -192285468748800), ([2,5,23], -160144104153600), ([2,6,6], -66338528256000), ([2,6,7], -46488944409600), ([2,6,22], -248574898252800), ([2,6,23], -203993551641600), ([2,7,7], -84973795737600), ([2,7,8], -90714629913600), ([2,7,9], -7529455863072), ([2,7,22], -259335221734400), ([2,7,23], -204780258547200), ([2,8,8], -112605399244800), ([2,8,9], -125016778985472), ([2,8,10], -23050175680224), ([2,8,22], -260822011161600), ([2,8,23], -195134239641600), ([2,9,9], -130233141891072), ([2,9,10], -132506633723904), ([2,9,22], -221368271723520), ([2,9,23], -146555199595008), ([2,10,10], -120095253983232), ([2,10,11], -77712204125952), ([2,10,22], -111371053931520), ([2,10,23], -32400483867648), ([2,11,11], -82979758667520), ([2,11,22], -730700712960), ([2,12,22], -121130956800), ([2,13,22], -121130956800), ([2,14,22], -121130956800), ([2,15,22], -121130956800), ([2,16,22], -121130956800), ([2,17,22], -121130956800), ([2,18,22], -121130956800), ([2,19,22], -121130956800), ([3,3,22], -53240921395200), ([3,4,4], -17295309964800), ([3,4,22], -187811186035200), ([3,5,5], -34946253619200), ([3,5,22], -245465824665600), ([3,5,23], -160144104153600), ([3,6,6], -66338528256000), ([3,6,7], -46488944409600), ([3,6,22], -301755254169600), ([3,6,23], -203993551641600), ([3,7,7], -84973795737600), ([3,7,8], -90714629913600), ([3,7,9], -7529455863072), ([3,7,22], -312515577651200), ([3,7,23], -204780258547200), ([3,8,8], -112605399244800), ([3,8,9], -125016778985472), ([3,8,10], -23050175680224), ([3,8,22], -314002367078400), ([3,8,23], -195134239641600), ([3,9,9], -130233141891072), ([3,9,10], -132506633723904), ([3,9,22], -274548627640320), ([3,9,23], -146555199595008), ([3,10,10], -120095253983232), ([3,10,11], -77712204125952), ([3,10,22], -164551409848320), ([3,10,23], -32400483867648), ([3,11,11], -82979758667520), ([3,11,22], -53911056629760), ([3,12,22], -53301486873600), ([3,13,22], -53301486873600), ([3,14,22], -53301486873600), ([3,15,22], -53301486873600), ([3,16,22], -53301486873600), ([3,17,22], -53301486873600), ([3,18,22], -26711308915200), ([3,19,22], -13416219936000), ([3,20,22], 13295088979200), ([3,21,22], 19942633468800), ([3,22,22], 33237722448000), ([3,22,23], 59827900406400), ([4,4,4], -17295309964800), ([4,4,5], -17295309964800), ([4,4,6], -17295309964800), ([4,4,7], -17295309964800), ([4,4,8], -17295309964800), ([4,4,9], -17295309964800), ([4,4,10], -17295309964800), ([4,4,11], -17295309964800), ([4,4,12], -17295309964800), ([4,4,13], -17295309964800), ([4,4,14], -17295309964800), ([4,4,15], -17295309964800), ([4,4,16], -17295309964800), ([4,4,17], -17295309964800), ([4,4,18], -15133396219200), ([4,4,19], -10809568728000), ([4,4,20], -6485741236800), ([4,4,21], 2161913745600), ([4,4,22], -123760695912000), ([4,4,23], 19457223710400), ([4,5,5], -34946253619200), ([4,5,22], -326795167910400), ([4,5,23], -160144104153600), ([4,6,6], -66338528256000), ([4,6,7], -46488944409600), ([4,6,22], -383084597414400), ([4,6,23], -203993551641600), ([4,7,7], -84973795737600), ([4,7,8], -90714629913600), ([4,7,9], -7529455863072), ([4,7,22], -393844920896000), ([4,7,23], -204780258547200), ([4,8,8], -112605399244800), ([4,8,9], -125016778985472), ([4,8,10], -23050175680224), ([4,8,22], -395331710323200), ([4,8,23], -195134239641600), ([4,9,9], -130233141891072), ([4,9,10], -132506633723904), ([4,9,22], -355877970885120), ([4,9,23], -146555199595008), ([4,10,10], -120095253983232), ([4,10,11], -77712204125952), ([4,10,22], -245880753093120), ([4,10,23], -32400483867648), ([4,11,11], -82979758667520), ([4,11,22], -135240399874560), ([4,12,22], -134630830118400), ([4,13,22], -134630830118400), ([4,14,22], -134630830118400), ([4,15,22], -134630830118400), ([4,16,22], -134630830118400), ([4,17,22], -134630830118400), ([4,18,22], -67375980537600), ([4,19,22], -33748555747200), ([4,20,22], 33627424790400), ([4,21,22], 50441137185600), ([4,22,22], 84068561976000), ([4,22,23], 151323411556800), ([5,5,5], -34946253619200), ([5,5,6], -34946253619200), ([5,5,7], -34946253619200), ([5,5,8], -34946253619200), ([5,5,9], -34946253619200), ([5,5,10], -34946253619200), ([5,5,11], -34946253619200), ([5,5,12], -34946253619200), ([5,5,13], -34946253619200), ([5,5,14], -34946253619200), ([5,5,15], -34946253619200), ([5,5,16], -34946253619200), ([5,5,17], -34946253619200), ([5,5,18], -30577971916800), ([5,5,19], -21841408512000), ([5,5,20], -13104845107200), ([5,5,21], 4368281702400), ([5,5,22], -170383494758400), ([5,5,23], -120829568832000), ([5,6,6], -66338528256000), ([5,6,7], -46488944409600), ([5,6,22], -440739236044800), ([5,6,23], -364137655795200), ([5,7,7], -84973795737600), ([5,7,8], -90714629913600), ([5,7,9], -7529455863072), ([5,7,22], -451499559526400), ([5,7,23], -364924362700800), ([5,8,8], -112605399244800), ([5,8,9], -125016778985472), ([5,8,10], -23050175680224), ([5,8,22], -452986348953600), ([5,8,23], -355278343795200), ([5,9,9], -130233141891072), ([5,9,10], -132506633723904), ([5,9,22], -413532609515520), ([5,9,23], -306699303748608), ([5,10,10], -120095253983232), ([5,10,11], -77712204125952), ([5,10,22], -303535391723520), ([5,10,23], -192544588021248), ([5,11,11], -82979758667520), ([5,11,22], -192895038504960), ([5,11,23], -160144104153600), ([5,12,22], -192285468748800), ([5,12,23], -160144104153600), ([5,13,22], -192285468748800), ([5,13,23], -160144104153600), ([5,14,22], -192285468748800), ([5,14,23], -160144104153600), ([5,15,22], -192285468748800), ([5,15,23], -160144104153600), ([5,16,22], -192285468748800), ([5,16,23], -160144104153600), ([5,17,22], -192285468748800), ([5,17,23], -160144104153600), ([5,18,22], -96203299852800), ([5,18,23], -80072052076800), ([5,19,22], -48162215404800), ([5,19,23], -40036026038400), ([5,20,22], 48041084448000), ([5,20,23], 40036026038400), ([5,21,22], 72061626672000), ([5,21,23], 60054039057600), ([5,22,22], 120102711120000), ([5,22,23], 316274945112000), ([5,23,23], 180162117172800), ([6,6,6], -66338528256000), ([6,6,7], -112827472665600), ([6,6,8], -66338528256000), ([6,6,9], -66338528256000), ([6,6,10], -66338528256000), ([6,6,11], -66338528256000), ([6,6,12], -66338528256000), ([6,6,13], -66338528256000), ([6,6,14], -66338528256000), ([6,6,15], -66338528256000), ([6,6,16], -66338528256000), ([6,6,17], -66338528256000), ([6,6,18], -58046212224000), ([6,6,19], -41461580160000), ([6,6,20], -24876948096000), ([6,6,21], 8292316032000), ([6,6,22], -207052752614400), ([6,6,23], -129362707353600), ([6,7,7], -131462740147200), ([6,7,8], -137203574323200), ([6,7,9], -54018400272672), ([6,7,10], -46488944409600), ([6,7,11], -46488944409600), ([6,7,12], -46488944409600), ([6,7,13], -46488944409600), ([6,7,14], -46488944409600), ([6,7,15], -46488944409600), ([6,7,16], -46488944409600), ([6,7,17], -46488944409600), ([6,7,18], -38678102453760), ([6,7,19], -25722717081600), ([6,7,20], -14100480979200), ([6,7,21], 9143991225600), ([6,7,22], -476733674869760), ([6,7,23], -356473747728000), ([6,8,8], -112605399244800), ([6,8,9], -125016778985472), ([6,8,10], -23050175680224), ([6,8,22], -509275778457600), ([6,8,23], -399127791283200), ([6,9,9], -130233141891072), ([6,9,10], -132506633723904), ([6,9,22], -469822039019520), ([6,9,23], -350548751236608), ([6,10,10], -120095253983232), ([6,10,11], -77712204125952), ([6,10,22], -359824821227520), ([6,10,23], -236394035509248), ([6,11,11], -82979758667520), ([6,11,22], -249184468008960), ([6,11,23], -203993551641600), ([6,12,22], -248574898252800), ([6,12,23], -203993551641600), ([6,13,22], -248574898252800), ([6,13,23], -203993551641600), ([6,14,22], -248574898252800), ([6,14,23], -203993551641600), ([6,15,22], -248574898252800), ([6,15,23], -203993551641600), ([6,16,22], -248574898252800), ([6,16,23], -203993551641600), ([6,17,22], -248574898252800), ([6,17,23], -203993551641600), ([6,18,22], -124348014604800), ([6,18,23], -101996775820800), ([6,19,22], -62234572780800), ([6,19,23], -50998387910400), ([6,20,22], 62113441824000), ([6,20,23], 50998387910400), ([6,21,22], 93170162736000), ([6,21,23], 76497581865600), ([6,22,22], 155283604560000), ([6,22,23], 407006457984000), ([6,23,23], 229492745596800), ([7,7,7], -84973795737600), ([7,7,8], -175688425651200), ([7,7,9], -92503251600672), ([7,7,10], -84973795737600), ([7,7,11], -84973795737600), ([7,7,12], -84973795737600), ([7,7,13], -84973795737600), ([7,7,14], -84973795737600), ([7,7,15], -84973795737600), ([7,7,16], -84973795737600), ([7,7,17], -84973795737600), ([7,7,18], -74352071270400), ([7,7,19], -53108622336000), ([7,7,20], -31865173401600), ([7,7,21], 10621724467200), ([7,7,22], -206166033920000), ([7,7,23], -109184738342400), ([7,8,8], -203320029158400), ([7,8,9], -223260864762144), ([7,8,10], -113764805593824), ([7,8,11], -90714629913600), ([7,8,12], -90714629913600), ([7,8,13], -90714629913600), ([7,8,14], -90714629913600), ([7,8,15], -90714629913600), ([7,8,16], -90714629913600), ([7,8,17], -90714629913600), ([7,8,18], -55791635444160), ([7,8,19], -17390534145600), ([7,8,20], 5288123332800), ([7,8,21], 50645438289600), ([7,8,22], -439755792512960), ([7,8,23], -297860539536000), ([7,9,9], -137762597754144), ([7,9,10], -140036089586976), ([7,9,11], -7529455863072), ([7,9,12], -7529455863072), ([7,9,13], -7529455863072), ([7,9,14], -7529455863072), ([7,9,15], -7529455863072), ([7,9,16], -7529455863072), ([7,9,17], -7529455863072), ([7,9,18], -3764727931536), ([7,9,20], 1882363965768), ([7,9,21], 5647091897304), ([7,9,22], -473052906638048), ([7,9,23], -342864820296252), ([7,10,10], -120095253983232), ([7,10,11], -77712204125952), ([7,10,22], -370585144709120), ([7,10,23], -237180742414848), ([7,11,11], -82979758667520), ([7,11,22], -259944791490560), ([7,11,23], -204780258547200), ([7,12,22], -259335221734400), ([7,12,23], -204780258547200), ([7,13,22], -259335221734400), ([7,13,23], -204780258547200), ([7,14,22], -259335221734400), ([7,14,23], -204780258547200), ([7,15,22], -259335221734400), ([7,15,23], -204780258547200), ([7,16,22], -259335221734400), ([7,16,23], -204780258547200), ([7,17,22], -259335221734400), ([7,17,23], -204780258547200), ([7,18,22], -129728176345600), ([7,18,23], -102390129273600), ([7,19,22], -64924653651200), ([7,19,23], -51195064636800), ([7,20,22], 64803522694400), ([7,20,23], 51195064636800), ([7,21,22], 97205284041600), ([7,21,23], 76792596955200), ([7,22,22], 162008806736000), ([7,22,23], 419603513716800), ([7,23,23], 230377790865600), ([8,8,8], -112605399244800), ([8,8,9], -237622178230272), ([8,8,10], -135655574925024), ([8,8,11], -112605399244800), ([8,8,12], -112605399244800), ([8,8,13], -112605399244800), ([8,8,14], -112605399244800), ([8,8,15], -112605399244800), ([8,8,16], -112605399244800), ([8,8,17], -112605399244800), ([8,8,18], -98529724339200), ([8,8,19], -70378374528000), ([8,8,20], -42227024716800), ([8,8,21], 14075674905600), ([8,8,22], -190383071155200), ([8,8,23], -68453165491200), ([8,9,9], -255249920876544), ([8,9,10], -280573588389600), ([8,9,11], -125016778985472), ([8,9,12], -125016778985472), ([8,9,13], -125016778985472), ([8,9,14], -125016778985472), ([8,9,15], -125016778985472), ([8,9,16], -125016778985472), ([8,9,17], -125016778985472), ([8,9,18], -87680823487488), ([8,9,19], -41954056657920), ([8,9,20], -10699861911552), ([8,9,21], 51808527581184), ([8,9,22], -382224806937600), ([8,9,23], -201045562877952), ([8,10,10], -143145429663456), ([8,10,11], -100762379806176), ([8,10,12], -23050175680224), ([8,10,13], -23050175680224), ([8,10,14], -23050175680224), ([8,10,15], -23050175680224), ([8,10,16], -23050175680224), ([8,10,17], -23050175680224), ([8,10,18], -19793954538864), ([8,10,19], -13781444497920), ([8,10,20], -8018900577864), ([8,10,21], 3506187262248), ([8,10,22], -357290625154848), ([8,10,23], -201603275868996), ([8,11,11], -82979758667520), ([8,11,22], -261431580917760), ([8,11,23], -195134239641600), ([8,12,22], -260822011161600), ([8,12,23], -195134239641600), ([8,13,22], -260822011161600), ([8,13,23], -195134239641600), ([8,14,22], -260822011161600), ([8,14,23], -195134239641600), ([8,15,22], -260822011161600), ([8,15,23], -195134239641600), ([8,16,22], -260822011161600), ([8,16,23], -195134239641600), ([8,17,22], -260822011161600), ([8,17,23], -195134239641600), ([8,18,22], -130471571059200), ([8,18,23], -97567119820800), ([8,19,22], -65296351008000), ([8,19,23], -48783559910400), ([8,20,22], 65175220051200), ([8,20,23], 48783559910400), ([8,21,22], 97762830076800), ([8,21,23], 73175339865600), ([8,22,22], 162938050128000), ([8,22,23], 415247390006400), ([8,23,23], 219526019596800), ([9,9,9], -130233141891072), ([9,9,10], -262739775614976), ([9,9,11], -130233141891072), ([9,9,12], -130233141891072), ([9,9,13], -130233141891072), ([9,9,14], -130233141891072), ([9,9,15], -130233141891072), ([9,9,16], -130233141891072), ([9,9,17], -130233141891072), ([9,9,18], -113953999154688), ([9,9,19], -81395713681920), ([9,9,20], -48837428209152), ([9,9,21], 16279142736384), ([9,9,22], -139911992563200), ([9,9,23], -42914967552), ([9,10,10], -252601887707136), ([9,10,11], -210218837849856), ([9,10,12], -132506633723904), ([9,10,13], -132506633723904), ([9,10,14], -132506633723904), ([9,10,15], -132506633723904), ([9,10,16], -132506633723904), ([9,10,17], -132506633723904), ([9,10,18], -115943304508416), ([9,10,19], -82816646077440), ([9,10,20], -49689987646464), ([9,10,21], 16563329215488), ([9,10,22], -249801548620800), ([9,10,23], -29885720523264), ([9,11,11], -82979758667520), ([9,11,22], -221977841479680), ([9,11,23], -146555199595008), ([9,12,22], -221368271723520), ([9,12,23], -146555199595008), ([9,13,22], -221368271723520), ([9,13,23], -146555199595008), ([9,14,22], -221368271723520), ([9,14,23], -146555199595008), ([9,15,22], -221368271723520), ([9,15,23], -146555199595008), ([9,16,22], -221368271723520), ([9,16,23], -146555199595008), ([9,17,22], -221368271723520), ([9,17,23], -146555199595008), ([9,18,22], -110744701340160), ([9,18,23], -73277599797504), ([9,19,22], -55432916148480), ([9,19,23], -36638799898752), ([9,20,22], 55311785191680), ([9,20,23], 36638799898752), ([9,21,22], 82967677787520), ([9,21,23], 54958199848128), ([9,22,22], 138279462979200), ([9,22,23], 340500033109440), ([9,23,23], 164874599544384), ([10,10,10], -120095253983232), ([10,10,11], -197807458109184), ([10,10,12], -120095253983232), ([10,10,13], -120095253983232), ([10,10,14], -120095253983232), ([10,10,15], -120095253983232), ([10,10,16], -120095253983232), ([10,10,17], -120095253983232), ([10,10,18], -105083347235328), ([10,10,19], -75059533739520), ([10,10,20], -45035720243712), ([10,10,21], 15011906747904), ([10,10,22], -36250954713600), ([10,10,23], 102706676863488), ([10,11,11], -160691962793472), ([10,11,12], -77712204125952), ([10,11,13], -77712204125952), ([10,11,14], -77712204125952), ([10,11,15], -77712204125952), ([10,11,16], -77712204125952), ([10,11,17], -77712204125952), ([10,11,18], -67998178610208), ([10,11,19], -48570127578720), ([10,11,20], -29142076547232), ([10,11,21], 9714025515744), ([10,11,22], -63410496108960), ([10,11,23], 55025745774048), ([10,12,22], -111371053931520), ([10,12,23], -32400483867648), ([10,13,22], -111371053931520), ([10,13,23], -32400483867648), ([10,14,22], -111371053931520), ([10,14,23], -32400483867648), ([10,15,22], -111371053931520), ([10,15,23], -32400483867648), ([10,16,22], -111371053931520), ([10,16,23], -32400483867648), ([10,17,22], -111371053931520), ([10,17,23], -32400483867648), ([10,18,22], -55746092444160), ([10,18,23], -16200241933824), ([10,19,22], -27933611700480), ([10,19,23], -8100120966912), ([10,20,22], 27812480743680), ([10,20,23], 8100120966912), ([10,21,22], 41718721115520), ([10,21,23], 12150181450368), ([10,22,22], 69531201859200), ([10,22,23], 145406465763840), ([10,23,23], 36450544351104), ([11,11,11], -82979758667520), ([11,11,12], -82979758667520), ([11,11,13], -82979758667520), ([11,11,14], -82979758667520), ([11,11,15], -82979758667520), ([11,11,16], -82979758667520), ([11,11,17], -82979758667520), ([11,11,18], -72607288834080), ([11,11,19], -51862349167200), ([11,11,20], -31117409500320), ([11,11,21], 10372469833440), ([11,11,22], 51192213932640), ([11,11,23], 93352228500960), ([11,12,22], -730700712960), ([11,13,22], -730700712960), ([11,14,22], -730700712960), ([11,15,22], -730700712960), ([11,16,22], -730700712960), ([11,17,22], -730700712960), ([11,18,22], -425915834880), ([11,19,22], -273523395840), ([11,20,22], 152392439040), ([11,21,22], 228588658560), ([11,22,22], 380981097600), ([11,22,23], 685765975680), ([12,12,22], -60565478400), ([12,13,22], -121130956800), ([12,14,22], -121130956800), ([12,15,22], -121130956800), ([12,16,22], -121130956800), ([12,17,22], -121130956800), ([12,18,22], -121130956800), ([12,19,22], -121130956800), ([13,13,22], -60565478400), ([13,14,22], -121130956800), ([13,15,22], -121130956800), ([13,16,22], -121130956800), ([13,17,22], -121130956800), ([13,18,22], -121130956800), ([13,19,22], -121130956800), ([14,14,22], -60565478400), ([14,15,22], -121130956800), ([14,16,22], -121130956800), ([14,17,22], -121130956800), ([14,18,22], -121130956800), ([14,19,22], -121130956800), ([15,15,22], -60565478400), ([15,16,22], -121130956800), ([15,17,22], -121130956800), ([15,18,22], -121130956800), ([15,19,22], -121130956800), ([16,16,22], -60565478400), ([16,17,22], -121130956800), ([16,18,22], -121130956800), ([16,19,22], -121130956800), ([17,17,22], -60565478400), ([17,18,22], -121130956800), ([17,19,22], -121130956800), ([18,18,22], -60565478400), ([18,19,22], -121130956800), ([18,22,23], 242261913600), ([19,19,22], -60565478400), ([19,22,23], 242261913600), ([20,22,23], 242261913600), ([21,22,23], 242261913600), ([22,22,23], 242261913600), ([22,23,23], 242261913600)]
theorem block000_data : block000 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (60565478400 : Int) atom0000) (SparsePolynomial.scale (333287317440 : Int) atom0001)) (SparsePolynomial.merge (SparsePolynomial.scale (3930610955040 : Int) atom0002) (SparsePolynomial.scale (470590991442 : Int) atom0003))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3618143020800 : Int) atom0004) (SparsePolynomial.scale (62491530222 : Int) atom0005)) (SparsePolynomial.merge (SparsePolynomial.scale (4199313888000 : Int) atom0006) (SparsePolynomial.merge (SparsePolynomial.scale (272866809600 : Int) atom0007) (SparsePolynomial.scale (779887920000 : Int) atom0008))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1333326456000 : Int) atom0009) (SparsePolynomial.scale (3323772244800 : Int) atom0010)) (SparsePolynomial.merge (SparsePolynomial.scale (8406856197600 : Int) atom0011) (SparsePolynomial.merge (SparsePolynomial.scale (12010271112000 : Int) atom0012) (SparsePolynomial.scale (10009006509600 : Int) atom0013)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15528360456000 : Int) atom0014) (SparsePolynomial.scale (12749596977600 : Int) atom0015)) (SparsePolynomial.merge (SparsePolynomial.scale (16200880673600 : Int) atom0016) (SparsePolynomial.merge (SparsePolynomial.scale (12798766159200 : Int) atom0017) (SparsePolynomial.scale (16293805012800 : Int) atom0018)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12195889977600 : Int) atom0019) (SparsePolynomial.scale (13827946297920 : Int) atom0020)) (SparsePolynomial.merge (SparsePolynomial.scale (9159699974688 : Int) atom0021) (SparsePolynomial.merge (SparsePolynomial.scale (6953120185920 : Int) atom0022) (SparsePolynomial.scale (2025030241728 : Int) atom0023)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (38098109760 : Int) atom0024) (SparsePolynomial.scale (1080956872800 : Int) atom0025)) (SparsePolynomial.merge (SparsePolynomial.scale (2184140851200 : Int) atom0026) (SparsePolynomial.merge (SparsePolynomial.scale (4146158016000 : Int) atom0027) (SparsePolynomial.scale (2572271708160 : Int) atom0028))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5310862233600 : Int) atom0029) (SparsePolynomial.scale (1739053414560 : Int) atom0030)) (SparsePolynomial.merge (SparsePolynomial.scale (7037837452800 : Int) atom0031) (SparsePolynomial.merge (SparsePolynomial.scale (4195405665792 : Int) atom0032) (SparsePolynomial.scale (1378144449792 : Int) atom0033)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8139571368192 : Int) atom0034) (SparsePolynomial.scale (8281664607744 : Int) atom0035)) (SparsePolynomial.merge (SparsePolynomial.scale (7505953373952 : Int) atom0036) (SparsePolynomial.merge (SparsePolynomial.scale (4857012757872 : Int) atom0037) (SparsePolynomial.scale (5186234916720 : Int) atom0038))))))) := by decide +kernel
theorem block000_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block000 := by
  rw [block000_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0000_nonneg g hg hA hB) (atom0001_nonneg g hg hA hB)) (add_nonneg (atom0002_nonneg g hg hA hB) (atom0003_nonneg g hg hA hB))) (add_nonneg (add_nonneg (atom0004_nonneg g hg hA hB) (atom0005_nonneg g hg hA hB)) (add_nonneg (atom0006_nonneg g hg hA hB) (add_nonneg (atom0007_nonneg g hg hA hB) (atom0008_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0009_nonneg g hg hA hB) (atom0010_nonneg g hg hA hB)) (add_nonneg (atom0011_nonneg g hg hA hB) (add_nonneg (atom0012_nonneg g hg hA hB) (atom0013_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0014_nonneg g hg hA hB) (atom0015_nonneg g hg hA hB)) (add_nonneg (atom0016_nonneg g hg hA hB) (add_nonneg (atom0017_nonneg g hg hA hB) (atom0018_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0019_nonneg g hg hA hB) (atom0020_nonneg g hg hA hB)) (add_nonneg (atom0021_nonneg g hg hA hB) (add_nonneg (atom0022_nonneg g hg hA hB) (atom0023_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0024_nonneg g hg hA hB) (atom0025_nonneg g hg hA hB)) (add_nonneg (atom0026_nonneg g hg hA hB) (add_nonneg (atom0027_nonneg g hg hA hB) (atom0028_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0029_nonneg g hg hA hB) (atom0030_nonneg g hg hA hB)) (add_nonneg (atom0031_nonneg g hg hA hB) (add_nonneg (atom0032_nonneg g hg hA hB) (atom0033_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0034_nonneg g hg hA hB) (atom0035_nonneg g hg hA hB)) (add_nonneg (atom0036_nonneg g hg hA hB) (add_nonneg (atom0037_nonneg g hg hA hB) (atom0038_nonneg g hg hA hB)))))))

end APPT.Finite24
