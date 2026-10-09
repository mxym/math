import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0495 : SparsePolynomial.Poly := [([2,8,8], 1)]
theorem eval_atom0495 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0495 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0495_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3718671360 : Int) atom0495) := by
  rw [SparsePolynomial.eval_scale, eval_atom0495]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0495Coded : CoefficientMerge.Poly := [(800, 1)]
theorem atom0495Coded_decode : atom0495 = SparsePolynomial.decodeCubic 18 atom0495Coded := by decide +kernel
theorem atom0495Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) := by
  have h := atom0495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0496 : SparsePolynomial.Poly := [([2,8,9], 1)]
theorem eval_atom0496 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0496 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0496_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6793720320 : Int) atom0496) := by
  rw [SparsePolynomial.eval_scale, eval_atom0496]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0496Coded : CoefficientMerge.Poly := [(801, 1)]
theorem atom0496Coded_decode : atom0496 = SparsePolynomial.decodeCubic 18 atom0496Coded := by decide +kernel
theorem atom0496Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded) := by
  have h := atom0496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0497 : SparsePolynomial.Poly := [([2,8,10], 1)]
theorem eval_atom0497 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0497 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0497_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6517608960 : Int) atom0497) := by
  rw [SparsePolynomial.eval_scale, eval_atom0497]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0497Coded : CoefficientMerge.Poly := [(802, 1)]
theorem atom0497Coded_decode : atom0497 = SparsePolynomial.decodeCubic 18 atom0497Coded := by decide +kernel
theorem atom0497Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) := by
  have h := atom0497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0498 : SparsePolynomial.Poly := [([2,8,11], 1)]
theorem eval_atom0498 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0498 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0498_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6167040000 : Int) atom0498) := by
  rw [SparsePolynomial.eval_scale, eval_atom0498]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0498Coded : CoefficientMerge.Poly := [(803, 1)]
theorem atom0498Coded_decode : atom0498 = SparsePolynomial.decodeCubic 18 atom0498Coded := by decide +kernel
theorem atom0498Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) := by
  have h := atom0498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0499 : SparsePolynomial.Poly := [([2,8,12], 1)]
theorem eval_atom0499 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0499 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0499_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7979381760 : Int) atom0499) := by
  rw [SparsePolynomial.eval_scale, eval_atom0499]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0499Coded : CoefficientMerge.Poly := [(804, 1)]
theorem atom0499Coded_decode : atom0499 = SparsePolynomial.decodeCubic 18 atom0499Coded := by decide +kernel
theorem atom0499Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded) := by
  have h := atom0499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0500 : SparsePolynomial.Poly := [([2,8,13], 1)]
theorem eval_atom0500 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0500 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0500_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6566323200 : Int) atom0500) := by
  rw [SparsePolynomial.eval_scale, eval_atom0500]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0500Coded : CoefficientMerge.Poly := [(805, 1)]
theorem atom0500Coded_decode : atom0500 = SparsePolynomial.decodeCubic 18 atom0500Coded := by decide +kernel
theorem atom0500Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) := by
  have h := atom0500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0501 : SparsePolynomial.Poly := [([2,8,14], 1)]
theorem eval_atom0501 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0501 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0501_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8933124000 : Int) atom0501) := by
  rw [SparsePolynomial.eval_scale, eval_atom0501]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0501Coded : CoefficientMerge.Poly := [(806, 1)]
theorem atom0501Coded_decode : atom0501 = SparsePolynomial.decodeCubic 18 atom0501Coded := by decide +kernel
theorem atom0501Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded) := by
  have h := atom0501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0502 : SparsePolynomial.Poly := [([2,8,15], 1)]
theorem eval_atom0502 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0502 = ((g 2) * (g 8) * (g 15)) := by
  norm_num [atom0502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0502_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7949368320 : Int) atom0502) := by
  rw [SparsePolynomial.eval_scale, eval_atom0502]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0502Coded : CoefficientMerge.Poly := [(807, 1)]
theorem atom0502Coded_decode : atom0502 = SparsePolynomial.decodeCubic 18 atom0502Coded := by decide +kernel
theorem atom0502Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) := by
  have h := atom0502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0503 : SparsePolynomial.Poly := [([2,8,16], 1)]
theorem eval_atom0503 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0503 = ((g 2) * (g 8) * (g 16)) := by
  norm_num [atom0503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0503_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8692055040 : Int) atom0503) := by
  rw [SparsePolynomial.eval_scale, eval_atom0503]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0503Coded : CoefficientMerge.Poly := [(808, 1)]
theorem atom0503Coded_decode : atom0503 = SparsePolynomial.decodeCubic 18 atom0503Coded := by decide +kernel
theorem atom0503Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) := by
  have h := atom0503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0504 : SparsePolynomial.Poly := [([2,8,17], 1)]
theorem eval_atom0504 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0504 = ((g 2) * (g 8) * (g 17)) := by
  norm_num [atom0504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0504_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10609182720 : Int) atom0504) := by
  rw [SparsePolynomial.eval_scale, eval_atom0504]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0504Coded : CoefficientMerge.Poly := [(809, 1)]
theorem atom0504Coded_decode : atom0504 = SparsePolynomial.decodeCubic 18 atom0504Coded := by decide +kernel
theorem atom0504Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded) := by
  have h := atom0504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0505 : SparsePolynomial.Poly := [([2,9,9], 1)]
theorem eval_atom0505 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0505 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0505_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4164011520 : Int) atom0505) := by
  rw [SparsePolynomial.eval_scale, eval_atom0505]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0505Coded : CoefficientMerge.Poly := [(819, 1)]
theorem atom0505Coded_decode : atom0505 = SparsePolynomial.decodeCubic 18 atom0505Coded := by decide +kernel
theorem atom0505Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) := by
  have h := atom0505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0506 : SparsePolynomial.Poly := [([2,9,10], 1)]
theorem eval_atom0506 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0506 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0506_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7503144960 : Int) atom0506) := by
  rw [SparsePolynomial.eval_scale, eval_atom0506]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0506Coded : CoefficientMerge.Poly := [(820, 1)]
theorem atom0506Coded_decode : atom0506 = SparsePolynomial.decodeCubic 18 atom0506Coded := by decide +kernel
theorem atom0506Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded) := by
  have h := atom0506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0507 : SparsePolynomial.Poly := [([2,9,11], 1)]
theorem eval_atom0507 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0507 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0507_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6954524160 : Int) atom0507) := by
  rw [SparsePolynomial.eval_scale, eval_atom0507]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0507Coded : CoefficientMerge.Poly := [(821, 1)]
theorem atom0507Coded_decode : atom0507 = SparsePolynomial.decodeCubic 18 atom0507Coded := by decide +kernel
theorem atom0507Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) := by
  have h := atom0507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0508 : SparsePolynomial.Poly := [([2,9,12], 1)]
theorem eval_atom0508 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0508 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0508_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8592628800 : Int) atom0508) := by
  rw [SparsePolynomial.eval_scale, eval_atom0508]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0508Coded : CoefficientMerge.Poly := [(822, 1)]
theorem atom0508Coded_decode : atom0508 = SparsePolynomial.decodeCubic 18 atom0508Coded := by decide +kernel
theorem atom0508Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) := by
  have h := atom0508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0509 : SparsePolynomial.Poly := [([2,9,13], 1)]
theorem eval_atom0509 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0509 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0509_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7029147840 : Int) atom0509) := by
  rw [SparsePolynomial.eval_scale, eval_atom0509]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0509Coded : CoefficientMerge.Poly := [(823, 1)]
theorem atom0509Coded_decode : atom0509 = SparsePolynomial.decodeCubic 18 atom0509Coded := by decide +kernel
theorem atom0509Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded) := by
  have h := atom0509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0510 : SparsePolynomial.Poly := [([2,9,14], 1)]
theorem eval_atom0510 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0510 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0510_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9631143840 : Int) atom0510) := by
  rw [SparsePolynomial.eval_scale, eval_atom0510]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0510Coded : CoefficientMerge.Poly := [(824, 1)]
theorem atom0510Coded_decode : atom0510 = SparsePolynomial.decodeCubic 18 atom0510Coded := by decide +kernel
theorem atom0510Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) := by
  have h := atom0510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0511 : SparsePolynomial.Poly := [([2,9,15], 1)]
theorem eval_atom0511 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0511 = ((g 2) * (g 9) * (g 15)) := by
  norm_num [atom0511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0511_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8158977600 : Int) atom0511) := by
  rw [SparsePolynomial.eval_scale, eval_atom0511]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0511Coded : CoefficientMerge.Poly := [(825, 1)]
theorem atom0511Coded_decode : atom0511 = SparsePolynomial.decodeCubic 18 atom0511Coded := by decide +kernel
theorem atom0511Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded) := by
  have h := atom0511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0512 : SparsePolynomial.Poly := [([2,9,16], 1)]
theorem eval_atom0512 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0512 = ((g 2) * (g 9) * (g 16)) := by
  norm_num [atom0512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0512_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8798871360 : Int) atom0512) := by
  rw [SparsePolynomial.eval_scale, eval_atom0512]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0512Coded : CoefficientMerge.Poly := [(826, 1)]
theorem atom0512Coded_decode : atom0512 = SparsePolynomial.decodeCubic 18 atom0512Coded := by decide +kernel
theorem atom0512Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) := by
  have h := atom0512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0513 : SparsePolynomial.Poly := [([2,9,17], 1)]
theorem eval_atom0513 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0513 = ((g 2) * (g 9) * (g 17)) := by
  norm_num [atom0513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0513_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10613206080 : Int) atom0513) := by
  rw [SparsePolynomial.eval_scale, eval_atom0513]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0513Coded : CoefficientMerge.Poly := [(827, 1)]
theorem atom0513Coded_decode : atom0513 = SparsePolynomial.decodeCubic 18 atom0513Coded := by decide +kernel
theorem atom0513Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) := by
  have h := atom0513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0514 : SparsePolynomial.Poly := [([2,10,10], 1)]
theorem eval_atom0514 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0514 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0514_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4531960320 : Int) atom0514) := by
  rw [SparsePolynomial.eval_scale, eval_atom0514]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0514Coded : CoefficientMerge.Poly := [(838, 1)]
theorem atom0514Coded_decode : atom0514 = SparsePolynomial.decodeCubic 18 atom0514Coded := by decide +kernel
theorem atom0514Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded) := by
  have h := atom0514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0515 : SparsePolynomial.Poly := [([2,10,11], 1)]
theorem eval_atom0515 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0515 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0515_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7932940800 : Int) atom0515) := by
  rw [SparsePolynomial.eval_scale, eval_atom0515]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0515Coded : CoefficientMerge.Poly := [(839, 1)]
theorem atom0515Coded_decode : atom0515 = SparsePolynomial.decodeCubic 18 atom0515Coded := by decide +kernel
theorem atom0515Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) := by
  have h := atom0515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0516 : SparsePolynomial.Poly := [([2,10,12], 1)]
theorem eval_atom0516 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0516 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0516_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9311655360 : Int) atom0516) := by
  rw [SparsePolynomial.eval_scale, eval_atom0516]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0516Coded : CoefficientMerge.Poly := [(840, 1)]
theorem atom0516Coded_decode : atom0516 = SparsePolynomial.decodeCubic 18 atom0516Coded := by decide +kernel
theorem atom0516Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded) := by
  have h := atom0516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0517 : SparsePolynomial.Poly := [([2,10,13], 1)]
theorem eval_atom0517 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0517 = ((g 2) * (g 10) * (g 13)) := by
  norm_num [atom0517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0517_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7477765440 : Int) atom0517) := by
  rw [SparsePolynomial.eval_scale, eval_atom0517]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0517Coded : CoefficientMerge.Poly := [(841, 1)]
theorem atom0517Coded_decode : atom0517 = SparsePolynomial.decodeCubic 18 atom0517Coded := by decide +kernel
theorem atom0517Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) := by
  have h := atom0517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0518 : SparsePolynomial.Poly := [([2,10,14], 1)]
theorem eval_atom0518 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0518 = ((g 2) * (g 10) * (g 14)) := by
  norm_num [atom0518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0518_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10379483040 : Int) atom0518) := by
  rw [SparsePolynomial.eval_scale, eval_atom0518]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0518Coded : CoefficientMerge.Poly := [(842, 1)]
theorem atom0518Coded_decode : atom0518 = SparsePolynomial.decodeCubic 18 atom0518Coded := by decide +kernel
theorem atom0518Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) := by
  have h := atom0518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0519 : SparsePolynomial.Poly := [([2,10,15], 1)]
theorem eval_atom0519 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0519 = ((g 2) * (g 10) * (g 15)) := by
  norm_num [atom0519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0519_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8044739520 : Int) atom0519) := by
  rw [SparsePolynomial.eval_scale, eval_atom0519]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0519Coded : CoefficientMerge.Poly := [(843, 1)]
theorem atom0519Coded_decode : atom0519 = SparsePolynomial.decodeCubic 18 atom0519Coded := by decide +kernel
theorem atom0519Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded) := by
  have h := atom0519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0520 : SparsePolynomial.Poly := [([2,10,16], 1)]
theorem eval_atom0520 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0520 = ((g 2) * (g 10) * (g 16)) := by
  norm_num [atom0520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0520_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8392186560 : Int) atom0520) := by
  rw [SparsePolynomial.eval_scale, eval_atom0520]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0520Coded : CoefficientMerge.Poly := [(844, 1)]
theorem atom0520Coded_decode : atom0520 = SparsePolynomial.decodeCubic 18 atom0520Coded := by decide +kernel
theorem atom0520Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) := by
  have h := atom0520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0521 : SparsePolynomial.Poly := [([2,10,17], 1)]
theorem eval_atom0521 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0521 = ((g 2) * (g 10) * (g 17)) := by
  norm_num [atom0521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0521_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10204830720 : Int) atom0521) := by
  rw [SparsePolynomial.eval_scale, eval_atom0521]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0521Coded : CoefficientMerge.Poly := [(845, 1)]
theorem atom0521Coded_decode : atom0521 = SparsePolynomial.decodeCubic 18 atom0521Coded := by decide +kernel
theorem atom0521Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded) := by
  have h := atom0521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0522 : SparsePolynomial.Poly := [([2,11,11], 1)]
theorem eval_atom0522 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0522 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0522_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4927426560 : Int) atom0522) := by
  rw [SparsePolynomial.eval_scale, eval_atom0522]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0522Coded : CoefficientMerge.Poly := [(857, 1)]
theorem atom0522Coded_decode : atom0522 = SparsePolynomial.decodeCubic 18 atom0522Coded := by decide +kernel
theorem atom0522Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) := by
  have h := atom0522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0523 : SparsePolynomial.Poly := [([2,11,12], 1)]
theorem eval_atom0523 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0523 = ((g 2) * (g 11) * (g 12)) := by
  norm_num [atom0523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0523_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9870336000 : Int) atom0523) := by
  rw [SparsePolynomial.eval_scale, eval_atom0523]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0523Coded : CoefficientMerge.Poly := [(858, 1)]
theorem atom0523Coded_decode : atom0523 = SparsePolynomial.decodeCubic 18 atom0523Coded := by decide +kernel
theorem atom0523Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) := by
  have h := atom0523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0524 : SparsePolynomial.Poly := [([2,11,13], 1)]
theorem eval_atom0524 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0524 = ((g 2) * (g 11) * (g 13)) := by
  norm_num [atom0524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0524_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7722086400 : Int) atom0524) := by
  rw [SparsePolynomial.eval_scale, eval_atom0524]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0524Coded : CoefficientMerge.Poly := [(859, 1)]
theorem atom0524Coded_decode : atom0524 = SparsePolynomial.decodeCubic 18 atom0524Coded := by decide +kernel
theorem atom0524Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded) := by
  have h := atom0524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0525 : SparsePolynomial.Poly := [([2,11,14], 1)]
theorem eval_atom0525 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0525 = ((g 2) * (g 11) * (g 14)) := by
  norm_num [atom0525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0525_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10978907040 : Int) atom0525) := by
  rw [SparsePolynomial.eval_scale, eval_atom0525]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0525Coded : CoefficientMerge.Poly := [(860, 1)]
theorem atom0525Coded_decode : atom0525 = SparsePolynomial.decodeCubic 18 atom0525Coded := by decide +kernel
theorem atom0525Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) := by
  have h := atom0525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0526 : SparsePolynomial.Poly := [([2,11,15], 1)]
theorem eval_atom0526 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0526 = ((g 2) * (g 11) * (g 15)) := by
  norm_num [atom0526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0526_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8678154240 : Int) atom0526) := by
  rw [SparsePolynomial.eval_scale, eval_atom0526]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0526Coded : CoefficientMerge.Poly := [(861, 1)]
theorem atom0526Coded_decode : atom0526 = SparsePolynomial.decodeCubic 18 atom0526Coded := by decide +kernel
theorem atom0526Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded) := by
  have h := atom0526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0527 : SparsePolynomial.Poly := [([2,11,16], 1)]
theorem eval_atom0527 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0527 = ((g 2) * (g 11) * (g 16)) := by
  norm_num [atom0527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0527_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7662090240 : Int) atom0527) := by
  rw [SparsePolynomial.eval_scale, eval_atom0527]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0527Coded : CoefficientMerge.Poly := [(862, 1)]
theorem atom0527Coded_decode : atom0527 = SparsePolynomial.decodeCubic 18 atom0527Coded := by decide +kernel
theorem atom0527Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) := by
  have h := atom0527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0528 : SparsePolynomial.Poly := [([2,11,17], 1)]
theorem eval_atom0528 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0528 = ((g 2) * (g 11) * (g 17)) := by
  norm_num [atom0528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0528_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11373788160 : Int) atom0528) := by
  rw [SparsePolynomial.eval_scale, eval_atom0528]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0528Coded : CoefficientMerge.Poly := [(863, 1)]
theorem atom0528Coded_decode : atom0528 = SparsePolynomial.decodeCubic 18 atom0528Coded := by decide +kernel
theorem atom0528Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) := by
  have h := atom0528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0529 : SparsePolynomial.Poly := [([2,12,12], 1)]
theorem eval_atom0529 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0529 = ((g 2) * (g 12) * (g 12)) := by
  norm_num [atom0529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0529_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6543452160 : Int) atom0529) := by
  rw [SparsePolynomial.eval_scale, eval_atom0529]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0529Coded : CoefficientMerge.Poly := [(876, 1)]
theorem atom0529Coded_decode : atom0529 = SparsePolynomial.decodeCubic 18 atom0529Coded := by decide +kernel
theorem atom0529Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded) := by
  have h := atom0529_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0529Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0530 : SparsePolynomial.Poly := [([2,12,13], 1)]
theorem eval_atom0530 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0530 = ((g 2) * (g 12) * (g 13)) := by
  norm_num [atom0530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0530_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10721894400 : Int) atom0530) := by
  rw [SparsePolynomial.eval_scale, eval_atom0530]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0530Coded : CoefficientMerge.Poly := [(877, 1)]
theorem atom0530Coded_decode : atom0530 = SparsePolynomial.decodeCubic 18 atom0530Coded := by decide +kernel
theorem atom0530Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) := by
  have h := atom0530_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0530Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0531 : SparsePolynomial.Poly := [([2,12,14], 1)]
theorem eval_atom0531 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0531 = ((g 2) * (g 12) * (g 14)) := by
  norm_num [atom0531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0531_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15248311200 : Int) atom0531) := by
  rw [SparsePolynomial.eval_scale, eval_atom0531]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0531Coded : CoefficientMerge.Poly := [(878, 1)]
theorem atom0531Coded_decode : atom0531 = SparsePolynomial.decodeCubic 18 atom0531Coded := by decide +kernel
theorem atom0531Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded) := by
  have h := atom0531_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0531Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0532 : SparsePolynomial.Poly := [([2,12,15], 1)]
theorem eval_atom0532 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0532 = ((g 2) * (g 12) * (g 15)) := by
  norm_num [atom0532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0532_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13098516480 : Int) atom0532) := by
  rw [SparsePolynomial.eval_scale, eval_atom0532]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0532Coded : CoefficientMerge.Poly := [(879, 1)]
theorem atom0532Coded_decode : atom0532 = SparsePolynomial.decodeCubic 18 atom0532Coded := by decide +kernel
theorem atom0532Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) := by
  have h := atom0532_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0532Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0533 : SparsePolynomial.Poly := [([2,12,16], 1)]
theorem eval_atom0533 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0533 = ((g 2) * (g 12) * (g 16)) := by
  norm_num [atom0533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0533_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7930137600 : Int) atom0533) := by
  rw [SparsePolynomial.eval_scale, eval_atom0533]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0533Coded : CoefficientMerge.Poly := [(880, 1)]
theorem atom0533Coded_decode : atom0533 = SparsePolynomial.decodeCubic 18 atom0533Coded := by decide +kernel
theorem atom0533Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) := by
  have h := atom0533_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0533Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0534 : SparsePolynomial.Poly := [([2,12,17], 1)]
theorem eval_atom0534 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0534 = ((g 2) * (g 12) * (g 17)) := by
  norm_num [atom0534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0534_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12465129600 : Int) atom0534) := by
  rw [SparsePolynomial.eval_scale, eval_atom0534]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0534Coded : CoefficientMerge.Poly := [(881, 1)]
theorem atom0534Coded_decode : atom0534 = SparsePolynomial.decodeCubic 18 atom0534Coded := by decide +kernel
theorem atom0534Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded) := by
  have h := atom0534_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0534Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0535 : SparsePolynomial.Poly := [([2,13,13], 1)]
theorem eval_atom0535 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0535 = ((g 2) * (g 13) * (g 13)) := by
  norm_num [atom0535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0535_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4665765888 : Int) atom0535) := by
  rw [SparsePolynomial.eval_scale, eval_atom0535]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0535Coded : CoefficientMerge.Poly := [(895, 1)]
theorem atom0535Coded_decode : atom0535 = SparsePolynomial.decodeCubic 18 atom0535Coded := by decide +kernel
theorem atom0535Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) := by
  have h := atom0535_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0535Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0536 : SparsePolynomial.Poly := [([2,13,14], 1)]
theorem eval_atom0536 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0536 = ((g 2) * (g 13) * (g 14)) := by
  norm_num [atom0536, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0536_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12464877240 : Int) atom0536) := by
  rw [SparsePolynomial.eval_scale, eval_atom0536]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0536Coded : CoefficientMerge.Poly := [(896, 1)]
theorem atom0536Coded_decode : atom0536 = SparsePolynomial.decodeCubic 18 atom0536Coded := by decide +kernel
theorem atom0536Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded) := by
  have h := atom0536_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0536Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0537 : SparsePolynomial.Poly := [([2,13,15], 1)]
theorem eval_atom0537 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0537 = ((g 2) * (g 13) * (g 15)) := by
  norm_num [atom0537, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0537_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12188897280 : Int) atom0537) := by
  rw [SparsePolynomial.eval_scale, eval_atom0537]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0537Coded : CoefficientMerge.Poly := [(897, 1)]
theorem atom0537Coded_decode : atom0537 = SparsePolynomial.decodeCubic 18 atom0537Coded := by decide +kernel
theorem atom0537Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) := by
  have h := atom0537_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0537Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0538 : SparsePolynomial.Poly := [([2,13,16], 1)]
theorem eval_atom0538 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0538 = ((g 2) * (g 13) * (g 16)) := by
  norm_num [atom0538, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0538_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8198184960 : Int) atom0538) := by
  rw [SparsePolynomial.eval_scale, eval_atom0538]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0538Coded : CoefficientMerge.Poly := [(898, 1)]
theorem atom0538Coded_decode : atom0538 = SparsePolynomial.decodeCubic 18 atom0538Coded := by decide +kernel
theorem atom0538Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) := by
  have h := atom0538_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0538Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0539 : SparsePolynomial.Poly := [([2,13,17], 1)]
theorem eval_atom0539 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0539 = ((g 2) * (g 13) * (g 17)) := by
  norm_num [atom0539, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0539_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9925534080 : Int) atom0539) := by
  rw [SparsePolynomial.eval_scale, eval_atom0539]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0539Coded : CoefficientMerge.Poly := [(899, 1)]
theorem atom0539Coded_decode : atom0539 = SparsePolynomial.decodeCubic 18 atom0539Coded := by decide +kernel
theorem atom0539Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded) := by
  have h := atom0539_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0539Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0540 : SparsePolynomial.Poly := [([2,14,14], 1)]
theorem eval_atom0540 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0540 = ((g 2) * (g 14) * (g 14)) := by
  norm_num [atom0540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0540_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8286435000 : Int) atom0540) := by
  rw [SparsePolynomial.eval_scale, eval_atom0540]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0540Coded : CoefficientMerge.Poly := [(914, 1)]
theorem atom0540Coded_decode : atom0540 = SparsePolynomial.decodeCubic 18 atom0540Coded := by decide +kernel
theorem atom0540Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) := by
  have h := atom0540_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0540Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0541 : SparsePolynomial.Poly := [([2,14,15], 1)]
theorem eval_atom0541 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0541 = ((g 2) * (g 14) * (g 15)) := by
  norm_num [atom0541, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0541_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12894527160 : Int) atom0541) := by
  rw [SparsePolynomial.eval_scale, eval_atom0541]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0541Coded : CoefficientMerge.Poly := [(915, 1)]
theorem atom0541Coded_decode : atom0541 = SparsePolynomial.decodeCubic 18 atom0541Coded := by decide +kernel
theorem atom0541Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded) := by
  have h := atom0541_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0541Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0542 : SparsePolynomial.Poly := [([2,14,16], 1)]
theorem eval_atom0542 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0542 = ((g 2) * (g 14) * (g 16)) := by
  norm_num [atom0542, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0542_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8358624720 : Int) atom0542) := by
  rw [SparsePolynomial.eval_scale, eval_atom0542]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0542Coded : CoefficientMerge.Poly := [(916, 1)]
theorem atom0542Coded_decode : atom0542 = SparsePolynomial.decodeCubic 18 atom0542Coded := by decide +kernel
theorem atom0542Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) := by
  have h := atom0542_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0542Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0543 : SparsePolynomial.Poly := [([2,14,17], 1)]
theorem eval_atom0543 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0543 = ((g 2) * (g 14) * (g 17)) := by
  norm_num [atom0543, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0543_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10676419920 : Int) atom0543) := by
  rw [SparsePolynomial.eval_scale, eval_atom0543]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0543Coded : CoefficientMerge.Poly := [(917, 1)]
theorem atom0543Coded_decode : atom0543 = SparsePolynomial.decodeCubic 18 atom0543Coded := by decide +kernel
theorem atom0543Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) := by
  have h := atom0543_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0543Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0544 : SparsePolynomial.Poly := [([2,15,15], 1)]
theorem eval_atom0544 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0544 = ((g 2) * (g 15) * (g 15)) := by
  norm_num [atom0544, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0544_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4296499200 : Int) atom0544) := by
  rw [SparsePolynomial.eval_scale, eval_atom0544]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0544Coded : CoefficientMerge.Poly := [(933, 1)]
theorem atom0544Coded_decode : atom0544 = SparsePolynomial.decodeCubic 18 atom0544Coded := by decide +kernel
theorem atom0544Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded) := by
  have h := atom0544_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0544Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0545 : SparsePolynomial.Poly := [([2,15,16], 1)]
theorem eval_atom0545 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0545 = ((g 2) * (g 15) * (g 16)) := by
  norm_num [atom0545, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0545_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5555934720 : Int) atom0545) := by
  rw [SparsePolynomial.eval_scale, eval_atom0545]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0545Coded : CoefficientMerge.Poly := [(934, 1)]
theorem atom0545Coded_decode : atom0545 = SparsePolynomial.decodeCubic 18 atom0545Coded := by decide +kernel
theorem atom0545Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) := by
  have h := atom0545_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0545Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0546 : SparsePolynomial.Poly := [([2,15,17], 1)]
theorem eval_atom0546 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0546 = ((g 2) * (g 15) * (g 17)) := by
  norm_num [atom0546, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0546_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8244432000 : Int) atom0546) := by
  rw [SparsePolynomial.eval_scale, eval_atom0546]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0546Coded : CoefficientMerge.Poly := [(935, 1)]
theorem atom0546Coded_decode : atom0546 = SparsePolynomial.decodeCubic 18 atom0546Coded := by decide +kernel
theorem atom0546Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded) := by
  have h := atom0546_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0546Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0547 : SparsePolynomial.Poly := [([2,16,16], 1)]
theorem eval_atom0547 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0547 = ((g 2) * (g 16) * (g 16)) := by
  norm_num [atom0547, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0547_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (572866560 : Int) atom0547) := by
  rw [SparsePolynomial.eval_scale, eval_atom0547]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0547Coded : CoefficientMerge.Poly := [(952, 1)]
theorem atom0547Coded_decode : atom0547 = SparsePolynomial.decodeCubic 18 atom0547Coded := by decide +kernel
theorem atom0547Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (572866560 : Int) atom0547Coded) := by
  have h := atom0547_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0547Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0548 : SparsePolynomial.Poly := [([2,16,17], 1)]
theorem eval_atom0548 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0548 = ((g 2) * (g 16) * (g 17)) := by
  norm_num [atom0548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0548_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3862212480 : Int) atom0548) := by
  rw [SparsePolynomial.eval_scale, eval_atom0548]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0548Coded : CoefficientMerge.Poly := [(953, 1)]
theorem atom0548Coded_decode : atom0548 = SparsePolynomial.decodeCubic 18 atom0548Coded := by decide +kernel
theorem atom0548Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) := by
  have h := atom0548_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0548Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0549 : SparsePolynomial.Poly := [([2,17,17], 1)]
theorem eval_atom0549 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0549 = ((g 2) * (g 17) * (g 17)) := by
  norm_num [atom0549, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0549_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2854776960 : Int) atom0549) := by
  rw [SparsePolynomial.eval_scale, eval_atom0549]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0549Coded : CoefficientMerge.Poly := [(971, 1)]
theorem atom0549Coded_decode : atom0549 = SparsePolynomial.decodeCubic 18 atom0549Coded := by decide +kernel
theorem atom0549Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded) := by
  have h := atom0549_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0549Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0550 : SparsePolynomial.Poly := [([3,3,3], 1)]
theorem eval_atom0550 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0550 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0550, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0550_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (249016320 : Int) atom0550) := by
  rw [SparsePolynomial.eval_scale, eval_atom0550]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0550Coded : CoefficientMerge.Poly := [(1029, 1)]
theorem atom0550Coded_decode : atom0550 = SparsePolynomial.decodeCubic 18 atom0550Coded := by decide +kernel
theorem atom0550Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (249016320 : Int) atom0550Coded) := by
  have h := atom0550_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0550Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0551 : SparsePolynomial.Poly := [([3,3,4], 1)]
theorem eval_atom0551 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0551 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom0551, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0551_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (633507840 : Int) atom0551) := by
  rw [SparsePolynomial.eval_scale, eval_atom0551]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0551Coded : CoefficientMerge.Poly := [(1030, 1)]
theorem atom0551Coded_decode : atom0551 = SparsePolynomial.decodeCubic 18 atom0551Coded := by decide +kernel
theorem atom0551Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (633507840 : Int) atom0551Coded) := by
  have h := atom0551_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0551Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0552 : SparsePolynomial.Poly := [([3,3,5], 1)]
theorem eval_atom0552 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0552 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom0552, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0552_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (519966720 : Int) atom0552) := by
  rw [SparsePolynomial.eval_scale, eval_atom0552]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0552Coded : CoefficientMerge.Poly := [(1031, 1)]
theorem atom0552Coded_decode : atom0552 = SparsePolynomial.decodeCubic 18 atom0552Coded := by decide +kernel
theorem atom0552Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (519966720 : Int) atom0552Coded) := by
  have h := atom0552_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0552Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0553 : SparsePolynomial.Poly := [([3,3,6], 1)]
theorem eval_atom0553 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0553 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom0553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0553_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (406425600 : Int) atom0553) := by
  rw [SparsePolynomial.eval_scale, eval_atom0553]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0553Coded : CoefficientMerge.Poly := [(1032, 1)]
theorem atom0553Coded_decode : atom0553 = SparsePolynomial.decodeCubic 18 atom0553Coded := by decide +kernel
theorem atom0553Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (406425600 : Int) atom0553Coded) := by
  have h := atom0553_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0553Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0554 : SparsePolynomial.Poly := [([3,3,7], 1)]
theorem eval_atom0554 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0554 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom0554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0554_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (292884480 : Int) atom0554) := by
  rw [SparsePolynomial.eval_scale, eval_atom0554]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0554Coded : CoefficientMerge.Poly := [(1033, 1)]
theorem atom0554Coded_decode : atom0554 = SparsePolynomial.decodeCubic 18 atom0554Coded := by decide +kernel
theorem atom0554Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (292884480 : Int) atom0554Coded) := by
  have h := atom0554_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0554Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0555 : SparsePolynomial.Poly := [([3,3,8], 1)]
theorem eval_atom0555 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0555 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom0555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0555_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230576640 : Int) atom0555) := by
  rw [SparsePolynomial.eval_scale, eval_atom0555]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0555Coded : CoefficientMerge.Poly := [(1034, 1)]
theorem atom0555Coded_decode : atom0555 = SparsePolynomial.decodeCubic 18 atom0555Coded := by decide +kernel
theorem atom0555Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (230576640 : Int) atom0555Coded) := by
  have h := atom0555_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0555Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0556 : SparsePolynomial.Poly := [([3,3,9], 1)]
theorem eval_atom0556 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0556 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom0556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0556_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108003840 : Int) atom0556) := by
  rw [SparsePolynomial.eval_scale, eval_atom0556]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0556Coded : CoefficientMerge.Poly := [(1035, 1)]
theorem atom0556Coded_decode : atom0556 = SparsePolynomial.decodeCubic 18 atom0556Coded := by decide +kernel
theorem atom0556Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (108003840 : Int) atom0556Coded) := by
  have h := atom0556_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0556Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0557 : SparsePolynomial.Poly := [([3,3,10], 1)]
theorem eval_atom0557 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0557 = ((g 3) * (g 3) * (g 10)) := by
  norm_num [atom0557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0557_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10590720 : Int) atom0557) := by
  rw [SparsePolynomial.eval_scale, eval_atom0557]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0557Coded : CoefficientMerge.Poly := [(1036, 1)]
theorem atom0557Coded_decode : atom0557 = SparsePolynomial.decodeCubic 18 atom0557Coded := by decide +kernel
theorem atom0557Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10590720 : Int) atom0557Coded) := by
  have h := atom0557_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0557Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0558 : SparsePolynomial.Poly := [([3,3,12], 1)]
theorem eval_atom0558 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0558 = ((g 3) * (g 3) * (g 12)) := by
  norm_num [atom0558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0558_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1501839360 : Int) atom0558) := by
  rw [SparsePolynomial.eval_scale, eval_atom0558]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0558Coded : CoefficientMerge.Poly := [(1038, 1)]
theorem atom0558Coded_decode : atom0558 = SparsePolynomial.decodeCubic 18 atom0558Coded := by decide +kernel
theorem atom0558Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) := by
  have h := atom0558_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0558Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0559 : SparsePolynomial.Poly := [([3,3,14], 1)]
theorem eval_atom0559 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0559 = ((g 3) * (g 3) * (g 14)) := by
  norm_num [atom0559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0559_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1167149520 : Int) atom0559) := by
  rw [SparsePolynomial.eval_scale, eval_atom0559]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0559Coded : CoefficientMerge.Poly := [(1040, 1)]
theorem atom0559Coded_decode : atom0559 = SparsePolynomial.decodeCubic 18 atom0559Coded := by decide +kernel
theorem atom0559Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded) := by
  have h := atom0559_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0559Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0560 : SparsePolynomial.Poly := [([3,4,4], 1)]
theorem eval_atom0560 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0560 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom0560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0560_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1344806400 : Int) atom0560) := by
  rw [SparsePolynomial.eval_scale, eval_atom0560]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0560Coded : CoefficientMerge.Poly := [(1048, 1)]
theorem atom0560Coded_decode : atom0560 = SparsePolynomial.decodeCubic 18 atom0560Coded := by decide +kernel
theorem atom0560Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) := by
  have h := atom0560_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0560Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0561 : SparsePolynomial.Poly := [([3,4,5], 1)]
theorem eval_atom0561 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0561 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0561_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1764439680 : Int) atom0561) := by
  rw [SparsePolynomial.eval_scale, eval_atom0561]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0561Coded : CoefficientMerge.Poly := [(1049, 1)]
theorem atom0561Coded_decode : atom0561 = SparsePolynomial.decodeCubic 18 atom0561Coded := by decide +kernel
theorem atom0561Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded) := by
  have h := atom0561_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0561Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0562 : SparsePolynomial.Poly := [([3,4,6], 1)]
theorem eval_atom0562 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0562 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0562_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (766439040 : Int) atom0562) := by
  rw [SparsePolynomial.eval_scale, eval_atom0562]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0562Coded : CoefficientMerge.Poly := [(1050, 1)]
theorem atom0562Coded_decode : atom0562 = SparsePolynomial.decodeCubic 18 atom0562Coded := by decide +kernel
theorem atom0562Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (766439040 : Int) atom0562Coded) := by
  have h := atom0562_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0562Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0563 : SparsePolynomial.Poly := [([3,4,7], 1)]
theorem eval_atom0563 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0563 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0563_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245414400 : Int) atom0563) := by
  rw [SparsePolynomial.eval_scale, eval_atom0563]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0563Coded : CoefficientMerge.Poly := [(1051, 1)]
theorem atom0563Coded_decode : atom0563 = SparsePolynomial.decodeCubic 18 atom0563Coded := by decide +kernel
theorem atom0563Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (245414400 : Int) atom0563Coded) := by
  have h := atom0563_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0563Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0564 : SparsePolynomial.Poly := [([3,4,8], 1)]
theorem eval_atom0564 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0564 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0564_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208266240 : Int) atom0564) := by
  rw [SparsePolynomial.eval_scale, eval_atom0564]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0564Coded : CoefficientMerge.Poly := [(1052, 1)]
theorem atom0564Coded_decode : atom0564 = SparsePolynomial.decodeCubic 18 atom0564Coded := by decide +kernel
theorem atom0564Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (208266240 : Int) atom0564Coded) := by
  have h := atom0564_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0564Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0565 : SparsePolynomial.Poly := [([3,4,9], 1)]
theorem eval_atom0565 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0565 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom0565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0565_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164398080 : Int) atom0565) := by
  rw [SparsePolynomial.eval_scale, eval_atom0565]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0565Coded : CoefficientMerge.Poly := [(1053, 1)]
theorem atom0565Coded_decode : atom0565 = SparsePolynomial.decodeCubic 18 atom0565Coded := by decide +kernel
theorem atom0565Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (164398080 : Int) atom0565Coded) := by
  have h := atom0565_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0565Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0566 : SparsePolynomial.Poly := [([3,4,10], 1)]
theorem eval_atom0566 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0566 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom0566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0566_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170849280 : Int) atom0566) := by
  rw [SparsePolynomial.eval_scale, eval_atom0566]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0566Coded : CoefficientMerge.Poly := [(1054, 1)]
theorem atom0566Coded_decode : atom0566 = SparsePolynomial.decodeCubic 18 atom0566Coded := by decide +kernel
theorem atom0566Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (170849280 : Int) atom0566Coded) := by
  have h := atom0566_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0566Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0567 : SparsePolynomial.Poly := [([3,4,11], 1)]
theorem eval_atom0567 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0567 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom0567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0567_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264122880 : Int) atom0567) := by
  rw [SparsePolynomial.eval_scale, eval_atom0567]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0567Coded : CoefficientMerge.Poly := [(1055, 1)]
theorem atom0567Coded_decode : atom0567 = SparsePolynomial.decodeCubic 18 atom0567Coded := by decide +kernel
theorem atom0567Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (264122880 : Int) atom0567Coded) := by
  have h := atom0567_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0567Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0568 : SparsePolynomial.Poly := [([3,4,12], 1)]
theorem eval_atom0568 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0568 = ((g 3) * (g 4) * (g 12)) := by
  norm_num [atom0568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0568_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3555901440 : Int) atom0568) := by
  rw [SparsePolynomial.eval_scale, eval_atom0568]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0568Coded : CoefficientMerge.Poly := [(1056, 1)]
theorem atom0568Coded_decode : atom0568 = SparsePolynomial.decodeCubic 18 atom0568Coded := by decide +kernel
theorem atom0568Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) := by
  have h := atom0568_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0568Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0569 : SparsePolynomial.Poly := [([3,4,13], 1)]
theorem eval_atom0569 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0569 = ((g 3) * (g 4) * (g 13)) := by
  norm_num [atom0569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0569_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (936962880 : Int) atom0569) := by
  rw [SparsePolynomial.eval_scale, eval_atom0569]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0569Coded : CoefficientMerge.Poly := [(1057, 1)]
theorem atom0569Coded_decode : atom0569 = SparsePolynomial.decodeCubic 18 atom0569Coded := by decide +kernel
theorem atom0569Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (936962880 : Int) atom0569Coded) := by
  have h := atom0569_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0569Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0570 : SparsePolynomial.Poly := [([3,4,14], 1)]
theorem eval_atom0570 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0570 = ((g 3) * (g 4) * (g 14)) := by
  norm_num [atom0570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0570_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3289076640 : Int) atom0570) := by
  rw [SparsePolynomial.eval_scale, eval_atom0570]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0570Coded : CoefficientMerge.Poly := [(1058, 1)]
theorem atom0570Coded_decode : atom0570 = SparsePolynomial.decodeCubic 18 atom0570Coded := by decide +kernel
theorem atom0570Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) := by
  have h := atom0570_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0570Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0571 : SparsePolynomial.Poly := [([3,4,15], 1)]
theorem eval_atom0571 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0571 = ((g 3) * (g 4) * (g 15)) := by
  norm_num [atom0571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0571_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2074914240 : Int) atom0571) := by
  rw [SparsePolynomial.eval_scale, eval_atom0571]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0571Coded : CoefficientMerge.Poly := [(1059, 1)]
theorem atom0571Coded_decode : atom0571 = SparsePolynomial.decodeCubic 18 atom0571Coded := by decide +kernel
theorem atom0571Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded) := by
  have h := atom0571_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0571Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0572 : SparsePolynomial.Poly := [([3,4,16], 1)]
theorem eval_atom0572 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0572 = ((g 3) * (g 4) * (g 16)) := by
  norm_num [atom0572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0572_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2798927040 : Int) atom0572) := by
  rw [SparsePolynomial.eval_scale, eval_atom0572]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0572Coded : CoefficientMerge.Poly := [(1060, 1)]
theorem atom0572Coded_decode : atom0572 = SparsePolynomial.decodeCubic 18 atom0572Coded := by decide +kernel
theorem atom0572Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) := by
  have h := atom0572_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0572Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0573 : SparsePolynomial.Poly := [([3,4,17], 1)]
theorem eval_atom0573 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0573 = ((g 3) * (g 4) * (g 17)) := by
  norm_num [atom0573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0573_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3522939840 : Int) atom0573) := by
  rw [SparsePolynomial.eval_scale, eval_atom0573]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0573Coded : CoefficientMerge.Poly := [(1061, 1)]
theorem atom0573Coded_decode : atom0573 = SparsePolynomial.decodeCubic 18 atom0573Coded := by decide +kernel
theorem atom0573Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) := by
  have h := atom0573_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0573Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0574 : SparsePolynomial.Poly := [([3,5,5], 1)]
theorem eval_atom0574 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0574 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0574_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1300867200 : Int) atom0574) := by
  rw [SparsePolynomial.eval_scale, eval_atom0574]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0574Coded : CoefficientMerge.Poly := [(1067, 1)]
theorem atom0574Coded_decode : atom0574 = SparsePolynomial.decodeCubic 18 atom0574Coded := by decide +kernel
theorem atom0574Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded) := by
  have h := atom0574_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0574Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block007 : CoefficientMerge.Poly := [(800, 3718671360), (801, 6793720320), (802, 6517608960), (803, 6167040000), (804, 7979381760), (805, 6566323200), (806, 8933124000), (807, 7949368320), (808, 8692055040), (809, 10609182720), (819, 4164011520), (820, 7503144960), (821, 6954524160), (822, 8592628800), (823, 7029147840), (824, 9631143840), (825, 8158977600), (826, 8798871360), (827, 10613206080), (838, 4531960320), (839, 7932940800), (840, 9311655360), (841, 7477765440), (842, 10379483040), (843, 8044739520), (844, 8392186560), (845, 10204830720), (857, 4927426560), (858, 9870336000), (859, 7722086400), (860, 10978907040), (861, 8678154240), (862, 7662090240), (863, 11373788160), (876, 6543452160), (877, 10721894400), (878, 15248311200), (879, 13098516480), (880, 7930137600), (881, 12465129600), (895, 4665765888), (896, 12464877240), (897, 12188897280), (898, 8198184960), (899, 9925534080), (914, 8286435000), (915, 12894527160), (916, 8358624720), (917, 10676419920), (933, 4296499200), (934, 5555934720), (935, 8244432000), (952, 572866560), (953, 3862212480), (971, 2854776960), (1029, 249016320), (1030, 633507840), (1031, 519966720), (1032, 406425600), (1033, 292884480), (1034, 230576640), (1035, 108003840), (1036, 10590720), (1038, 1501839360), (1040, 1167149520), (1048, 1344806400), (1049, 1764439680), (1050, 766439040), (1051, 245414400), (1052, 208266240), (1053, 164398080), (1054, 170849280), (1055, 264122880), (1056, 3555901440), (1057, 936962880), (1058, 3289076640), (1059, 2074914240), (1060, 2798927040), (1061, 3522939840), (1067, 1300867200)]
theorem block007_data : block007 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572866560 : Int) atom0547Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249016320 : Int) atom0550Coded) (CoefficientMerge.scale (633507840 : Int) atom0551Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519966720 : Int) atom0552Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230576640 : Int) atom0555Coded) (CoefficientMerge.scale (108003840 : Int) atom0556Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10590720 : Int) atom0557Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (766439040 : Int) atom0562Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164398080 : Int) atom0565Coded) (CoefficientMerge.scale (170849280 : Int) atom0566Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264122880 : Int) atom0567Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded)))))))) := by decide +kernel
theorem block007_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block007 := by
  rw [block007_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0495Coded_nonneg g hg hA hB) (atom0496Coded_nonneg g hg hA hB)) (add_nonneg (atom0497Coded_nonneg g hg hA hB) (add_nonneg (atom0498Coded_nonneg g hg hA hB) (atom0499Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0500Coded_nonneg g hg hA hB) (atom0501Coded_nonneg g hg hA hB)) (add_nonneg (atom0502Coded_nonneg g hg hA hB) (add_nonneg (atom0503Coded_nonneg g hg hA hB) (atom0504Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0505Coded_nonneg g hg hA hB) (atom0506Coded_nonneg g hg hA hB)) (add_nonneg (atom0507Coded_nonneg g hg hA hB) (add_nonneg (atom0508Coded_nonneg g hg hA hB) (atom0509Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0510Coded_nonneg g hg hA hB) (atom0511Coded_nonneg g hg hA hB)) (add_nonneg (atom0512Coded_nonneg g hg hA hB) (add_nonneg (atom0513Coded_nonneg g hg hA hB) (atom0514Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0515Coded_nonneg g hg hA hB) (atom0516Coded_nonneg g hg hA hB)) (add_nonneg (atom0517Coded_nonneg g hg hA hB) (add_nonneg (atom0518Coded_nonneg g hg hA hB) (atom0519Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0520Coded_nonneg g hg hA hB) (atom0521Coded_nonneg g hg hA hB)) (add_nonneg (atom0522Coded_nonneg g hg hA hB) (add_nonneg (atom0523Coded_nonneg g hg hA hB) (atom0524Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0525Coded_nonneg g hg hA hB) (atom0526Coded_nonneg g hg hA hB)) (add_nonneg (atom0527Coded_nonneg g hg hA hB) (add_nonneg (atom0528Coded_nonneg g hg hA hB) (atom0529Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0530Coded_nonneg g hg hA hB) (atom0531Coded_nonneg g hg hA hB)) (add_nonneg (atom0532Coded_nonneg g hg hA hB) (add_nonneg (atom0533Coded_nonneg g hg hA hB) (atom0534Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0535Coded_nonneg g hg hA hB) (atom0536Coded_nonneg g hg hA hB)) (add_nonneg (atom0537Coded_nonneg g hg hA hB) (add_nonneg (atom0538Coded_nonneg g hg hA hB) (atom0539Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0540Coded_nonneg g hg hA hB) (atom0541Coded_nonneg g hg hA hB)) (add_nonneg (atom0542Coded_nonneg g hg hA hB) (add_nonneg (atom0543Coded_nonneg g hg hA hB) (atom0544Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0545Coded_nonneg g hg hA hB) (atom0546Coded_nonneg g hg hA hB)) (add_nonneg (atom0547Coded_nonneg g hg hA hB) (add_nonneg (atom0548Coded_nonneg g hg hA hB) (atom0549Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0550Coded_nonneg g hg hA hB) (atom0551Coded_nonneg g hg hA hB)) (add_nonneg (atom0552Coded_nonneg g hg hA hB) (add_nonneg (atom0553Coded_nonneg g hg hA hB) (atom0554Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0555Coded_nonneg g hg hA hB) (atom0556Coded_nonneg g hg hA hB)) (add_nonneg (atom0557Coded_nonneg g hg hA hB) (add_nonneg (atom0558Coded_nonneg g hg hA hB) (atom0559Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0560Coded_nonneg g hg hA hB) (atom0561Coded_nonneg g hg hA hB)) (add_nonneg (atom0562Coded_nonneg g hg hA hB) (add_nonneg (atom0563Coded_nonneg g hg hA hB) (atom0564Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0565Coded_nonneg g hg hA hB) (atom0566Coded_nonneg g hg hA hB)) (add_nonneg (atom0567Coded_nonneg g hg hA hB) (add_nonneg (atom0568Coded_nonneg g hg hA hB) (atom0569Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0570Coded_nonneg g hg hA hB) (atom0571Coded_nonneg g hg hA hB)) (add_nonneg (atom0572Coded_nonneg g hg hA hB) (add_nonneg (atom0573Coded_nonneg g hg hA hB) (atom0574Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
