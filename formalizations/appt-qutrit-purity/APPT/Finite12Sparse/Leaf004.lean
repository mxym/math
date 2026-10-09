import APPT.Finite12Sparse.Base00
import APPT.Finite12Sparse.Base01
import APPT.Finite12Sparse.Base02
import APPT.Finite12Sparse.Base03
import APPT.Finite12Sparse.Base04
import APPT.Finite12Sparse.Base05
import APPT.Finite12Sparse.Base06
import APPT.Finite12Sparse.Base07
import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def atom0320 : SparsePolynomial.Poly := [([8,9,11], 1)]
theorem eval_atom0320 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0320 = ((g 8) * (g 9) * (g 11)) := by
  norm_num [atom0320, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0320_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225024 : Int) atom0320) := by
  rw [SparsePolynomial.eval_scale, eval_atom0320]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0320Coded : CoefficientMerge.Poly := [(1271, 1)]
theorem atom0320Coded_decode : atom0320 = SparsePolynomial.decodeCubic 12 atom0320Coded := by decide +kernel
theorem atom0320Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (225024 : Int) atom0320Coded) := by
  have h := atom0320_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0320Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0321 : SparsePolynomial.Poly := [([8,10,10], 1)]
theorem eval_atom0321 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0321 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom0321, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0321_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171072 : Int) atom0321) := by
  rw [SparsePolynomial.eval_scale, eval_atom0321]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0321Coded : CoefficientMerge.Poly := [(1282, 1)]
theorem atom0321Coded_decode : atom0321 = SparsePolynomial.decodeCubic 12 atom0321Coded := by decide +kernel
theorem atom0321Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (171072 : Int) atom0321Coded) := by
  have h := atom0321_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0321Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0322 : SparsePolynomial.Poly := [([8,10,11], 1)]
theorem eval_atom0322 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0322 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom0322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0322_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (290688 : Int) atom0322) := by
  rw [SparsePolynomial.eval_scale, eval_atom0322]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0322Coded : CoefficientMerge.Poly := [(1283, 1)]
theorem atom0322Coded_decode : atom0322 = SparsePolynomial.decodeCubic 12 atom0322Coded := by decide +kernel
theorem atom0322Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (290688 : Int) atom0322Coded) := by
  have h := atom0322_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0322Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0323 : SparsePolynomial.Poly := [([8,11,11], 1)]
theorem eval_atom0323 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0323 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom0323, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0323_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90240 : Int) atom0323) := by
  rw [SparsePolynomial.eval_scale, eval_atom0323]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0323Coded : CoefficientMerge.Poly := [(1295, 1)]
theorem atom0323Coded_decode : atom0323 = SparsePolynomial.decodeCubic 12 atom0323Coded := by decide +kernel
theorem atom0323Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (90240 : Int) atom0323Coded) := by
  have h := atom0323_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0323Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0324 : SparsePolynomial.Poly := [([9,9,9], 1)]
theorem eval_atom0324 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0324 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom0324, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0324_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47616 : Int) atom0324) := by
  rw [SparsePolynomial.eval_scale, eval_atom0324]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0324Coded : CoefficientMerge.Poly := [(1413, 1)]
theorem atom0324Coded_decode : atom0324 = SparsePolynomial.decodeCubic 12 atom0324Coded := by decide +kernel
theorem atom0324Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (47616 : Int) atom0324Coded) := by
  have h := atom0324_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0324Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0325 : SparsePolynomial.Poly := [([9,9,10], 1)]
theorem eval_atom0325 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0325 = ((g 9) * (g 9) * (g 10)) := by
  norm_num [atom0325, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0325_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163776 : Int) atom0325) := by
  rw [SparsePolynomial.eval_scale, eval_atom0325]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0325Coded : CoefficientMerge.Poly := [(1414, 1)]
theorem atom0325Coded_decode : atom0325 = SparsePolynomial.decodeCubic 12 atom0325Coded := by decide +kernel
theorem atom0325Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (163776 : Int) atom0325Coded) := by
  have h := atom0325_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0325Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0326 : SparsePolynomial.Poly := [([9,9,11], 1)]
theorem eval_atom0326 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0326 = ((g 9) * (g 9) * (g 11)) := by
  norm_num [atom0326, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0326_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108672 : Int) atom0326) := by
  rw [SparsePolynomial.eval_scale, eval_atom0326]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0326Coded : CoefficientMerge.Poly := [(1415, 1)]
theorem atom0326Coded_decode : atom0326 = SparsePolynomial.decodeCubic 12 atom0326Coded := by decide +kernel
theorem atom0326Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (108672 : Int) atom0326Coded) := by
  have h := atom0326_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0326Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0327 : SparsePolynomial.Poly := [([9,10,10], 1)]
theorem eval_atom0327 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0327 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom0327, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0327_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (190080 : Int) atom0327) := by
  rw [SparsePolynomial.eval_scale, eval_atom0327]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0327Coded : CoefficientMerge.Poly := [(1426, 1)]
theorem atom0327Coded_decode : atom0327 = SparsePolynomial.decodeCubic 12 atom0327Coded := by decide +kernel
theorem atom0327Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (190080 : Int) atom0327Coded) := by
  have h := atom0327_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0327Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0328 : SparsePolynomial.Poly := [([9,10,11], 1)]
theorem eval_atom0328 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0328 = ((g 9) * (g 10) * (g 11)) := by
  norm_num [atom0328, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0328_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (298752 : Int) atom0328) := by
  rw [SparsePolynomial.eval_scale, eval_atom0328]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0328Coded : CoefficientMerge.Poly := [(1427, 1)]
theorem atom0328Coded_decode : atom0328 = SparsePolynomial.decodeCubic 12 atom0328Coded := by decide +kernel
theorem atom0328Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (298752 : Int) atom0328Coded) := by
  have h := atom0328_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0328Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0329 : SparsePolynomial.Poly := [([9,11,11], 1)]
theorem eval_atom0329 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0329 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom0329, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0329_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76032 : Int) atom0329) := by
  rw [SparsePolynomial.eval_scale, eval_atom0329]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0329Coded : CoefficientMerge.Poly := [(1439, 1)]
theorem atom0329Coded_decode : atom0329 = SparsePolynomial.decodeCubic 12 atom0329Coded := by decide +kernel
theorem atom0329Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (76032 : Int) atom0329Coded) := by
  have h := atom0329_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0329Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0330 : SparsePolynomial.Poly := [([10,10,10], 1)]
theorem eval_atom0330 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0330 = ((g 10) * (g 10) * (g 10)) := by
  norm_num [atom0330, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0330_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69696 : Int) atom0330) := by
  rw [SparsePolynomial.eval_scale, eval_atom0330]
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 10) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0330Coded : CoefficientMerge.Poly := [(1570, 1)]
theorem atom0330Coded_decode : atom0330 = SparsePolynomial.decodeCubic 12 atom0330Coded := by decide +kernel
theorem atom0330Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (69696 : Int) atom0330Coded) := by
  have h := atom0330_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0330Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0331 : SparsePolynomial.Poly := [([10,10,11], 1)]
theorem eval_atom0331 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0331 = ((g 10) * (g 10) * (g 11)) := by
  norm_num [atom0331, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0331_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179520 : Int) atom0331) := by
  rw [SparsePolynomial.eval_scale, eval_atom0331]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0331Coded : CoefficientMerge.Poly := [(1571, 1)]
theorem atom0331Coded_decode : atom0331 = SparsePolynomial.decodeCubic 12 atom0331Coded := by decide +kernel
theorem atom0331Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (179520 : Int) atom0331Coded) := by
  have h := atom0331_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0331Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0332 : SparsePolynomial.Poly := [([10,11,11], 1)]
theorem eval_atom0332 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0332 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom0332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0332_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114048 : Int) atom0332) := by
  rw [SparsePolynomial.eval_scale, eval_atom0332]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0332Coded : CoefficientMerge.Poly := [(1583, 1)]
theorem atom0332Coded_decode : atom0332 = SparsePolynomial.decodeCubic 12 atom0332Coded := by decide +kernel
theorem atom0332Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (114048 : Int) atom0332Coded) := by
  have h := atom0332_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0332Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0333 : SparsePolynomial.Poly := [([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,0,9], -2), ([0,0,10], -2), ([0,0,11], -2), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -6), ([0,1,7], -4), ([0,1,8], -4), ([0,1,9], -4), ([0,1,10], -4), ([0,1,11], -4), ([0,2,2], -2), ([0,2,3], -4), ([0,2,4], -4), ([0,2,5], -4), ([0,2,6], -8), ([0,2,7], -6), ([0,2,8], -4), ([0,2,9], -4), ([0,2,10], -4), ([0,2,11], -4), ([0,3,3], -2), ([0,3,4], -4), ([0,3,5], -4), ([0,3,6], -8), ([0,3,7], -6), ([0,3,8], -4), ([0,3,9], -4), ([0,3,10], -4), ([0,3,11], -4), ([0,4,4], -2), ([0,4,5], -4), ([0,4,6], -8), ([0,4,7], -6), ([0,4,8], -4), ([0,4,9], -4), ([0,4,10], -4), ([0,4,11], -4), ([0,5,5], -2), ([0,5,6], -8), ([0,5,7], -6), ([0,5,8], -4), ([0,5,9], -4), ([0,5,10], -4), ([0,5,11], -4), ([0,6,6], -6), ([0,6,7], -10), ([0,6,8], -8), ([0,6,9], -8), ([0,6,10], -4), ([0,6,11], -4), ([0,7,7], -4), ([0,7,8], -8), ([0,7,9], -8), ([0,7,10], -4), ([0,7,11], -4), ([0,8,8], -4), ([0,8,9], -8), ([0,8,10], -4), ([0,8,11], -4), ([0,9,9], -4), ([0,9,10], -4), ([0,9,11], -4), ([1,1,2], -2), ([1,1,3], -2), ([1,1,4], -2), ([1,1,5], -2), ([1,1,6], -4), ([1,1,7], -2), ([1,1,8], -2), ([1,1,9], -4), ([1,1,10], -4), ([1,1,11], -4), ([1,2,2], -4), ([1,2,3], -8), ([1,2,4], -8), ([1,2,5], -8), ([1,2,6], -12), ([1,2,7], -8), ([1,2,8], -6), ([1,2,9], -10), ([1,2,10], -8), ([1,2,11], -8), ([1,3,3], -4), ([1,3,4], -8), ([1,3,5], -8), ([1,3,6], -12), ([1,3,7], -8), ([1,3,8], -6), ([1,3,9], -10), ([1,3,10], -8), ([1,3,11], -8), ([1,4,4], -4), ([1,4,5], -8), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -6), ([1,4,9], -10), ([1,4,10], -8), ([1,4,11], -8), ([1,5,5], -4), ([1,5,6], -12), ([1,5,7], -8), ([1,5,8], -6), ([1,5,9], -10), ([1,5,10], -8), ([1,5,11], -8), ([1,6,6], -8), ([1,6,7], -12), ([1,6,8], -10), ([1,6,9], -14), ([1,6,10], -8), ([1,6,11], -8), ([1,7,7], -4), ([1,7,8], -8), ([1,7,9], -12), ([1,7,10], -8), ([1,7,11], -8), ([1,8,8], -4), ([1,8,9], -8), ([1,8,10], -4), ([1,8,11], -4), ([1,9,9], -4), ([1,9,10], -4), ([1,9,11], -4), ([2,2,2], -2), ([2,2,3], -6), ([2,2,4], -6), ([2,2,5], -6), ([2,2,6], -8), ([2,2,7], -6), ([2,2,8], -4), ([2,2,9], -6), ([2,2,10], -4), ([2,2,11], -6), ([2,3,3], -6), ([2,3,4], -12), ([2,3,5], -12), ([2,3,6], -16), ([2,3,7], -12), ([2,3,8], -8), ([2,3,9], -12), ([2,3,10], -8), ([2,3,11], -12), ([2,4,4], -6), ([2,4,5], -12), ([2,4,6], -16), ([2,4,7], -12), ([2,4,8], -8), ([2,4,9], -12), ([2,4,10], -8), ([2,4,11], -12), ([2,5,5], -6), ([2,5,6], -16), ([2,5,7], -12), ([2,5,8], -8), ([2,5,9], -12), ([2,5,10], -8), ([2,5,11], -12), ([2,6,6], -10), ([2,6,7], -16), ([2,6,8], -12), ([2,6,9], -16), ([2,6,10], -8), ([2,6,11], -12), ([2,7,7], -6), ([2,7,8], -10), ([2,7,9], -14), ([2,7,10], -8), ([2,7,11], -8), ([2,8,8], -4), ([2,8,9], -8), ([2,8,10], -4), ([2,8,11], -4), ([2,9,9], -4), ([2,9,10], -4), ([2,9,11], -4), ([3,3,3], -2), ([3,3,4], -6), ([3,3,5], -6), ([3,3,6], -8), ([3,3,7], -6), ([3,3,8], -4), ([3,3,9], -6), ([3,3,10], -4), ([3,3,11], -6), ([3,4,4], -6), ([3,4,5], -12), ([3,4,6], -16), ([3,4,7], -12), ([3,4,8], -8), ([3,4,9], -12), ([3,4,10], -8), ([3,4,11], -12), ([3,5,5], -6), ([3,5,6], -16), ([3,5,7], -12), ([3,5,8], -8), ([3,5,9], -12), ([3,5,10], -8), ([3,5,11], -12), ([3,6,6], -10), ([3,6,7], -16), ([3,6,8], -12), ([3,6,9], -16), ([3,6,10], -8), ([3,6,11], -12), ([3,7,7], -6), ([3,7,8], -10), ([3,7,9], -14), ([3,7,10], -8), ([3,7,11], -8), ([3,8,8], -4), ([3,8,9], -8), ([3,8,10], -4), ([3,8,11], -4), ([3,9,9], -4), ([3,9,10], -4), ([3,9,11], -4), ([4,4,4], -2), ([4,4,5], -6), ([4,4,6], -8), ([4,4,7], -6), ([4,4,8], -4), ([4,4,9], -6), ([4,4,10], -4), ([4,4,11], -6), ([4,5,5], -6), ([4,5,6], -16), ([4,5,7], -12), ([4,5,8], -8), ([4,5,9], -12), ([4,5,10], -8), ([4,5,11], -12), ([4,6,6], -10), ([4,6,7], -16), ([4,6,8], -12), ([4,6,9], -16), ([4,6,10], -8), ([4,6,11], -12), ([4,7,7], -6), ([4,7,8], -10), ([4,7,9], -14), ([4,7,10], -8), ([4,7,11], -8), ([4,8,8], -4), ([4,8,9], -8), ([4,8,10], -4), ([4,8,11], -4), ([4,9,9], -4), ([4,9,10], -4), ([4,9,11], -4), ([5,5,5], -2), ([5,5,6], -8), ([5,5,7], -6), ([5,5,8], -4), ([5,5,9], -6), ([5,5,10], -4), ([5,5,11], -6), ([5,6,6], -10), ([5,6,7], -16), ([5,6,8], -12), ([5,6,9], -16), ([5,6,10], -8), ([5,6,11], -12), ([5,7,7], -6), ([5,7,8], -10), ([5,7,9], -14), ([5,7,10], -8), ([5,7,11], -8), ([5,8,8], -4), ([5,8,9], -8), ([5,8,10], -4), ([5,8,11], -4), ([5,9,9], -4), ([5,9,10], -4), ([5,9,11], -4), ([6,6,6], -4), ([6,6,7], -10), ([6,6,8], -8), ([6,6,9], -10), ([6,6,10], -4), ([6,6,11], -6), ([6,7,7], -8), ([6,7,8], -14), ([6,7,9], -18), ([6,7,10], -8), ([6,7,11], -8), ([6,8,8], -6), ([6,8,9], -12), ([6,8,10], -4), ([6,8,11], -4), ([6,9,9], -6), ([6,9,10], -4), ([6,9,11], 4), ([6,10,11], 8), ([6,11,11], 8), ([7,7,7], -2), ([7,7,8], -6), ([7,7,9], -8), ([7,7,10], -4), ([7,7,11], -4), ([7,8,8], -6), ([7,8,9], -12), ([7,8,10], -4), ([7,8,11], -4), ([7,9,9], -6), ([7,9,10], -4), ([7,9,11], 4), ([7,10,11], 8), ([7,11,11], 8), ([8,8,8], -2), ([8,8,9], -6), ([8,8,10], -2), ([8,8,11], -2), ([8,9,9], -6), ([8,9,10], -4), ([8,9,11], 4), ([8,10,11], 8), ([8,11,11], 8), ([9,9,9], -2), ([9,9,10], -2), ([9,9,11], 6), ([9,10,11], 16), ([9,11,11], 16), ([10,10,11], 8), ([10,11,11], 16), ([11,11,11], 8)]
theorem atom0333_data : atom0333 = SparsePolynomial.monoTimes [] 1 base00 := by decide +kernel
theorem eval_atom0333 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0333 = (detA (outer g)) := by
  rw [atom0333_data, SparsePolynomial.eval_monoTimes, eval_base00]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0333_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6528 : Int) atom0333) := by
  rw [SparsePolynomial.eval_scale, eval_atom0333]
  have hb := base00_nonneg g hg hA hB
  rw [eval_base00] at hb
  have ht : 0 ≤ (detA (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0333Coded : CoefficientMerge.Poly := [(6, -2), (7, -2), (8, -2), (9, -2), (10, -2), (11, -2), (14, -2), (15, -2), (16, -2), (17, -2), (18, -6), (19, -4), (20, -4), (21, -4), (22, -4), (23, -4), (26, -2), (27, -4), (28, -4), (29, -4), (30, -8), (31, -6), (32, -4), (33, -4), (34, -4), (35, -4), (39, -2), (40, -4), (41, -4), (42, -8), (43, -6), (44, -4), (45, -4), (46, -4), (47, -4), (52, -2), (53, -4), (54, -8), (55, -6), (56, -4), (57, -4), (58, -4), (59, -4), (65, -2), (66, -8), (67, -6), (68, -4), (69, -4), (70, -4), (71, -4), (78, -6), (79, -10), (80, -8), (81, -8), (82, -4), (83, -4), (91, -4), (92, -8), (93, -8), (94, -4), (95, -4), (104, -4), (105, -8), (106, -4), (107, -4), (117, -4), (118, -4), (119, -4), (158, -2), (159, -2), (160, -2), (161, -2), (162, -4), (163, -2), (164, -2), (165, -4), (166, -4), (167, -4), (170, -4), (171, -8), (172, -8), (173, -8), (174, -12), (175, -8), (176, -6), (177, -10), (178, -8), (179, -8), (183, -4), (184, -8), (185, -8), (186, -12), (187, -8), (188, -6), (189, -10), (190, -8), (191, -8), (196, -4), (197, -8), (198, -12), (199, -8), (200, -6), (201, -10), (202, -8), (203, -8), (209, -4), (210, -12), (211, -8), (212, -6), (213, -10), (214, -8), (215, -8), (222, -8), (223, -12), (224, -10), (225, -14), (226, -8), (227, -8), (235, -4), (236, -8), (237, -12), (238, -8), (239, -8), (248, -4), (249, -8), (250, -4), (251, -4), (261, -4), (262, -4), (263, -4), (314, -2), (315, -6), (316, -6), (317, -6), (318, -8), (319, -6), (320, -4), (321, -6), (322, -4), (323, -6), (327, -6), (328, -12), (329, -12), (330, -16), (331, -12), (332, -8), (333, -12), (334, -8), (335, -12), (340, -6), (341, -12), (342, -16), (343, -12), (344, -8), (345, -12), (346, -8), (347, -12), (353, -6), (354, -16), (355, -12), (356, -8), (357, -12), (358, -8), (359, -12), (366, -10), (367, -16), (368, -12), (369, -16), (370, -8), (371, -12), (379, -6), (380, -10), (381, -14), (382, -8), (383, -8), (392, -4), (393, -8), (394, -4), (395, -4), (405, -4), (406, -4), (407, -4), (471, -2), (472, -6), (473, -6), (474, -8), (475, -6), (476, -4), (477, -6), (478, -4), (479, -6), (484, -6), (485, -12), (486, -16), (487, -12), (488, -8), (489, -12), (490, -8), (491, -12), (497, -6), (498, -16), (499, -12), (500, -8), (501, -12), (502, -8), (503, -12), (510, -10), (511, -16), (512, -12), (513, -16), (514, -8), (515, -12), (523, -6), (524, -10), (525, -14), (526, -8), (527, -8), (536, -4), (537, -8), (538, -4), (539, -4), (549, -4), (550, -4), (551, -4), (628, -2), (629, -6), (630, -8), (631, -6), (632, -4), (633, -6), (634, -4), (635, -6), (641, -6), (642, -16), (643, -12), (644, -8), (645, -12), (646, -8), (647, -12), (654, -10), (655, -16), (656, -12), (657, -16), (658, -8), (659, -12), (667, -6), (668, -10), (669, -14), (670, -8), (671, -8), (680, -4), (681, -8), (682, -4), (683, -4), (693, -4), (694, -4), (695, -4), (785, -2), (786, -8), (787, -6), (788, -4), (789, -6), (790, -4), (791, -6), (798, -10), (799, -16), (800, -12), (801, -16), (802, -8), (803, -12), (811, -6), (812, -10), (813, -14), (814, -8), (815, -8), (824, -4), (825, -8), (826, -4), (827, -4), (837, -4), (838, -4), (839, -4), (942, -4), (943, -10), (944, -8), (945, -10), (946, -4), (947, -6), (955, -8), (956, -14), (957, -18), (958, -8), (959, -8), (968, -6), (969, -12), (970, -4), (971, -4), (981, -6), (982, -4), (983, 4), (995, 8), (1007, 8), (1099, -2), (1100, -6), (1101, -8), (1102, -4), (1103, -4), (1112, -6), (1113, -12), (1114, -4), (1115, -4), (1125, -6), (1126, -4), (1127, 4), (1139, 8), (1151, 8), (1256, -2), (1257, -6), (1258, -2), (1259, -2), (1269, -6), (1270, -4), (1271, 4), (1283, 8), (1295, 8), (1413, -2), (1414, -2), (1415, 6), (1427, 16), (1439, 16), (1571, 8), (1583, 16), (1727, 8)]
theorem atom0333Coded_decode : atom0333 = SparsePolynomial.decodeCubic 12 atom0333Coded := by decide +kernel
theorem atom0333Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (6528 : Int) atom0333Coded) := by
  have h := atom0333_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0333Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0334 : SparsePolynomial.Poly := [([0,1,5], -4), ([1,1,5], -12), ([1,2,5], -16), ([1,3,5], -16), ([1,4,5], -16), ([1,5,5], -16), ([1,5,6], -8), ([1,5,7], -4), ([1,5,8], 4), ([1,5,9], 6), ([1,5,10], 10), ([1,5,11], 18)]
theorem atom0334_data : atom0334 = SparsePolynomial.monoTimes [1,5] 1 base01 := by decide +kernel
theorem eval_atom0334 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0334 = (quadA (outer g) ![2,1,2] * g 1 * g 5) := by
  rw [atom0334_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0334_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (128 : Int) atom0334) := by
  rw [SparsePolynomial.eval_scale, eval_atom0334]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0334Coded : CoefficientMerge.Poly := [(17, -4), (161, -12), (173, -16), (185, -16), (197, -16), (209, -16), (210, -8), (211, -4), (212, 4), (213, 6), (214, 10), (215, 18)]
theorem atom0334Coded_decode : atom0334 = SparsePolynomial.decodeCubic 12 atom0334Coded := by decide +kernel
theorem atom0334Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (128 : Int) atom0334Coded) := by
  have h := atom0334_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0334Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0335 : SparsePolynomial.Poly := [([0,1,7], -4), ([1,1,7], -12), ([1,2,7], -16), ([1,3,7], -16), ([1,4,7], -16), ([1,5,7], -16), ([1,6,7], -8), ([1,7,7], -4), ([1,7,8], 4), ([1,7,9], 6), ([1,7,10], 10), ([1,7,11], 18)]
theorem atom0335_data : atom0335 = SparsePolynomial.monoTimes [1,7] 1 base01 := by decide +kernel
theorem eval_atom0335 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0335 = (quadA (outer g) ![2,1,2] * g 1 * g 7) := by
  rw [atom0335_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0335_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1360 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0335Coded : CoefficientMerge.Poly := [(19, -4), (163, -12), (175, -16), (187, -16), (199, -16), (211, -16), (223, -8), (235, -4), (236, 4), (237, 6), (238, 10), (239, 18)]
theorem atom0335Coded_decode : atom0335 = SparsePolynomial.decodeCubic 12 atom0335Coded := by decide +kernel
theorem atom0335Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1360 : Int) atom0335Coded) := by
  have h := atom0335_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0335Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0336 : SparsePolynomial.Poly := [([0,1,9], -4), ([1,1,9], -12), ([1,2,9], -16), ([1,3,9], -16), ([1,4,9], -16), ([1,5,9], -16), ([1,6,9], -8), ([1,7,9], -4), ([1,8,9], 4), ([1,9,9], 6), ([1,9,10], 10), ([1,9,11], 18)]
theorem atom0336_data : atom0336 = SparsePolynomial.monoTimes [1,9] 1 base01 := by decide +kernel
theorem eval_atom0336 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0336 = (quadA (outer g) ![2,1,2] * g 1 * g 9) := by
  rw [atom0336_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0336_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0336Coded : CoefficientMerge.Poly := [(21, -4), (165, -12), (177, -16), (189, -16), (201, -16), (213, -16), (225, -8), (237, -4), (249, 4), (261, 6), (262, 10), (263, 18)]
theorem atom0336Coded_decode : atom0336 = SparsePolynomial.decodeCubic 12 atom0336Coded := by decide +kernel
theorem atom0336Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (48 : Int) atom0336Coded) := by
  have h := atom0336_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0336Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0337 : SparsePolynomial.Poly := [([0,1,10], -4), ([1,1,10], -12), ([1,2,10], -16), ([1,3,10], -16), ([1,4,10], -16), ([1,5,10], -16), ([1,6,10], -8), ([1,7,10], -4), ([1,8,10], 4), ([1,9,10], 6), ([1,10,10], 10), ([1,10,11], 18)]
theorem atom0337_data : atom0337 = SparsePolynomial.monoTimes [1,10] 1 base01 := by decide +kernel
theorem eval_atom0337 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0337 = (quadA (outer g) ![2,1,2] * g 1 * g 10) := by
  rw [atom0337_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0337_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1184 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337Coded : CoefficientMerge.Poly := [(22, -4), (166, -12), (178, -16), (190, -16), (202, -16), (214, -16), (226, -8), (238, -4), (250, 4), (262, 6), (274, 10), (275, 18)]
theorem atom0337Coded_decode : atom0337 = SparsePolynomial.decodeCubic 12 atom0337Coded := by decide +kernel
theorem atom0337Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1184 : Int) atom0337Coded) := by
  have h := atom0337_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0337Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0338 : SparsePolynomial.Poly := [([0,1,11], -4), ([1,1,11], -12), ([1,2,11], -16), ([1,3,11], -16), ([1,4,11], -16), ([1,5,11], -16), ([1,6,11], -8), ([1,7,11], -4), ([1,8,11], 4), ([1,9,11], 6), ([1,10,11], 10), ([1,11,11], 18)]
theorem atom0338_data : atom0338 = SparsePolynomial.monoTimes [1,11] 1 base01 := by decide +kernel
theorem eval_atom0338 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0338 = (quadA (outer g) ![2,1,2] * g 1 * g 11) := by
  rw [atom0338_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0338_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1724 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338Coded : CoefficientMerge.Poly := [(23, -4), (167, -12), (179, -16), (191, -16), (203, -16), (215, -16), (227, -8), (239, -4), (251, 4), (263, 6), (275, 10), (287, 18)]
theorem atom0338Coded_decode : atom0338 = SparsePolynomial.decodeCubic 12 atom0338Coded := by decide +kernel
theorem atom0338Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1724 : Int) atom0338Coded) := by
  have h := atom0338_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0338Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0339 : SparsePolynomial.Poly := [([0,3,3], -4), ([1,3,3], -12), ([2,3,3], -16), ([3,3,3], -16), ([3,3,4], -16), ([3,3,5], -16), ([3,3,6], -8), ([3,3,7], -4), ([3,3,8], 4), ([3,3,9], 6), ([3,3,10], 10), ([3,3,11], 18)]
theorem atom0339_data : atom0339 = SparsePolynomial.monoTimes [3,3] 1 base01 := by decide +kernel
theorem eval_atom0339 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0339 = (quadA (outer g) ![2,1,2] * g 3 * g 3) := by
  rw [atom0339_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0339_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (696 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 3 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339Coded : CoefficientMerge.Poly := [(39, -4), (183, -12), (327, -16), (471, -16), (472, -16), (473, -16), (474, -8), (475, -4), (476, 4), (477, 6), (478, 10), (479, 18)]
theorem atom0339Coded_decode : atom0339 = SparsePolynomial.decodeCubic 12 atom0339Coded := by decide +kernel
theorem atom0339Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (696 : Int) atom0339Coded) := by
  have h := atom0339_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0339Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0340 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -14), ([1,1,7], -10), ([1,1,8], -6), ([1,1,9], 2), ([1,1,10], 10), ([1,1,11], 18)]
theorem atom0340_data : atom0340 = SparsePolynomial.monoTimes [1,1] 1 base02 := by decide +kernel
theorem eval_atom0340 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0340 = (quadA (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0340_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0340_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1248 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340Coded : CoefficientMerge.Poly := [(13, -8), (157, -12), (158, -16), (159, -16), (160, -16), (161, -16), (162, -14), (163, -10), (164, -6), (165, 2), (166, 10), (167, 18)]
theorem atom0340Coded_decode : atom0340 = SparsePolynomial.decodeCubic 12 atom0340Coded := by decide +kernel
theorem atom0340Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1248 : Int) atom0340Coded) := by
  have h := atom0340_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0340Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0341 : SparsePolynomial.Poly := [([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,0,9], -2), ([0,0,10], -2), ([0,0,11], -2), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -6), ([0,1,7], -4), ([0,1,8], -4), ([0,1,9], -4), ([0,1,10], -4), ([0,1,11], -4), ([0,2,2], -2), ([0,2,3], -4), ([0,2,4], -4), ([0,2,5], -4), ([0,2,6], -8), ([0,2,7], -6), ([0,2,8], -6), ([0,2,9], -4), ([0,2,10], -4), ([0,2,11], -4), ([0,3,3], -2), ([0,3,4], -4), ([0,3,5], -4), ([0,3,6], -8), ([0,3,7], -6), ([0,3,8], -6), ([0,3,9], -4), ([0,3,10], -4), ([0,3,11], -4), ([0,4,4], -2), ([0,4,5], -4), ([0,4,6], -8), ([0,4,7], -6), ([0,4,8], -6), ([0,4,9], -4), ([0,4,10], -4), ([0,4,11], -4), ([0,5,5], -2), ([0,5,6], -8), ([0,5,7], -6), ([0,5,8], -6), ([0,5,9], -4), ([0,5,10], -4), ([0,5,11], -4), ([0,6,6], -6), ([0,6,7], -10), ([0,6,8], -10), ([0,6,9], -8), ([0,6,10], -4), ([0,6,11], -4), ([0,7,7], -4), ([0,7,8], -8), ([0,7,9], -8), ([0,7,10], -4), ([0,7,11], -4), ([0,8,8], -4), ([0,8,9], -8), ([0,8,10], -4), ([0,8,11], -4), ([0,9,9], -4), ([0,9,10], -4), ([0,9,11], -4), ([1,1,2], -2), ([1,1,3], -2), ([1,1,4], -2), ([1,1,5], -2), ([1,1,6], -4), ([1,1,7], -2), ([1,1,8], -4), ([1,1,9], -4), ([1,1,10], -4), ([1,1,11], -4), ([1,2,2], -4), ([1,2,3], -8), ([1,2,4], -8), ([1,2,5], -8), ([1,2,6], -12), ([1,2,7], -8), ([1,2,8], -12), ([1,2,9], -10), ([1,2,10], -8), ([1,2,11], -8), ([1,3,3], -4), ([1,3,4], -8), ([1,3,5], -8), ([1,3,6], -12), ([1,3,7], -8), ([1,3,8], -12), ([1,3,9], -10), ([1,3,10], -8), ([1,3,11], -8), ([1,4,4], -4), ([1,4,5], -8), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -12), ([1,4,9], -10), ([1,4,10], -8), ([1,4,11], -8), ([1,5,5], -4), ([1,5,6], -12), ([1,5,7], -8), ([1,5,8], -12), ([1,5,9], -10), ([1,5,10], -8), ([1,5,11], -8), ([1,6,6], -8), ([1,6,7], -12), ([1,6,8], -16), ([1,6,9], -14), ([1,6,10], -8), ([1,6,11], -8), ([1,7,7], -4), ([1,7,8], -12), ([1,7,9], -12), ([1,7,10], -8), ([1,7,11], -8), ([1,8,8], -8), ([1,8,9], -12), ([1,8,10], -8), ([1,8,11], -8), ([1,9,9], -4), ([1,9,10], -4), ([1,9,11], -4), ([2,2,2], -2), ([2,2,3], -6), ([2,2,4], -6), ([2,2,5], -6), ([2,2,6], -8), ([2,2,7], -6), ([2,2,8], -8), ([2,2,9], -6), ([2,2,10], -4), ([2,2,11], -6), ([2,3,3], -6), ([2,3,4], -12), ([2,3,5], -12), ([2,3,6], -16), ([2,3,7], -12), ([2,3,8], -16), ([2,3,9], -12), ([2,3,10], -8), ([2,3,11], -12), ([2,4,4], -6), ([2,4,5], -12), ([2,4,6], -16), ([2,4,7], -12), ([2,4,8], -16), ([2,4,9], -12), ([2,4,10], -8), ([2,4,11], -12), ([2,5,5], -6), ([2,5,6], -16), ([2,5,7], -12), ([2,5,8], -16), ([2,5,9], -12), ([2,5,10], -8), ([2,5,11], -12), ([2,6,6], -10), ([2,6,7], -16), ([2,6,8], -20), ([2,6,9], -16), ([2,6,10], -8), ([2,6,11], -12), ([2,7,7], -6), ([2,7,8], -16), ([2,7,9], -14), ([2,7,10], -8), ([2,7,11], -8), ([2,8,8], -10), ([2,8,9], -14), ([2,8,10], -8), ([2,8,11], -8), ([2,9,9], -4), ([2,9,10], -4), ([2,9,11], -4), ([3,3,3], -2), ([3,3,4], -6), ([3,3,5], -6), ([3,3,6], -8), ([3,3,7], -6), ([3,3,8], -8), ([3,3,9], -6), ([3,3,10], -4), ([3,3,11], -6), ([3,4,4], -6), ([3,4,5], -12), ([3,4,6], -16), ([3,4,7], -12), ([3,4,8], -16), ([3,4,9], -12), ([3,4,10], -8), ([3,4,11], -12), ([3,5,5], -6), ([3,5,6], -16), ([3,5,7], -12), ([3,5,8], -16), ([3,5,9], -12), ([3,5,10], -8), ([3,5,11], -12), ([3,6,6], -10), ([3,6,7], -16), ([3,6,8], -20), ([3,6,9], -16), ([3,6,10], -8), ([3,6,11], -12), ([3,7,7], -6), ([3,7,8], -16), ([3,7,9], -14), ([3,7,10], -8), ([3,7,11], -8), ([3,8,8], -10), ([3,8,9], -14), ([3,8,10], -8), ([3,8,11], -8), ([3,9,9], -4), ([3,9,10], -4), ([3,9,11], -4), ([4,4,4], -2), ([4,4,5], -6), ([4,4,6], -8), ([4,4,7], -6), ([4,4,8], -8), ([4,4,9], -6), ([4,4,10], -4), ([4,4,11], -6), ([4,5,5], -6), ([4,5,6], -16), ([4,5,7], -12), ([4,5,8], -16), ([4,5,9], -12), ([4,5,10], -8), ([4,5,11], -12), ([4,6,6], -10), ([4,6,7], -16), ([4,6,8], -20), ([4,6,9], -16), ([4,6,10], -8), ([4,6,11], -12), ([4,7,7], -6), ([4,7,8], -16), ([4,7,9], -14), ([4,7,10], -8), ([4,7,11], -8), ([4,8,8], -10), ([4,8,9], -14), ([4,8,10], -8), ([4,8,11], -8), ([4,9,9], -4), ([4,9,10], -4), ([4,9,11], -4), ([5,5,5], -2), ([5,5,6], -8), ([5,5,7], -6), ([5,5,8], -8), ([5,5,9], -6), ([5,5,10], -4), ([5,5,11], -6), ([5,6,6], -10), ([5,6,7], -16), ([5,6,8], -20), ([5,6,9], -16), ([5,6,10], -8), ([5,6,11], -12), ([5,7,7], -6), ([5,7,8], -16), ([5,7,9], -14), ([5,7,10], -8), ([5,7,11], -8), ([5,8,8], -10), ([5,8,9], -14), ([5,8,10], -8), ([5,8,11], -8), ([5,9,9], -4), ([5,9,10], -4), ([5,9,11], -4), ([6,6,6], -4), ([6,6,7], -10), ([6,6,8], -12), ([6,6,9], -10), ([6,6,10], -4), ([6,6,11], -6), ([6,7,7], -8), ([6,7,8], -20), ([6,7,9], -18), ([6,7,10], -8), ([6,7,11], -8), ([6,8,8], -12), ([6,8,9], -18), ([6,8,10], -8), ([6,9,9], -6), ([6,9,10], -4), ([6,9,11], 4), ([6,10,11], 8), ([6,11,11], 8), ([7,7,7], -2), ([7,7,8], -8), ([7,7,9], -8), ([7,7,10], -4), ([7,7,11], -4), ([7,8,8], -10), ([7,8,9], -16), ([7,8,10], -8), ([7,9,9], -6), ([7,9,10], -4), ([7,9,11], 4), ([7,10,11], 8), ([7,11,11], 8), ([8,8,8], -4), ([8,8,9], -8), ([8,8,10], -4), ([8,8,11], 4), ([8,9,9], -6), ([8,9,10], -4), ([8,9,11], 12), ([8,10,11], 16), ([8,11,11], 16), ([9,9,9], -2), ([9,9,10], -2), ([9,9,11], 6), ([9,10,11], 16), ([9,11,11], 16), ([10,10,11], 8), ([10,11,11], 16), ([11,11,11], 8)]
theorem atom0341_data : atom0341 = SparsePolynomial.monoTimes [] 1 base03 := by decide +kernel
theorem eval_atom0341 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0341 = (detB (outer g)) := by
  rw [atom0341_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0341_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12480 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (detB (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341Coded : CoefficientMerge.Poly := [(6, -2), (7, -2), (8, -2), (9, -2), (10, -2), (11, -2), (14, -2), (15, -2), (16, -2), (17, -2), (18, -6), (19, -4), (20, -4), (21, -4), (22, -4), (23, -4), (26, -2), (27, -4), (28, -4), (29, -4), (30, -8), (31, -6), (32, -6), (33, -4), (34, -4), (35, -4), (39, -2), (40, -4), (41, -4), (42, -8), (43, -6), (44, -6), (45, -4), (46, -4), (47, -4), (52, -2), (53, -4), (54, -8), (55, -6), (56, -6), (57, -4), (58, -4), (59, -4), (65, -2), (66, -8), (67, -6), (68, -6), (69, -4), (70, -4), (71, -4), (78, -6), (79, -10), (80, -10), (81, -8), (82, -4), (83, -4), (91, -4), (92, -8), (93, -8), (94, -4), (95, -4), (104, -4), (105, -8), (106, -4), (107, -4), (117, -4), (118, -4), (119, -4), (158, -2), (159, -2), (160, -2), (161, -2), (162, -4), (163, -2), (164, -4), (165, -4), (166, -4), (167, -4), (170, -4), (171, -8), (172, -8), (173, -8), (174, -12), (175, -8), (176, -12), (177, -10), (178, -8), (179, -8), (183, -4), (184, -8), (185, -8), (186, -12), (187, -8), (188, -12), (189, -10), (190, -8), (191, -8), (196, -4), (197, -8), (198, -12), (199, -8), (200, -12), (201, -10), (202, -8), (203, -8), (209, -4), (210, -12), (211, -8), (212, -12), (213, -10), (214, -8), (215, -8), (222, -8), (223, -12), (224, -16), (225, -14), (226, -8), (227, -8), (235, -4), (236, -12), (237, -12), (238, -8), (239, -8), (248, -8), (249, -12), (250, -8), (251, -8), (261, -4), (262, -4), (263, -4), (314, -2), (315, -6), (316, -6), (317, -6), (318, -8), (319, -6), (320, -8), (321, -6), (322, -4), (323, -6), (327, -6), (328, -12), (329, -12), (330, -16), (331, -12), (332, -16), (333, -12), (334, -8), (335, -12), (340, -6), (341, -12), (342, -16), (343, -12), (344, -16), (345, -12), (346, -8), (347, -12), (353, -6), (354, -16), (355, -12), (356, -16), (357, -12), (358, -8), (359, -12), (366, -10), (367, -16), (368, -20), (369, -16), (370, -8), (371, -12), (379, -6), (380, -16), (381, -14), (382, -8), (383, -8), (392, -10), (393, -14), (394, -8), (395, -8), (405, -4), (406, -4), (407, -4), (471, -2), (472, -6), (473, -6), (474, -8), (475, -6), (476, -8), (477, -6), (478, -4), (479, -6), (484, -6), (485, -12), (486, -16), (487, -12), (488, -16), (489, -12), (490, -8), (491, -12), (497, -6), (498, -16), (499, -12), (500, -16), (501, -12), (502, -8), (503, -12), (510, -10), (511, -16), (512, -20), (513, -16), (514, -8), (515, -12), (523, -6), (524, -16), (525, -14), (526, -8), (527, -8), (536, -10), (537, -14), (538, -8), (539, -8), (549, -4), (550, -4), (551, -4), (628, -2), (629, -6), (630, -8), (631, -6), (632, -8), (633, -6), (634, -4), (635, -6), (641, -6), (642, -16), (643, -12), (644, -16), (645, -12), (646, -8), (647, -12), (654, -10), (655, -16), (656, -20), (657, -16), (658, -8), (659, -12), (667, -6), (668, -16), (669, -14), (670, -8), (671, -8), (680, -10), (681, -14), (682, -8), (683, -8), (693, -4), (694, -4), (695, -4), (785, -2), (786, -8), (787, -6), (788, -8), (789, -6), (790, -4), (791, -6), (798, -10), (799, -16), (800, -20), (801, -16), (802, -8), (803, -12), (811, -6), (812, -16), (813, -14), (814, -8), (815, -8), (824, -10), (825, -14), (826, -8), (827, -8), (837, -4), (838, -4), (839, -4), (942, -4), (943, -10), (944, -12), (945, -10), (946, -4), (947, -6), (955, -8), (956, -20), (957, -18), (958, -8), (959, -8), (968, -12), (969, -18), (970, -8), (981, -6), (982, -4), (983, 4), (995, 8), (1007, 8), (1099, -2), (1100, -8), (1101, -8), (1102, -4), (1103, -4), (1112, -10), (1113, -16), (1114, -8), (1125, -6), (1126, -4), (1127, 4), (1139, 8), (1151, 8), (1256, -4), (1257, -8), (1258, -4), (1259, 4), (1269, -6), (1270, -4), (1271, 12), (1283, 16), (1295, 16), (1413, -2), (1414, -2), (1415, 6), (1427, 16), (1439, 16), (1571, 8), (1583, 16), (1727, 8)]
theorem atom0341Coded_decode : atom0341 = SparsePolynomial.decodeCubic 12 atom0341Coded := by decide +kernel
theorem atom0341Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (12480 : Int) atom0341Coded) := by
  have h := atom0341_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0341Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0342 : SparsePolynomial.Poly := [([0,0,0], -1), ([0,0,1], -2), ([0,0,2], -2), ([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,0,9], -2), ([0,1,1], -1), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -2), ([0,1,7], -2), ([0,1,8], -2), ([0,1,9], -2), ([0,2,2], -1), ([0,2,3], -2), ([0,2,4], -2), ([0,2,5], -2), ([0,2,6], -2), ([0,2,7], -2), ([0,2,8], -2), ([0,2,9], -2), ([0,3,3], -1), ([0,3,4], -2), ([0,3,5], -2), ([0,3,6], -2), ([0,3,7], -2), ([0,3,8], -2), ([0,3,9], -2), ([0,4,4], -1), ([0,4,5], -2), ([0,4,6], -2), ([0,4,7], -2), ([0,4,8], -2), ([0,4,9], -2), ([0,5,5], -1), ([0,5,6], -2), ([0,5,7], -2), ([0,5,8], -2), ([0,5,9], -2), ([0,6,6], -1), ([0,6,7], -2), ([0,6,8], -2), ([0,6,9], -2), ([0,7,7], -1), ([0,7,8], -2), ([0,7,9], -2), ([0,8,8], -1), ([0,8,9], -2), ([0,8,11], 4), ([0,9,9], -1), ([0,9,11], 4), ([0,10,11], 4), ([0,11,11], 4)]
theorem atom0342_data : atom0342 = SparsePolynomial.monoTimes [0] 1 base04 := by decide +kernel
theorem eval_atom0342 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0342 = (minorB (outer g) 0 1 * g 0) := by
  rw [atom0342_data, SparsePolynomial.eval_monoTimes, eval_base04]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0342_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4224 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg0 : 0 ≤ g 0 := hg 0
  have hb := base04_nonneg g hg hA hB
  rw [eval_base04] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 0) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342Coded : CoefficientMerge.Poly := [(0, -1), (1, -2), (2, -2), (3, -2), (4, -2), (5, -2), (6, -2), (7, -2), (8, -2), (9, -2), (13, -1), (14, -2), (15, -2), (16, -2), (17, -2), (18, -2), (19, -2), (20, -2), (21, -2), (26, -1), (27, -2), (28, -2), (29, -2), (30, -2), (31, -2), (32, -2), (33, -2), (39, -1), (40, -2), (41, -2), (42, -2), (43, -2), (44, -2), (45, -2), (52, -1), (53, -2), (54, -2), (55, -2), (56, -2), (57, -2), (65, -1), (66, -2), (67, -2), (68, -2), (69, -2), (78, -1), (79, -2), (80, -2), (81, -2), (91, -1), (92, -2), (93, -2), (104, -1), (105, -2), (107, 4), (117, -1), (119, 4), (131, 4), (143, 4)]
theorem atom0342Coded_decode : atom0342 = SparsePolynomial.decodeCubic 12 atom0342Coded := by decide +kernel
theorem atom0342Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (4224 : Int) atom0342Coded) := by
  have h := atom0342_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0342Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0343 : SparsePolynomial.Poly := [([0,0,11], -2), ([0,1,11], -2), ([0,2,11], -2), ([0,3,11], -2), ([0,4,11], -2), ([0,5,11], -2), ([0,6,11], -2), ([0,7,11], -2), ([0,10,11], 2), ([0,11,11], 4)]
theorem atom0343_data : atom0343 = SparsePolynomial.monoTimes [0,11] 1 base05 := by decide +kernel
theorem eval_atom0343 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0343 = (quadB (outer g) ![1,1,0] * g 0 * g 11) := by
  rw [atom0343_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0343_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5280 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,1,0] * g 0 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343Coded : CoefficientMerge.Poly := [(11, -2), (23, -2), (35, -2), (47, -2), (59, -2), (71, -2), (83, -2), (95, -2), (131, 2), (143, 4)]
theorem atom0343Coded_decode : atom0343 = SparsePolynomial.decodeCubic 12 atom0343Coded := by decide +kernel
theorem atom0343Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (5280 : Int) atom0343Coded) := by
  have h := atom0343_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0343Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0344 : SparsePolynomial.Poly := [([0,2,10], -4), ([1,2,10], -8), ([2,2,10], -16), ([2,3,10], -16), ([2,4,10], -16), ([2,5,10], -16), ([2,6,10], -8), ([2,8,10], 8), ([2,9,10], 12), ([2,10,10], 16), ([2,10,11], 18)]
theorem atom0344_data : atom0344 = SparsePolynomial.monoTimes [2,10] 1 base06 := by decide +kernel
theorem eval_atom0344 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0344 = (quadB (outer g) ![1,2,2] * g 2 * g 10) := by
  rw [atom0344_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0344_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1332 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 2 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344Coded : CoefficientMerge.Poly := [(34, -4), (178, -8), (322, -16), (334, -16), (346, -16), (358, -16), (370, -8), (394, 8), (406, 12), (418, 16), (419, 18)]
theorem atom0344Coded_decode : atom0344 = SparsePolynomial.decodeCubic 12 atom0344Coded := by decide +kernel
theorem atom0344Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1332 : Int) atom0344Coded) := by
  have h := atom0344_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0344Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0345 : SparsePolynomial.Poly := [([0,3,4], -4), ([1,3,4], -8), ([2,3,4], -16), ([3,3,4], -16), ([3,4,4], -16), ([3,4,5], -16), ([3,4,6], -8), ([3,4,8], 8), ([3,4,9], 12), ([3,4,10], 16), ([3,4,11], 18)]
theorem atom0345_data : atom0345 = SparsePolynomial.monoTimes [3,4] 1 base06 := by decide +kernel
theorem eval_atom0345 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0345 = (quadB (outer g) ![1,2,2] * g 3 * g 4) := by
  rw [atom0345_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0345_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345Coded : CoefficientMerge.Poly := [(40, -4), (184, -8), (328, -16), (472, -16), (484, -16), (485, -16), (486, -8), (488, 8), (489, 12), (490, 16), (491, 18)]
theorem atom0345Coded_decode : atom0345 = SparsePolynomial.decodeCubic 12 atom0345Coded := by decide +kernel
theorem atom0345Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (264 : Int) atom0345Coded) := by
  have h := atom0345_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0345Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0346 : SparsePolynomial.Poly := [([0,3,10], -4), ([1,3,10], -8), ([2,3,10], -16), ([3,3,10], -16), ([3,4,10], -16), ([3,5,10], -16), ([3,6,10], -8), ([3,8,10], 8), ([3,9,10], 12), ([3,10,10], 16), ([3,10,11], 18)]
theorem atom0346_data : atom0346 = SparsePolynomial.monoTimes [3,10] 1 base06 := by decide +kernel
theorem eval_atom0346 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0346 = (quadB (outer g) ![1,2,2] * g 3 * g 10) := by
  rw [atom0346_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0346_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2187 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346Coded : CoefficientMerge.Poly := [(46, -4), (190, -8), (334, -16), (478, -16), (490, -16), (502, -16), (514, -8), (538, 8), (550, 12), (562, 16), (563, 18)]
theorem atom0346Coded_decode : atom0346 = SparsePolynomial.decodeCubic 12 atom0346Coded := by decide +kernel
theorem atom0346Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (2187 : Int) atom0346Coded) := by
  have h := atom0346_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0346Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0347 : SparsePolynomial.Poly := [([0,4,5], -4), ([1,4,5], -8), ([2,4,5], -16), ([3,4,5], -16), ([4,4,5], -16), ([4,5,5], -16), ([4,5,6], -8), ([4,5,8], 8), ([4,5,9], 12), ([4,5,10], 16), ([4,5,11], 18)]
theorem atom0347_data : atom0347 = SparsePolynomial.monoTimes [4,5] 1 base06 := by decide +kernel
theorem eval_atom0347 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0347 = (quadB (outer g) ![1,2,2] * g 4 * g 5) := by
  rw [atom0347_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0347_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1644 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347Coded : CoefficientMerge.Poly := [(53, -4), (197, -8), (341, -16), (485, -16), (629, -16), (641, -16), (642, -8), (644, 8), (645, 12), (646, 16), (647, 18)]
theorem atom0347Coded_decode : atom0347 = SparsePolynomial.decodeCubic 12 atom0347Coded := by decide +kernel
theorem atom0347Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1644 : Int) atom0347Coded) := by
  have h := atom0347_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0347Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0348 : SparsePolynomial.Poly := [([0,4,7], -4), ([1,4,7], -8), ([2,4,7], -16), ([3,4,7], -16), ([4,4,7], -16), ([4,5,7], -16), ([4,6,7], -8), ([4,7,8], 8), ([4,7,9], 12), ([4,7,10], 16), ([4,7,11], 18)]
theorem atom0348_data : atom0348 = SparsePolynomial.monoTimes [4,7] 1 base06 := by decide +kernel
theorem eval_atom0348 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0348 = (quadB (outer g) ![1,2,2] * g 4 * g 7) := by
  rw [atom0348_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0348_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (552 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348Coded : CoefficientMerge.Poly := [(55, -4), (199, -8), (343, -16), (487, -16), (631, -16), (643, -16), (655, -8), (668, 8), (669, 12), (670, 16), (671, 18)]
theorem atom0348Coded_decode : atom0348 = SparsePolynomial.decodeCubic 12 atom0348Coded := by decide +kernel
theorem atom0348Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (552 : Int) atom0348Coded) := by
  have h := atom0348_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0348Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0349 : SparsePolynomial.Poly := [([0,4,10], -4), ([1,4,10], -8), ([2,4,10], -16), ([3,4,10], -16), ([4,4,10], -16), ([4,5,10], -16), ([4,6,10], -8), ([4,8,10], 8), ([4,9,10], 12), ([4,10,10], 16), ([4,10,11], 18)]
theorem atom0349_data : atom0349 = SparsePolynomial.monoTimes [4,10] 1 base06 := by decide +kernel
theorem eval_atom0349 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0349 = (quadB (outer g) ![1,2,2] * g 4 * g 10) := by
  rw [atom0349_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0349_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2148 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349Coded : CoefficientMerge.Poly := [(58, -4), (202, -8), (346, -16), (490, -16), (634, -16), (646, -16), (658, -8), (682, 8), (694, 12), (706, 16), (707, 18)]
theorem atom0349Coded_decode : atom0349 = SparsePolynomial.decodeCubic 12 atom0349Coded := by decide +kernel
theorem atom0349Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (2148 : Int) atom0349Coded) := by
  have h := atom0349_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0349Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0350 : SparsePolynomial.Poly := [([0,5,7], -4), ([1,5,7], -8), ([2,5,7], -16), ([3,5,7], -16), ([4,5,7], -16), ([5,5,7], -16), ([5,6,7], -8), ([5,7,8], 8), ([5,7,9], 12), ([5,7,10], 16), ([5,7,11], 18)]
theorem atom0350_data : atom0350 = SparsePolynomial.monoTimes [5,7] 1 base06 := by decide +kernel
theorem eval_atom0350 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0350 = (quadB (outer g) ![1,2,2] * g 5 * g 7) := by
  rw [atom0350_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0350_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1152 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350Coded : CoefficientMerge.Poly := [(67, -4), (211, -8), (355, -16), (499, -16), (643, -16), (787, -16), (799, -8), (812, 8), (813, 12), (814, 16), (815, 18)]
theorem atom0350Coded_decode : atom0350 = SparsePolynomial.decodeCubic 12 atom0350Coded := by decide +kernel
theorem atom0350Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1152 : Int) atom0350Coded) := by
  have h := atom0350_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0350Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0351 : SparsePolynomial.Poly := [([0,5,10], -4), ([1,5,10], -8), ([2,5,10], -16), ([3,5,10], -16), ([4,5,10], -16), ([5,5,10], -16), ([5,6,10], -8), ([5,8,10], 8), ([5,9,10], 12), ([5,10,10], 16), ([5,10,11], 18)]
theorem atom0351_data : atom0351 = SparsePolynomial.monoTimes [5,10] 1 base06 := by decide +kernel
theorem eval_atom0351 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0351 = (quadB (outer g) ![1,2,2] * g 5 * g 10) := by
  rw [atom0351_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0351_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1260 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351Coded : CoefficientMerge.Poly := [(70, -4), (214, -8), (358, -16), (502, -16), (646, -16), (790, -16), (802, -8), (826, 8), (838, 12), (850, 16), (851, 18)]
theorem atom0351Coded_decode : atom0351 = SparsePolynomial.decodeCubic 12 atom0351Coded := by decide +kernel
theorem atom0351Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1260 : Int) atom0351Coded) := by
  have h := atom0351_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0351Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0352 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -16), ([0,1,4], -16), ([0,1,5], -16), ([0,1,6], -14), ([0,1,7], -10), ([0,1,8], -2), ([0,1,9], 2), ([0,1,10], 10), ([0,1,11], 18)]
theorem atom0352_data : atom0352 = SparsePolynomial.monoTimes [0,1] 1 base07 := by decide +kernel
theorem eval_atom0352 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0352 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0352_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0352_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (936 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352Coded : CoefficientMerge.Poly := [(1, -8), (13, -12), (14, -16), (15, -16), (16, -16), (17, -16), (18, -14), (19, -10), (20, -2), (21, 2), (22, 10), (23, 18)]
theorem atom0352Coded_decode : atom0352 = SparsePolynomial.decodeCubic 12 atom0352Coded := by decide +kernel
theorem atom0352Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (936 : Int) atom0352Coded) := by
  have h := atom0352_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0352Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0353 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -16), ([0,2,4], -16), ([0,2,5], -16), ([0,2,6], -14), ([0,2,7], -10), ([0,2,8], -2), ([0,2,9], 2), ([0,2,10], 10), ([0,2,11], 18)]
theorem atom0353_data : atom0353 = SparsePolynomial.monoTimes [0,2] 1 base07 := by decide +kernel
theorem eval_atom0353 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0353 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0353_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0353_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1344 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353Coded : CoefficientMerge.Poly := [(2, -8), (14, -12), (26, -16), (27, -16), (28, -16), (29, -16), (30, -14), (31, -10), (32, -2), (33, 2), (34, 10), (35, 18)]
theorem atom0353Coded_decode : atom0353 = SparsePolynomial.decodeCubic 12 atom0353Coded := by decide +kernel
theorem atom0353Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1344 : Int) atom0353Coded) := by
  have h := atom0353_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0353Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0354 : SparsePolynomial.Poly := [([0,0,3], -8), ([0,1,3], -12), ([0,2,3], -16), ([0,3,3], -16), ([0,3,4], -16), ([0,3,5], -16), ([0,3,6], -14), ([0,3,7], -10), ([0,3,8], -2), ([0,3,9], 2), ([0,3,10], 10), ([0,3,11], 18)]
theorem atom0354_data : atom0354 = SparsePolynomial.monoTimes [0,3] 1 base07 := by decide +kernel
theorem eval_atom0354 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0354 = (quadB (outer g) ![2,2,1] * g 0 * g 3) := by
  rw [atom0354_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0354_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1752 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354Coded : CoefficientMerge.Poly := [(3, -8), (15, -12), (27, -16), (39, -16), (40, -16), (41, -16), (42, -14), (43, -10), (44, -2), (45, 2), (46, 10), (47, 18)]
theorem atom0354Coded_decode : atom0354 = SparsePolynomial.decodeCubic 12 atom0354Coded := by decide +kernel
theorem atom0354Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1752 : Int) atom0354Coded) := by
  have h := atom0354_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0354Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0355 : SparsePolynomial.Poly := [([0,0,4], -8), ([0,1,4], -12), ([0,2,4], -16), ([0,3,4], -16), ([0,4,4], -16), ([0,4,5], -16), ([0,4,6], -14), ([0,4,7], -10), ([0,4,8], -2), ([0,4,9], 2), ([0,4,10], 10), ([0,4,11], 18)]
theorem atom0355_data : atom0355 = SparsePolynomial.monoTimes [0,4] 1 base07 := by decide +kernel
theorem eval_atom0355 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0355 = (quadB (outer g) ![2,2,1] * g 0 * g 4) := by
  rw [atom0355_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0355_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2160 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355Coded : CoefficientMerge.Poly := [(4, -8), (16, -12), (28, -16), (40, -16), (52, -16), (53, -16), (54, -14), (55, -10), (56, -2), (57, 2), (58, 10), (59, 18)]
theorem atom0355Coded_decode : atom0355 = SparsePolynomial.decodeCubic 12 atom0355Coded := by decide +kernel
theorem atom0355Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (2160 : Int) atom0355Coded) := by
  have h := atom0355_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0355Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0356 : SparsePolynomial.Poly := [([0,0,5], -8), ([0,1,5], -12), ([0,2,5], -16), ([0,3,5], -16), ([0,4,5], -16), ([0,5,5], -16), ([0,5,6], -14), ([0,5,7], -10), ([0,5,8], -2), ([0,5,9], 2), ([0,5,10], 10), ([0,5,11], 18)]
theorem atom0356_data : atom0356 = SparsePolynomial.monoTimes [0,5] 1 base07 := by decide +kernel
theorem eval_atom0356 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0356 = (quadB (outer g) ![2,2,1] * g 0 * g 5) := by
  rw [atom0356_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0356_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2568 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356Coded : CoefficientMerge.Poly := [(5, -8), (17, -12), (29, -16), (41, -16), (53, -16), (65, -16), (66, -14), (67, -10), (68, -2), (69, 2), (70, 10), (71, 18)]
theorem atom0356Coded_decode : atom0356 = SparsePolynomial.decodeCubic 12 atom0356Coded := by decide +kernel
theorem atom0356Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (2568 : Int) atom0356Coded) := by
  have h := atom0356_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0356Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0357 : SparsePolynomial.Poly := [([0,0,10], -8), ([0,1,10], -12), ([0,2,10], -16), ([0,3,10], -16), ([0,4,10], -16), ([0,5,10], -16), ([0,6,10], -14), ([0,7,10], -10), ([0,8,10], -2), ([0,9,10], 2), ([0,10,10], 10), ([0,10,11], 18)]
theorem atom0357_data : atom0357 = SparsePolynomial.monoTimes [0,10] 1 base07 := by decide +kernel
theorem eval_atom0357 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0357 = (quadB (outer g) ![2,2,1] * g 0 * g 10) := by
  rw [atom0357_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0357_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (912 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357Coded : CoefficientMerge.Poly := [(10, -8), (22, -12), (34, -16), (46, -16), (58, -16), (70, -16), (82, -14), (94, -10), (106, -2), (118, 2), (130, 10), (131, 18)]
theorem atom0357Coded_decode : atom0357 = SparsePolynomial.decodeCubic 12 atom0357Coded := by decide +kernel
theorem atom0357Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (912 : Int) atom0357Coded) := by
  have h := atom0357_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0357Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0358 : SparsePolynomial.Poly := [([0,1,11], -8), ([1,1,11], -12), ([1,2,11], -16), ([1,3,11], -16), ([1,4,11], -16), ([1,5,11], -16), ([1,6,11], -14), ([1,7,11], -10), ([1,8,11], -2), ([1,9,11], 2), ([1,10,11], 10), ([1,11,11], 18)]
theorem atom0358_data : atom0358 = SparsePolynomial.monoTimes [1,11] 1 base07 := by decide +kernel
theorem eval_atom0358 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0358 = (quadB (outer g) ![2,2,1] * g 1 * g 11) := by
  rw [atom0358_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0358_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (596 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358Coded : CoefficientMerge.Poly := [(23, -8), (167, -12), (179, -16), (191, -16), (203, -16), (215, -16), (227, -14), (239, -10), (251, -2), (263, 2), (275, 10), (287, 18)]
theorem atom0358Coded_decode : atom0358 = SparsePolynomial.decodeCubic 12 atom0358Coded := by decide +kernel
theorem atom0358Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (596 : Int) atom0358Coded) := by
  have h := atom0358_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0358Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0359 : SparsePolynomial.Poly := [([0,2,11], -8), ([1,2,11], -12), ([2,2,11], -16), ([2,3,11], -16), ([2,4,11], -16), ([2,5,11], -16), ([2,6,11], -14), ([2,7,11], -10), ([2,8,11], -2), ([2,9,11], 2), ([2,10,11], 10), ([2,11,11], 18)]
theorem atom0359_data : atom0359 = SparsePolynomial.monoTimes [2,11] 1 base07 := by decide +kernel
theorem eval_atom0359 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0359 = (quadB (outer g) ![2,2,1] * g 2 * g 11) := by
  rw [atom0359_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0359_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (408 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 2 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359Coded : CoefficientMerge.Poly := [(35, -8), (179, -12), (323, -16), (335, -16), (347, -16), (359, -16), (371, -14), (383, -10), (395, -2), (407, 2), (419, 10), (431, 18)]
theorem atom0359Coded_decode : atom0359 = SparsePolynomial.decodeCubic 12 atom0359Coded := by decide +kernel
theorem atom0359Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (408 : Int) atom0359Coded) := by
  have h := atom0359_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0359Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0360 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -16), ([4,4,4], -16), ([4,4,5], -16), ([4,4,6], -14), ([4,4,7], -10), ([4,4,8], -2), ([4,4,9], 2), ([4,4,10], 10), ([4,4,11], 18)]
theorem atom0360_data : atom0360 = SparsePolynomial.monoTimes [4,4] 1 base07 := by decide +kernel
theorem eval_atom0360 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0360 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0360_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0360_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1248 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360Coded : CoefficientMerge.Poly := [(52, -8), (196, -12), (340, -16), (484, -16), (628, -16), (629, -16), (630, -14), (631, -10), (632, -2), (633, 2), (634, 10), (635, 18)]
theorem atom0360Coded_decode : atom0360 = SparsePolynomial.decodeCubic 12 atom0360Coded := by decide +kernel
theorem atom0360Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1248 : Int) atom0360Coded) := by
  have h := atom0360_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0360Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0361 : SparsePolynomial.Poly := [([0,5,5], -8), ([1,5,5], -12), ([2,5,5], -16), ([3,5,5], -16), ([4,5,5], -16), ([5,5,5], -16), ([5,5,6], -14), ([5,5,7], -10), ([5,5,8], -2), ([5,5,9], 2), ([5,5,10], 10), ([5,5,11], 18)]
theorem atom0361_data : atom0361 = SparsePolynomial.monoTimes [5,5] 1 base07 := by decide +kernel
theorem eval_atom0361 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0361 = (quadB (outer g) ![2,2,1] * g 5 * g 5) := by
  rw [atom0361_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0361_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1728 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361Coded : CoefficientMerge.Poly := [(65, -8), (209, -12), (353, -16), (497, -16), (641, -16), (785, -16), (786, -14), (787, -10), (788, -2), (789, 2), (790, 10), (791, 18)]
theorem atom0361Coded_decode : atom0361 = SparsePolynomial.decodeCubic 12 atom0361Coded := by decide +kernel
theorem atom0361Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1728 : Int) atom0361Coded) := by
  have h := atom0361_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0361Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0362 : SparsePolynomial.Poly := [([0,7,7], -8), ([1,7,7], -12), ([2,7,7], -16), ([3,7,7], -16), ([4,7,7], -16), ([5,7,7], -16), ([6,7,7], -14), ([7,7,7], -10), ([7,7,8], -2), ([7,7,9], 2), ([7,7,10], 10), ([7,7,11], 18)]
theorem atom0362_data : atom0362 = SparsePolynomial.monoTimes [7,7] 1 base07 := by decide +kernel
theorem eval_atom0362 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0362 = (quadB (outer g) ![2,2,1] * g 7 * g 7) := by
  rw [atom0362_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0362_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1728 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362Coded : CoefficientMerge.Poly := [(91, -8), (235, -12), (379, -16), (523, -16), (667, -16), (811, -16), (955, -14), (1099, -10), (1100, -2), (1101, 2), (1102, 10), (1103, 18)]
theorem atom0362Coded_decode : atom0362 = SparsePolynomial.decodeCubic 12 atom0362Coded := by decide +kernel
theorem atom0362Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1728 : Int) atom0362Coded) := by
  have h := atom0362_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0362Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block004 : CoefficientMerge.Poly := [(0, -4224), (1, -15936), (2, -19200), (3, -22464), (4, -25728), (5, -28992), (6, -46464), (7, -46464), (8, -46464), (9, -46464), (10, -45312), (11, -48576), (13, -25440), (14, -77568), (15, -82464), (16, -87360), (17, -92768), (18, -135600), (19, -99280), (20, -86352), (21, -82800), (22, -82352), (23, -81408), (26, -63744), (27, -134016), (28, -140544), (29, -147072), (30, -179328), (31, -135936), (32, -112128), (33, -81792), (34, -82512), (35, -65664), (39, -73056), (40, -148128), (41, -153600), (42, -185040), (43, -140016), (44, -112944), (45, -80976), (46, -81852), (47, -55056), (52, -86784), (53, -166704), (54, -190752), (55, -146304), (56, -113760), (57, -80160), (58, -77616), (59, -47712), (65, -97152), (66, -196464), (67, -152784), (68, -114576), (69, -79344), (70, -69984), (71, -40368), (78, -118272), (79, -198528), (80, -185472), (81, -160512), (82, -88800), (83, -86592), (91, -94080), (92, -160512), (93, -160512), (94, -85152), (95, -86592), (104, -80256), (105, -160512), (106, -77856), (107, -59136), (117, -80256), (118, -74208), (119, -59136), (130, 9120), (131, 43872), (143, 38016), (157, -14976), (158, -57984), (159, -57984), (160, -57984), (161, -59520), (162, -93504), (163, -66816), (164, -70464), (165, -74112), (166, -77760), (167, -81408), (170, -76032), (171, -152064), (172, -152064), (173, -154112), (174, -228096), (175, -173824), (176, -188928), (177, -190848), (178, -181664), (179, -194080), (183, -84384), (184, -154176), (185, -154112), (186, -228096), (187, -173824), (188, -188928), (189, -190848), (190, -188504), (191, -189184), (196, -91008), (197, -167264), (198, -228096), (199, -178240), (200, -188928), (201, -190848), (202, -188192), (203, -189184), (209, -98816), (210, -229120), (211, -183552), (212, -188416), (213, -190080), (214, -179808), (215, -186880), (222, -152064), (223, -238976), (224, -264960), (225, -266496), (226, -161536), (227, -174200), (235, -102208), (236, -196544), (237, -220128), (238, -143200), (239, -140440), (248, -125952), (249, -201792), (250, -121216), (251, -120248), (261, -75744), (262, -68448), (263, -63632), (274, 11840), (275, 44512), (287, 41760), (314, -38016), (315, -114048), (316, -114048), (317, -114048), (318, -152064), (319, -114048), (320, -125952), (321, -114048), (322, -97344), (323, -120576), (327, -125184), (328, -232320), (329, -228096), (330, -304128), (331, -228096), (332, -251904), (333, -228096), (334, -208368), (335, -234624), (340, -134016), (341, -254400), (342, -304128), (343, -236928), (344, -251904), (345, -228096), (346, -207744), (347, -234624), (353, -141696), (354, -304128), (355, -246528), (356, -251904), (357, -228096), (358, -193536), (359, -234624), (366, -190080), (367, -304128), (368, -327936), (369, -304128), (370, -162720), (371, -233808), (379, -141696), (380, -264960), (381, -266112), (382, -152064), (383, -156144), (392, -150912), (393, -226944), (394, -115296), (395, -126768), (405, -76032), (406, -60048), (407, -75216), (418, 21312), (419, 28056), (431, 7344), (471, -49152), (472, -129408), (473, -125184), (474, -157632), (475, -116832), (476, -123168), (477, -109872), (478, -104064), (479, -101520), (484, -138240), (485, -258624), (486, -306240), (487, -236928), (488, -249792), (489, -224928), (490, -217200), (491, -223344), (497, -141696), (498, -304128), (499, -246528), (500, -251904), (501, -228096), (502, -207216), (503, -228096), (510, -190080), (511, -304128), (512, -327936), (513, -304128), (514, -169560), (515, -228096), (523, -141696), (524, -264960), (525, -266112), (526, -152064), (527, -152064), (536, -150912), (537, -226944), (538, -108456), (539, -125952), (549, -76032), (550, -49788), (551, -76032), (562, 34992), (563, 39366), (628, -57984), (629, -160320), (630, -169536), (631, -135360), (632, -128448), (633, -111552), (634, -97920), (635, -91584), (641, -168000), (642, -317280), (643, -255360), (644, -238752), (645, -208368), (646, -180288), (647, -198504), (654, -190080), (655, -308544), (656, -327936), (657, -304128), (658, -169248), (659, -228096), (667, -141696), (668, -260544), (669, -259488), (670, -143232), (671, -142128), (680, -150912), (681, -226944), (682, -108768), (683, -125952), (693, -76032), (694, -50256), (695, -76032), (706, 34368), (707, 38664), (785, -65664), (786, -176256), (787, -149760), (788, -129408), (789, -110592), (790, -78912), (791, -82944), (798, -190080), (799, -313344), (800, -327936), (801, -304128), (802, -162144), (803, -228096), (811, -141696), (812, -255744), (813, -252288), (814, -133632), (815, -131328), (824, -150912), (825, -226944), (826, -115872), (827, -125952), (837, -76032), (838, -60912), (839, -76032), (850, 20160), (851, 22680), (942, -76032), (943, -190080), (944, -201984), (945, -190080), (946, -76032), (947, -114048), (955, -176256), (956, -340992), (957, -342144), (958, -152064), (959, -152064), (968, -188928), (969, -302976), (970, -125952), (971, -26112), (981, -114048), (982, -76032), (983, 76032), (995, 152064), (1007, 152064), (1099, -55296), (1100, -142464), (1101, -148608), (1102, -58752), (1103, -44928), (1112, -163968), (1113, -278016), (1114, -125952), (1115, -26112), (1125, -114048), (1126, -76032), (1127, 76032), (1139, 152064), (1151, 152064), (1256, -62976), (1257, -139008), (1258, -62976), (1259, 36864), (1269, -114048), (1270, -76032), (1271, 400896), (1282, 171072), (1283, 542592), (1295, 342144), (1413, 9600), (1414, 125760), (1415, 222720), (1426, 190080), (1427, 602880), (1439, 380160), (1570, 69696), (1571, 331584), (1583, 418176), (1727, 152064)]
theorem block004_data : block004 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (225024 : Int) atom0320Coded) (CoefficientMerge.scale (171072 : Int) atom0321Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (290688 : Int) atom0322Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90240 : Int) atom0323Coded) (CoefficientMerge.scale (47616 : Int) atom0324Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163776 : Int) atom0325Coded) (CoefficientMerge.scale (108672 : Int) atom0326Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (190080 : Int) atom0327Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298752 : Int) atom0328Coded) (CoefficientMerge.scale (76032 : Int) atom0329Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69696 : Int) atom0330Coded) (CoefficientMerge.scale (179520 : Int) atom0331Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114048 : Int) atom0332Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6528 : Int) atom0333Coded) (CoefficientMerge.scale (128 : Int) atom0334Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1360 : Int) atom0335Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48 : Int) atom0336Coded) (CoefficientMerge.scale (1184 : Int) atom0337Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724 : Int) atom0338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (696 : Int) atom0339Coded) (CoefficientMerge.scale (1248 : Int) atom0340Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12480 : Int) atom0341Coded) (CoefficientMerge.scale (4224 : Int) atom0342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5280 : Int) atom0343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1332 : Int) atom0344Coded) (CoefficientMerge.scale (264 : Int) atom0345Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2187 : Int) atom0346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1644 : Int) atom0347Coded) (CoefficientMerge.scale (552 : Int) atom0348Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2148 : Int) atom0349Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1152 : Int) atom0350Coded) (CoefficientMerge.scale (1260 : Int) atom0351Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (936 : Int) atom0352Coded) (CoefficientMerge.scale (1344 : Int) atom0353Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1752 : Int) atom0354Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2160 : Int) atom0355Coded) (CoefficientMerge.scale (2568 : Int) atom0356Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (912 : Int) atom0357Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (596 : Int) atom0358Coded) (CoefficientMerge.scale (408 : Int) atom0359Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1248 : Int) atom0360Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1728 : Int) atom0361Coded) (CoefficientMerge.scale (1728 : Int) atom0362Coded))))))) := by decide +kernel
theorem block004_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) block004 := by
  rw [block004_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0320Coded_nonneg g hg hA hB) (atom0321Coded_nonneg g hg hA hB)) (add_nonneg (atom0322Coded_nonneg g hg hA hB) (add_nonneg (atom0323Coded_nonneg g hg hA hB) (atom0324Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0325Coded_nonneg g hg hA hB) (atom0326Coded_nonneg g hg hA hB)) (add_nonneg (atom0327Coded_nonneg g hg hA hB) (add_nonneg (atom0328Coded_nonneg g hg hA hB) (atom0329Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0330Coded_nonneg g hg hA hB) (atom0331Coded_nonneg g hg hA hB)) (add_nonneg (atom0332Coded_nonneg g hg hA hB) (add_nonneg (atom0333Coded_nonneg g hg hA hB) (atom0334Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0335Coded_nonneg g hg hA hB) (add_nonneg (atom0336Coded_nonneg g hg hA hB) (atom0337Coded_nonneg g hg hA hB))) (add_nonneg (atom0338Coded_nonneg g hg hA hB) (add_nonneg (atom0339Coded_nonneg g hg hA hB) (atom0340Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0341Coded_nonneg g hg hA hB) (atom0342Coded_nonneg g hg hA hB)) (add_nonneg (atom0343Coded_nonneg g hg hA hB) (add_nonneg (atom0344Coded_nonneg g hg hA hB) (atom0345Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0346Coded_nonneg g hg hA hB) (add_nonneg (atom0347Coded_nonneg g hg hA hB) (atom0348Coded_nonneg g hg hA hB))) (add_nonneg (atom0349Coded_nonneg g hg hA hB) (add_nonneg (atom0350Coded_nonneg g hg hA hB) (atom0351Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0352Coded_nonneg g hg hA hB) (atom0353Coded_nonneg g hg hA hB)) (add_nonneg (atom0354Coded_nonneg g hg hA hB) (add_nonneg (atom0355Coded_nonneg g hg hA hB) (atom0356Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0357Coded_nonneg g hg hA hB) (add_nonneg (atom0358Coded_nonneg g hg hA hB) (atom0359Coded_nonneg g hg hA hB))) (add_nonneg (atom0360Coded_nonneg g hg hA hB) (add_nonneg (atom0361Coded_nonneg g hg hA hB) (atom0362Coded_nonneg g hg hA hB)))))))

end APPT.Finite12
