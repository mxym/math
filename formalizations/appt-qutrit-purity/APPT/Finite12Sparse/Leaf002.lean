-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def atom0160 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0160 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0160 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0160, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0160_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167040 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160Coded : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 1))]
theorem atom0160Coded_decode : atom0160 = SparsePolynomial.decodeCubic 12 atom0160Coded := by decide +kernel
theorem atom0160Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (167040 : Int) atom0160Coded) := by
  have h := atom0160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0161 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0161 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0161 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0161, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0161_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223104 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161Coded : CoefficientMerge.Poly := [(nat_lit 368, Int.ofNat (nat_lit 1))]
theorem atom0161Coded_decode : atom0161 = SparsePolynomial.decodeCubic 12 atom0161Coded := by decide +kernel
theorem atom0161Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (223104 : Int) atom0161Coded) := by
  have h := atom0161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0162 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0162 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0162 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0162, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0162_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (231552 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162Coded : CoefficientMerge.Poly := [(nat_lit 369, Int.ofNat (nat_lit 1))]
theorem atom0162Coded_decode : atom0162 = SparsePolynomial.decodeCubic 12 atom0162Coded := by decide +kernel
theorem atom0162Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (231552 : Int) atom0162Coded) := by
  have h := atom0162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0163 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0163 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0163 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0163, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0163_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122400 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163Coded : CoefficientMerge.Poly := [(nat_lit 370, Int.ofNat (nat_lit 1))]
theorem atom0163Coded_decode : atom0163 = SparsePolynomial.decodeCubic 12 atom0163Coded := by decide +kernel
theorem atom0163Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (122400 : Int) atom0163Coded) := by
  have h := atom0163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0164 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0164 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0164 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0164, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0164_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225744 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164Coded : CoefficientMerge.Poly := [(nat_lit 371, Int.ofNat (nat_lit 1))]
theorem atom0164Coded_decode : atom0164 = SparsePolynomial.decodeCubic 12 atom0164Coded := by decide +kernel
theorem atom0164Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (225744 : Int) atom0164Coded) := by
  have h := atom0164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0165 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0165 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0165 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0165, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0165_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79488 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165Coded : CoefficientMerge.Poly := [(nat_lit 379, Int.ofNat (nat_lit 1))]
theorem atom0165Coded_decode : atom0165 = SparsePolynomial.decodeCubic 12 atom0165Coded := by decide +kernel
theorem atom0165Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (79488 : Int) atom0165Coded) := by
  have h := atom0165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0166 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0166 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0166 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0166, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0166_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (181440 : Int) atom0166) := by
  rw [SparsePolynomial.eval_scale, eval_atom0166]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0166Coded : CoefficientMerge.Poly := [(nat_lit 380, Int.ofNat (nat_lit 1))]
theorem atom0166Coded_decode : atom0166 = SparsePolynomial.decodeCubic 12 atom0166Coded := by decide +kernel
theorem atom0166Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (181440 : Int) atom0166Coded) := by
  have h := atom0166_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0166Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0167 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0167 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0167 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0167, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0167_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223488 : Int) atom0167) := by
  rw [SparsePolynomial.eval_scale, eval_atom0167]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0167Coded : CoefficientMerge.Poly := [(nat_lit 381, Int.ofNat (nat_lit 1))]
theorem atom0167Coded_decode : atom0167 = SparsePolynomial.decodeCubic 12 atom0167Coded := by decide +kernel
theorem atom0167Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (223488 : Int) atom0167Coded) := by
  have h := atom0167_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0167Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0168 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0168 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0168 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0168, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0168_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150336 : Int) atom0168) := by
  rw [SparsePolynomial.eval_scale, eval_atom0168]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0168Coded : CoefficientMerge.Poly := [(nat_lit 382, Int.ofNat (nat_lit 1))]
theorem atom0168Coded_decode : atom0168 = SparsePolynomial.decodeCubic 12 atom0168Coded := by decide +kernel
theorem atom0168Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (150336 : Int) atom0168Coded) := by
  have h := atom0168_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0168Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0169 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0169 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0169 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0169, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0169_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (195312 : Int) atom0169) := by
  rw [SparsePolynomial.eval_scale, eval_atom0169]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0169Coded : CoefficientMerge.Poly := [(nat_lit 383, Int.ofNat (nat_lit 1))]
theorem atom0169Coded_decode : atom0169 = SparsePolynomial.decodeCubic 12 atom0169Coded := by decide +kernel
theorem atom0169Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (195312 : Int) atom0169Coded) := by
  have h := atom0169_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0169Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0170 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0170 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0170 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0170, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0170_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119808 : Int) atom0170) := by
  rw [SparsePolynomial.eval_scale, eval_atom0170]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0170Coded : CoefficientMerge.Poly := [(nat_lit 392, Int.ofNat (nat_lit 1))]
theorem atom0170Coded_decode : atom0170 = SparsePolynomial.decodeCubic 12 atom0170Coded := by decide +kernel
theorem atom0170Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (119808 : Int) atom0170Coded) := by
  have h := atom0170_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0170Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0171 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0171 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0171 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0171, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0171_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (214272 : Int) atom0171) := by
  rw [SparsePolynomial.eval_scale, eval_atom0171]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0171Coded : CoefficientMerge.Poly := [(nat_lit 393, Int.ofNat (nat_lit 1))]
theorem atom0171Coded_decode : atom0171 = SparsePolynomial.decodeCubic 12 atom0171Coded := by decide +kernel
theorem atom0171Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (214272 : Int) atom0171Coded) := by
  have h := atom0171_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0171Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0172 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0172 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0172 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0172, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0172_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152160 : Int) atom0172) := by
  rw [SparsePolynomial.eval_scale, eval_atom0172]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0172Coded : CoefficientMerge.Poly := [(nat_lit 394, Int.ofNat (nat_lit 1))]
theorem atom0172Coded_decode : atom0172 = SparsePolynomial.decodeCubic 12 atom0172Coded := by decide +kernel
theorem atom0172Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (152160 : Int) atom0172Coded) := by
  have h := atom0172_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0172Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0173 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0173 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0173 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0173, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0173_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213168 : Int) atom0173) := by
  rw [SparsePolynomial.eval_scale, eval_atom0173]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0173Coded : CoefficientMerge.Poly := [(nat_lit 395, Int.ofNat (nat_lit 1))]
theorem atom0173Coded_decode : atom0173 = SparsePolynomial.decodeCubic 12 atom0173Coded := by decide +kernel
theorem atom0173Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (213168 : Int) atom0173Coded) := by
  have h := atom0173_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0173Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0174 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0174 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0174 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0174, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0174_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84672 : Int) atom0174) := by
  rw [SparsePolynomial.eval_scale, eval_atom0174]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0174Coded : CoefficientMerge.Poly := [(nat_lit 405, Int.ofNat (nat_lit 1))]
theorem atom0174Coded_decode : atom0174 = SparsePolynomial.decodeCubic 12 atom0174Coded := by decide +kernel
theorem atom0174Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (84672 : Int) atom0174Coded) := by
  have h := atom0174_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0174Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0175 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0175 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0175 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0175, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0175_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135504 : Int) atom0175) := by
  rw [SparsePolynomial.eval_scale, eval_atom0175]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0175Coded : CoefficientMerge.Poly := [(nat_lit 406, Int.ofNat (nat_lit 1))]
theorem atom0175Coded_decode : atom0175 = SparsePolynomial.decodeCubic 12 atom0175Coded := by decide +kernel
theorem atom0175Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (135504 : Int) atom0175Coded) := by
  have h := atom0175_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0175Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0176 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0176 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0176 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0176, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0176_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208848 : Int) atom0176) := by
  rw [SparsePolynomial.eval_scale, eval_atom0176]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0176Coded : CoefficientMerge.Poly := [(nat_lit 407, Int.ofNat (nat_lit 1))]
theorem atom0176Coded_decode : atom0176 = SparsePolynomial.decodeCubic 12 atom0176Coded := by decide +kernel
theorem atom0176Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (208848 : Int) atom0176Coded) := by
  have h := atom0176_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0176Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0177 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0177 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0177 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0177, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0177_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35712 : Int) atom0177) := by
  rw [SparsePolynomial.eval_scale, eval_atom0177]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0177Coded : CoefficientMerge.Poly := [(nat_lit 418, Int.ofNat (nat_lit 1))]
theorem atom0177Coded_decode : atom0177 = SparsePolynomial.decodeCubic 12 atom0177Coded := by decide +kernel
theorem atom0177Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (35712 : Int) atom0177Coded) := by
  have h := atom0177_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0177Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0178 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0178 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0178 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0178, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0178_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152808 : Int) atom0178) := by
  rw [SparsePolynomial.eval_scale, eval_atom0178]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0178Coded : CoefficientMerge.Poly := [(nat_lit 419, Int.ofNat (nat_lit 1))]
theorem atom0178Coded_decode : atom0178 = SparsePolynomial.decodeCubic 12 atom0178Coded := by decide +kernel
theorem atom0178Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (152808 : Int) atom0178Coded) := by
  have h := atom0178_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0178Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0179 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0179 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0179 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0179_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106704 : Int) atom0179) := by
  rw [SparsePolynomial.eval_scale, eval_atom0179]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0179Coded : CoefficientMerge.Poly := [(nat_lit 431, Int.ofNat (nat_lit 1))]
theorem atom0179Coded_decode : atom0179 = SparsePolynomial.decodeCubic 12 atom0179Coded := by decide +kernel
theorem atom0179Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (106704 : Int) atom0179Coded) := by
  have h := atom0179_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0179Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0180 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0180 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0180 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0180, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0180_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4608 : Int) atom0180) := by
  rw [SparsePolynomial.eval_scale, eval_atom0180]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0180Coded : CoefficientMerge.Poly := [(nat_lit 471, Int.ofNat (nat_lit 1))]
theorem atom0180Coded_decode : atom0180 = SparsePolynomial.decodeCubic 12 atom0180Coded := by decide +kernel
theorem atom0180Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (4608 : Int) atom0180Coded) := by
  have h := atom0180_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0180Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0181 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0181 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0181 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom0181, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0181_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36672 : Int) atom0181) := by
  rw [SparsePolynomial.eval_scale, eval_atom0181]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0181Coded : CoefficientMerge.Poly := [(nat_lit 474, Int.ofNat (nat_lit 1))]
theorem atom0181Coded_decode : atom0181 = SparsePolynomial.decodeCubic 12 atom0181Coded := by decide +kernel
theorem atom0181Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (36672 : Int) atom0181Coded) := by
  have h := atom0181_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0181Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0182 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0182 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0182 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom0182, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0182_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96 : Int) atom0182) := by
  rw [SparsePolynomial.eval_scale, eval_atom0182]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0182Coded : CoefficientMerge.Poly := [(nat_lit 475, Int.ofNat (nat_lit 1))]
theorem atom0182Coded_decode : atom0182 = SparsePolynomial.decodeCubic 12 atom0182Coded := by decide +kernel
theorem atom0182Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (96 : Int) atom0182Coded) := by
  have h := atom0182_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0182Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0183 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0183 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0183 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom0183, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0183_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10656 : Int) atom0183) := by
  rw [SparsePolynomial.eval_scale, eval_atom0183]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0183Coded : CoefficientMerge.Poly := [(nat_lit 476, Int.ofNat (nat_lit 1))]
theorem atom0183Coded_decode : atom0183 = SparsePolynomial.decodeCubic 12 atom0183Coded := by decide +kernel
theorem atom0183Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (10656 : Int) atom0183Coded) := by
  have h := atom0183_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0183Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0184 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0184 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0184 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom0184, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0184_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1584 : Int) atom0184) := by
  rw [SparsePolynomial.eval_scale, eval_atom0184]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0184Coded : CoefficientMerge.Poly := [(nat_lit 477, Int.ofNat (nat_lit 1))]
theorem atom0184Coded_decode : atom0184 = SparsePolynomial.decodeCubic 12 atom0184Coded := by decide +kernel
theorem atom0184Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1584 : Int) atom0184Coded) := by
  have h := atom0184_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0184Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0185 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0185 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0185 = ((g 3) * (g 3) * (g 11)) := by
  norm_num [atom0185, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0185_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1680 : Int) atom0185) := by
  rw [SparsePolynomial.eval_scale, eval_atom0185]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0185Coded : CoefficientMerge.Poly := [(nat_lit 479, Int.ofNat (nat_lit 1))]
theorem atom0185Coded_decode : atom0185 = SparsePolynomial.decodeCubic 12 atom0185Coded := by decide +kernel
theorem atom0185Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1680 : Int) atom0185Coded) := by
  have h := atom0185_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0185Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0186 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0186 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0186 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0186_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2112 : Int) atom0186) := by
  rw [SparsePolynomial.eval_scale, eval_atom0186]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0186Coded : CoefficientMerge.Poly := [(nat_lit 485, Int.ofNat (nat_lit 1))]
theorem atom0186Coded_decode : atom0186 = SparsePolynomial.decodeCubic 12 atom0186Coded := by decide +kernel
theorem atom0186Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (2112 : Int) atom0186Coded) := by
  have h := atom0186_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0186Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0187 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0187 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0187 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0187, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0187_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69696 : Int) atom0187) := by
  rw [SparsePolynomial.eval_scale, eval_atom0187]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0187Coded : CoefficientMerge.Poly := [(nat_lit 486, Int.ofNat (nat_lit 1))]
theorem atom0187Coded_decode : atom0187 = SparsePolynomial.decodeCubic 12 atom0187Coded := by decide +kernel
theorem atom0187Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (69696 : Int) atom0187Coded) := by
  have h := atom0187_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0187Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0188 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0188 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0188 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0188, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0188_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20352 : Int) atom0188) := by
  rw [SparsePolynomial.eval_scale, eval_atom0188]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0188Coded : CoefficientMerge.Poly := [(nat_lit 487, Int.ofNat (nat_lit 1))]
theorem atom0188Coded_decode : atom0188 = SparsePolynomial.decodeCubic 12 atom0188Coded := by decide +kernel
theorem atom0188Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (20352 : Int) atom0188Coded) := by
  have h := atom0188_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0188Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0189 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0189 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0189 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0189, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0189_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53184 : Int) atom0189) := by
  rw [SparsePolynomial.eval_scale, eval_atom0189]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0189Coded : CoefficientMerge.Poly := [(nat_lit 488, Int.ofNat (nat_lit 1))]
theorem atom0189Coded_decode : atom0189 = SparsePolynomial.decodeCubic 12 atom0189Coded := by decide +kernel
theorem atom0189Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (53184 : Int) atom0189Coded) := by
  have h := atom0189_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0189Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0190 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0190 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0190 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom0190, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0190_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48288 : Int) atom0190) := by
  rw [SparsePolynomial.eval_scale, eval_atom0190]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0190Coded : CoefficientMerge.Poly := [(nat_lit 489, Int.ofNat (nat_lit 1))]
theorem atom0190Coded_decode : atom0190 = SparsePolynomial.decodeCubic 12 atom0190Coded := by decide +kernel
theorem atom0190Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (48288 : Int) atom0190Coded) := by
  have h := atom0190_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0190Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0191 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0191 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0191 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom0191, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0191_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60528 : Int) atom0191) := by
  rw [SparsePolynomial.eval_scale, eval_atom0191]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0191Coded : CoefficientMerge.Poly := [(nat_lit 490, Int.ofNat (nat_lit 1))]
theorem atom0191Coded_decode : atom0191 = SparsePolynomial.decodeCubic 12 atom0191Coded := by decide +kernel
theorem atom0191Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (60528 : Int) atom0191Coded) := by
  have h := atom0191_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0191Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0192 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0192 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0192 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom0192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0192_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86640 : Int) atom0192) := by
  rw [SparsePolynomial.eval_scale, eval_atom0192]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0192Coded : CoefficientMerge.Poly := [(nat_lit 491, Int.ofNat (nat_lit 1))]
theorem atom0192Coded_decode : atom0192 = SparsePolynomial.decodeCubic 12 atom0192Coded := by decide +kernel
theorem atom0192Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (86640 : Int) atom0192Coded) := by
  have h := atom0192_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0192Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0193 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0193 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0193 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0193, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0193_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10368 : Int) atom0193) := by
  rw [SparsePolynomial.eval_scale, eval_atom0193]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0193Coded : CoefficientMerge.Poly := [(nat_lit 497, Int.ofNat (nat_lit 1))]
theorem atom0193Coded_decode : atom0193 = SparsePolynomial.decodeCubic 12 atom0193Coded := by decide +kernel
theorem atom0193Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (10368 : Int) atom0193Coded) := by
  have h := atom0193_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0193Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0194 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0194 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0194 = ((g 3) * (g 5) * (g 6)) := by
  norm_num [atom0194, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0194_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72960 : Int) atom0194) := by
  rw [SparsePolynomial.eval_scale, eval_atom0194]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0194Coded : CoefficientMerge.Poly := [(nat_lit 498, Int.ofNat (nat_lit 1))]
theorem atom0194Coded_decode : atom0194 = SparsePolynomial.decodeCubic 12 atom0194Coded := by decide +kernel
theorem atom0194Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (72960 : Int) atom0194Coded) := by
  have h := atom0194_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0194Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0195 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0195 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0195 = ((g 3) * (g 5) * (g 7)) := by
  norm_num [atom0195, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0195_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46848 : Int) atom0195) := by
  rw [SparsePolynomial.eval_scale, eval_atom0195]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0195Coded : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 1))]
theorem atom0195Coded_decode : atom0195 = SparsePolynomial.decodeCubic 12 atom0195Coded := by decide +kernel
theorem atom0195Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (46848 : Int) atom0195Coded) := by
  have h := atom0195_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0195Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0196 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0196 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0196 = ((g 3) * (g 5) * (g 8)) := by
  norm_num [atom0196, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0196_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83712 : Int) atom0196) := by
  rw [SparsePolynomial.eval_scale, eval_atom0196]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0196Coded : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 1))]
theorem atom0196Coded_decode : atom0196 = SparsePolynomial.decodeCubic 12 atom0196Coded := by decide +kernel
theorem atom0196Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (83712 : Int) atom0196Coded) := by
  have h := atom0196_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0196Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0197 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0197 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0197 = ((g 3) * (g 5) * (g 9)) := by
  norm_num [atom0197, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0197_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91392 : Int) atom0197) := by
  rw [SparsePolynomial.eval_scale, eval_atom0197]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0197Coded : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 1))]
theorem atom0197Coded_decode : atom0197 = SparsePolynomial.decodeCubic 12 atom0197Coded := by decide +kernel
theorem atom0197Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (91392 : Int) atom0197Coded) := by
  have h := atom0197_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0197Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0198 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0198 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0198 = ((g 3) * (g 5) * (g 10)) := by
  norm_num [atom0198, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0198_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102000 : Int) atom0198) := by
  rw [SparsePolynomial.eval_scale, eval_atom0198]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0198Coded : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 1))]
theorem atom0198Coded_decode : atom0198 = SparsePolynomial.decodeCubic 12 atom0198Coded := by decide +kernel
theorem atom0198Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (102000 : Int) atom0198Coded) := by
  have h := atom0198_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0198Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0199 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0199 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0199 = ((g 3) * (g 5) * (g 11)) := by
  norm_num [atom0199, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0199_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154368 : Int) atom0199) := by
  rw [SparsePolynomial.eval_scale, eval_atom0199]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0199Coded : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 1))]
theorem atom0199Coded_decode : atom0199 = SparsePolynomial.decodeCubic 12 atom0199Coded := by decide +kernel
theorem atom0199Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (154368 : Int) atom0199Coded) := by
  have h := atom0199_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0199Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0200 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0200 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0200 = ((g 3) * (g 6) * (g 6)) := by
  norm_num [atom0200, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0200_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77184 : Int) atom0200) := by
  rw [SparsePolynomial.eval_scale, eval_atom0200]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0200Coded : CoefficientMerge.Poly := [(nat_lit 510, Int.ofNat (nat_lit 1))]
theorem atom0200Coded_decode : atom0200 = SparsePolynomial.decodeCubic 12 atom0200Coded := by decide +kernel
theorem atom0200Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (77184 : Int) atom0200Coded) := by
  have h := atom0200_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0200Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0201 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0201 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0201 = ((g 3) * (g 6) * (g 7)) := by
  norm_num [atom0201, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0201_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121344 : Int) atom0201) := by
  rw [SparsePolynomial.eval_scale, eval_atom0201]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0201Coded : CoefficientMerge.Poly := [(nat_lit 511, Int.ofNat (nat_lit 1))]
theorem atom0201Coded_decode : atom0201 = SparsePolynomial.decodeCubic 12 atom0201Coded := by decide +kernel
theorem atom0201Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (121344 : Int) atom0201Coded) := by
  have h := atom0201_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0201Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0202 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0202 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0202 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom0202, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0202_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188160 : Int) atom0202) := by
  rw [SparsePolynomial.eval_scale, eval_atom0202]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0202Coded : CoefficientMerge.Poly := [(nat_lit 512, Int.ofNat (nat_lit 1))]
theorem atom0202Coded_decode : atom0202 = SparsePolynomial.decodeCubic 12 atom0202Coded := by decide +kernel
theorem atom0202Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (188160 : Int) atom0202Coded) := by
  have h := atom0202_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0202Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0203 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0203 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0203 = ((g 3) * (g 6) * (g 9)) := by
  norm_num [atom0203, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0203_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207360 : Int) atom0203) := by
  rw [SparsePolynomial.eval_scale, eval_atom0203]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0203Coded : CoefficientMerge.Poly := [(nat_lit 513, Int.ofNat (nat_lit 1))]
theorem atom0203Coded_decode : atom0203 = SparsePolynomial.decodeCubic 12 atom0203Coded := by decide +kernel
theorem atom0203Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (207360 : Int) atom0203Coded) := by
  have h := atom0203_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0203Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0204 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0204 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0204 = ((g 3) * (g 6) * (g 10)) := by
  norm_num [atom0204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0204_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115800 : Int) atom0204) := by
  rw [SparsePolynomial.eval_scale, eval_atom0204]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0204Coded : CoefficientMerge.Poly := [(nat_lit 514, Int.ofNat (nat_lit 1))]
theorem atom0204Coded_decode : atom0204 = SparsePolynomial.decodeCubic 12 atom0204Coded := by decide +kernel
theorem atom0204Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (115800 : Int) atom0204Coded) := by
  have h := atom0204_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0204Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0205 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0205 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0205 = ((g 3) * (g 6) * (g 11)) := by
  norm_num [atom0205, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0205_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217344 : Int) atom0205) := by
  rw [SparsePolynomial.eval_scale, eval_atom0205]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0205Coded : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 1))]
theorem atom0205Coded_decode : atom0205 = SparsePolynomial.decodeCubic 12 atom0205Coded := by decide +kernel
theorem atom0205Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (217344 : Int) atom0205Coded) := by
  have h := atom0205_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0205Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0206 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0206 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0206 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0206, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0206_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58752 : Int) atom0206) := by
  rw [SparsePolynomial.eval_scale, eval_atom0206]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0206Coded : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 1))]
theorem atom0206Coded_decode : atom0206 = SparsePolynomial.decodeCubic 12 atom0206Coded := by decide +kernel
theorem atom0206Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (58752 : Int) atom0206Coded) := by
  have h := atom0206_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0206Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0207 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0207 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0207 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom0207, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0207_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153600 : Int) atom0207) := by
  rw [SparsePolynomial.eval_scale, eval_atom0207]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0207Coded : CoefficientMerge.Poly := [(nat_lit 524, Int.ofNat (nat_lit 1))]
theorem atom0207Coded_decode : atom0207 = SparsePolynomial.decodeCubic 12 atom0207Coded := by decide +kernel
theorem atom0207Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (153600 : Int) atom0207Coded) := by
  have h := atom0207_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0207Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0208 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0208 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0208 = ((g 3) * (g 7) * (g 9)) := by
  norm_num [atom0208, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0208_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (209280 : Int) atom0208) := by
  rw [SparsePolynomial.eval_scale, eval_atom0208]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0208Coded : CoefficientMerge.Poly := [(nat_lit 525, Int.ofNat (nat_lit 1))]
theorem atom0208Coded_decode : atom0208 = SparsePolynomial.decodeCubic 12 atom0208Coded := by decide +kernel
theorem atom0208Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (209280 : Int) atom0208Coded) := by
  have h := atom0208_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0208Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0209 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0209 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0209 = ((g 3) * (g 7) * (g 10)) := by
  norm_num [atom0209, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0209_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149760 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0209Coded : CoefficientMerge.Poly := [(nat_lit 526, Int.ofNat (nat_lit 1))]
theorem atom0209Coded_decode : atom0209 = SparsePolynomial.decodeCubic 12 atom0209Coded := by decide +kernel
theorem atom0209Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (149760 : Int) atom0209Coded) := by
  have h := atom0209_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0209Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0210 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0210 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0210 = ((g 3) * (g 7) * (g 11)) := by
  norm_num [atom0210, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0210_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (204288 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210Coded : CoefficientMerge.Poly := [(nat_lit 527, Int.ofNat (nat_lit 1))]
theorem atom0210Coded_decode : atom0210 = SparsePolynomial.decodeCubic 12 atom0210Coded := by decide +kernel
theorem atom0210Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (204288 : Int) atom0210Coded) := by
  have h := atom0210_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0210Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0211 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0211 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0211 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0211, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0211_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109440 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211Coded : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 1))]
theorem atom0211Coded_decode : atom0211 = SparsePolynomial.decodeCubic 12 atom0211Coded := by decide +kernel
theorem atom0211Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (109440 : Int) atom0211Coded) := by
  have h := atom0211_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0211Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0212 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0212 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0212 = ((g 3) * (g 8) * (g 9)) := by
  norm_num [atom0212, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0212_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210048 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212Coded : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 1))]
theorem atom0212Coded_decode : atom0212 = SparsePolynomial.decodeCubic 12 atom0212Coded := by decide +kernel
theorem atom0212Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (210048 : Int) atom0212Coded) := by
  have h := atom0212_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0212Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0213 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0213 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0213 = ((g 3) * (g 8) * (g 10)) := by
  norm_num [atom0213, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0213_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157608 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213Coded : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 1))]
theorem atom0213Coded_decode : atom0213 = SparsePolynomial.decodeCubic 12 atom0213Coded := by decide +kernel
theorem atom0213Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (157608 : Int) atom0213Coded) := by
  have h := atom0213_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0213Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0214 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0214 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0214 = ((g 3) * (g 8) * (g 11)) := by
  norm_num [atom0214, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0214_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241152 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214Coded : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 1))]
theorem atom0214Coded_decode : atom0214 = SparsePolynomial.decodeCubic 12 atom0214Coded := by decide +kernel
theorem atom0214Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (241152 : Int) atom0214Coded) := by
  have h := atom0214_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0214Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0215 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0215 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0215 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom0215, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0215_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87552 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215Coded : CoefficientMerge.Poly := [(nat_lit 549, Int.ofNat (nat_lit 1))]
theorem atom0215Coded_decode : atom0215 = SparsePolynomial.decodeCubic 12 atom0215Coded := by decide +kernel
theorem atom0215Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (87552 : Int) atom0215Coded) := by
  have h := atom0215_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0215Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0216 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0216 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0216 = ((g 3) * (g 9) * (g 10)) := by
  norm_num [atom0216, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0216_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150396 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216Coded : CoefficientMerge.Poly := [(nat_lit 550, Int.ofNat (nat_lit 1))]
theorem atom0216Coded_decode : atom0216 = SparsePolynomial.decodeCubic 12 atom0216Coded := by decide +kernel
theorem atom0216Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (150396 : Int) atom0216Coded) := by
  have h := atom0216_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0216Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0217 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0217 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0217 = ((g 3) * (g 9) * (g 11)) := by
  norm_num [atom0217, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0217_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254208 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217Coded : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 1))]
theorem atom0217Coded_decode : atom0217 = SparsePolynomial.decodeCubic 12 atom0217Coded := by decide +kernel
theorem atom0217Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (254208 : Int) atom0217Coded) := by
  have h := atom0217_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0217Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0218 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0218 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0218 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom0218, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0218_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41040 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218Coded : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 1))]
theorem atom0218Coded_decode : atom0218 = SparsePolynomial.decodeCubic 12 atom0218Coded := by decide +kernel
theorem atom0218Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (41040 : Int) atom0218Coded) := by
  have h := atom0218_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0218Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0219 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0219 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0219 = ((g 3) * (g 10) * (g 11)) := by
  norm_num [atom0219, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0219_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (201786 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219Coded : CoefficientMerge.Poly := [(nat_lit 563, Int.ofNat (nat_lit 1))]
theorem atom0219Coded_decode : atom0219 = SparsePolynomial.decodeCubic 12 atom0219Coded := by decide +kernel
theorem atom0219Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (201786 : Int) atom0219Coded) := by
  have h := atom0219_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0219Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0220 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0220 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0220 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom0220, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0220_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152064 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220Coded : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 1))]
theorem atom0220Coded_decode : atom0220 = SparsePolynomial.decodeCubic 12 atom0220Coded := by decide +kernel
theorem atom0220Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (152064 : Int) atom0220Coded) := by
  have h := atom0220_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0220Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0221 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0221 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0221 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0221, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0221_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (384 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221Coded : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 1))]
theorem atom0221Coded_decode : atom0221 = SparsePolynomial.decodeCubic 12 atom0221Coded := by decide +kernel
theorem atom0221Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (384 : Int) atom0221Coded) := by
  have h := atom0221_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0221Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0222 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0222 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0222 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom0222, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0222_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21696 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222Coded : CoefficientMerge.Poly := [(nat_lit 630, Int.ofNat (nat_lit 1))]
theorem atom0222Coded_decode : atom0222 = SparsePolynomial.decodeCubic 12 atom0222Coded := by decide +kernel
theorem atom0222Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (21696 : Int) atom0222Coded) := by
  have h := atom0222_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0222Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0223 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0223 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0223 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom0223, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0223_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5568 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223Coded : CoefficientMerge.Poly := [(nat_lit 632, Int.ofNat (nat_lit 1))]
theorem atom0223Coded_decode : atom0223 = SparsePolynomial.decodeCubic 12 atom0223Coded := by decide +kernel
theorem atom0223Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (5568 : Int) atom0223Coded) := by
  have h := atom0223_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0223Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0224 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0224 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0224 = ((g 4) * (g 4) * (g 9)) := by
  norm_num [atom0224, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0224_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1152 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224Coded : CoefficientMerge.Poly := [(nat_lit 633, Int.ofNat (nat_lit 1))]
theorem atom0224Coded_decode : atom0224 = SparsePolynomial.decodeCubic 12 atom0224Coded := by decide +kernel
theorem atom0224Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (1152 : Int) atom0224Coded) := by
  have h := atom0224_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0224Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0225 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0225 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0225 = ((g 4) * (g 4) * (g 11)) := by
  norm_num [atom0225, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0225_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6144 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225Coded : CoefficientMerge.Poly := [(nat_lit 635, Int.ofNat (nat_lit 1))]
theorem atom0225Coded_decode : atom0225 = SparsePolynomial.decodeCubic 12 atom0225Coded := by decide +kernel
theorem atom0225Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (6144 : Int) atom0225Coded) := by
  have h := atom0225_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0225Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0226 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0226 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0226 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom0226, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0226_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3840 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226Coded : CoefficientMerge.Poly := [(nat_lit 641, Int.ofNat (nat_lit 1))]
theorem atom0226Coded_decode : atom0226 = SparsePolynomial.decodeCubic 12 atom0226Coded := by decide +kernel
theorem atom0226Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (3840 : Int) atom0226Coded) := by
  have h := atom0226_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0226Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0227 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0227 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0227 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom0227, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0227_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28320 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227Coded : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 1))]
theorem atom0227Coded_decode : atom0227 = SparsePolynomial.decodeCubic 12 atom0227Coded := by decide +kernel
theorem atom0227Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (28320 : Int) atom0227Coded) := by
  have h := atom0227_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0227Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0228 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0228 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0228 = ((g 4) * (g 5) * (g 7)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0228_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5760 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228Coded : CoefficientMerge.Poly := [(nat_lit 643, Int.ofNat (nat_lit 1))]
theorem atom0228Coded_decode : atom0228 = SparsePolynomial.decodeCubic 12 atom0228Coded := by decide +kernel
theorem atom0228Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (5760 : Int) atom0228Coded) := by
  have h := atom0228_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0228Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0229 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0229 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0229 = ((g 4) * (g 5) * (g 8)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0229_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28512 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229Coded : CoefficientMerge.Poly := [(nat_lit 644, Int.ofNat (nat_lit 1))]
theorem atom0229Coded_decode : atom0229 = SparsePolynomial.decodeCubic 12 atom0229Coded := by decide +kernel
theorem atom0229Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (28512 : Int) atom0229Coded) := by
  have h := atom0229_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0229Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0230 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0230 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0230 = ((g 4) * (g 5) * (g 9)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0230_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37488 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230Coded : CoefficientMerge.Poly := [(nat_lit 645, Int.ofNat (nat_lit 1))]
theorem atom0230Coded_decode : atom0230 = SparsePolynomial.decodeCubic 12 atom0230Coded := by decide +kernel
theorem atom0230Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (37488 : Int) atom0230Coded) := by
  have h := atom0230_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0230Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0231 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0231 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0231 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0231_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48768 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231Coded : CoefficientMerge.Poly := [(nat_lit 646, Int.ofNat (nat_lit 1))]
theorem atom0231Coded_decode : atom0231 = SparsePolynomial.decodeCubic 12 atom0231Coded := by decide +kernel
theorem atom0231Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (48768 : Int) atom0231Coded) := by
  have h := atom0231_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0231Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0232 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0232 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0232 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0232_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106344 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232Coded : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 1))]
theorem atom0232Coded_decode : atom0232 = SparsePolynomial.decodeCubic 12 atom0232Coded := by decide +kernel
theorem atom0232Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (106344 : Int) atom0232Coded) := by
  have h := atom0232_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0232Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0233 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0233 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0233 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0233_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48960 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233Coded : CoefficientMerge.Poly := [(nat_lit 654, Int.ofNat (nat_lit 1))]
theorem atom0233Coded_decode : atom0233 = SparsePolynomial.decodeCubic 12 atom0233Coded := by decide +kernel
theorem atom0233Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (48960 : Int) atom0233Coded) := by
  have h := atom0233_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0233Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0234 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0234 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0234 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0234_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80064 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234Coded : CoefficientMerge.Poly := [(nat_lit 655, Int.ofNat (nat_lit 1))]
theorem atom0234Coded_decode : atom0234 = SparsePolynomial.decodeCubic 12 atom0234Coded := by decide +kernel
theorem atom0234Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (80064 : Int) atom0234Coded) := by
  have h := atom0234_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0234Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0235 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0235 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0235 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0235_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153216 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235Coded : CoefficientMerge.Poly := [(nat_lit 656, Int.ofNat (nat_lit 1))]
theorem atom0235Coded_decode : atom0235 = SparsePolynomial.decodeCubic 12 atom0235Coded := by decide +kernel
theorem atom0235Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (153216 : Int) atom0235Coded) := by
  have h := atom0235_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0235Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0236 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0236 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0236 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0236_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183168 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236Coded : CoefficientMerge.Poly := [(nat_lit 657, Int.ofNat (nat_lit 1))]
theorem atom0236Coded_decode : atom0236 = SparsePolynomial.decodeCubic 12 atom0236Coded := by decide +kernel
theorem atom0236Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (183168 : Int) atom0236Coded) := by
  have h := atom0236_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0236Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0237 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0237 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0237 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0237_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102048 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237Coded : CoefficientMerge.Poly := [(nat_lit 658, Int.ofNat (nat_lit 1))]
theorem atom0237Coded_decode : atom0237 = SparsePolynomial.decodeCubic 12 atom0237Coded := by decide +kernel
theorem atom0237Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (102048 : Int) atom0237Coded) := by
  have h := atom0237_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0237Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0238 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0238 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0238 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0238_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (214656 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238Coded : CoefficientMerge.Poly := [(nat_lit 659, Int.ofNat (nat_lit 1))]
theorem atom0238Coded_decode : atom0238 = SparsePolynomial.decodeCubic 12 atom0238Coded := by decide +kernel
theorem atom0238Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (214656 : Int) atom0238Coded) := by
  have h := atom0238_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0238Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0239 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0239 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0239 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0239_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38016 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239Coded : CoefficientMerge.Poly := [(nat_lit 667, Int.ofNat (nat_lit 1))]
theorem atom0239Coded_decode : atom0239 = SparsePolynomial.decodeCubic 12 atom0239Coded := by decide +kernel
theorem atom0239Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (38016 : Int) atom0239Coded) := by
  have h := atom0239_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0239Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block002 : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 167040)), (nat_lit 368, Int.ofNat (nat_lit 223104)), (nat_lit 369, Int.ofNat (nat_lit 231552)), (nat_lit 370, Int.ofNat (nat_lit 122400)), (nat_lit 371, Int.ofNat (nat_lit 225744)), (nat_lit 379, Int.ofNat (nat_lit 79488)), (nat_lit 380, Int.ofNat (nat_lit 181440)), (nat_lit 381, Int.ofNat (nat_lit 223488)), (nat_lit 382, Int.ofNat (nat_lit 150336)), (nat_lit 383, Int.ofNat (nat_lit 195312)), (nat_lit 392, Int.ofNat (nat_lit 119808)), (nat_lit 393, Int.ofNat (nat_lit 214272)), (nat_lit 394, Int.ofNat (nat_lit 152160)), (nat_lit 395, Int.ofNat (nat_lit 213168)), (nat_lit 405, Int.ofNat (nat_lit 84672)), (nat_lit 406, Int.ofNat (nat_lit 135504)), (nat_lit 407, Int.ofNat (nat_lit 208848)), (nat_lit 418, Int.ofNat (nat_lit 35712)), (nat_lit 419, Int.ofNat (nat_lit 152808)), (nat_lit 431, Int.ofNat (nat_lit 106704)), (nat_lit 471, Int.ofNat (nat_lit 4608)), (nat_lit 474, Int.ofNat (nat_lit 36672)), (nat_lit 475, Int.ofNat (nat_lit 96)), (nat_lit 476, Int.ofNat (nat_lit 10656)), (nat_lit 477, Int.ofNat (nat_lit 1584)), (nat_lit 479, Int.ofNat (nat_lit 1680)), (nat_lit 485, Int.ofNat (nat_lit 2112)), (nat_lit 486, Int.ofNat (nat_lit 69696)), (nat_lit 487, Int.ofNat (nat_lit 20352)), (nat_lit 488, Int.ofNat (nat_lit 53184)), (nat_lit 489, Int.ofNat (nat_lit 48288)), (nat_lit 490, Int.ofNat (nat_lit 60528)), (nat_lit 491, Int.ofNat (nat_lit 86640)), (nat_lit 497, Int.ofNat (nat_lit 10368)), (nat_lit 498, Int.ofNat (nat_lit 72960)), (nat_lit 499, Int.ofNat (nat_lit 46848)), (nat_lit 500, Int.ofNat (nat_lit 83712)), (nat_lit 501, Int.ofNat (nat_lit 91392)), (nat_lit 502, Int.ofNat (nat_lit 102000)), (nat_lit 503, Int.ofNat (nat_lit 154368)), (nat_lit 510, Int.ofNat (nat_lit 77184)), (nat_lit 511, Int.ofNat (nat_lit 121344)), (nat_lit 512, Int.ofNat (nat_lit 188160)), (nat_lit 513, Int.ofNat (nat_lit 207360)), (nat_lit 514, Int.ofNat (nat_lit 115800)), (nat_lit 515, Int.ofNat (nat_lit 217344)), (nat_lit 523, Int.ofNat (nat_lit 58752)), (nat_lit 524, Int.ofNat (nat_lit 153600)), (nat_lit 525, Int.ofNat (nat_lit 209280)), (nat_lit 526, Int.ofNat (nat_lit 149760)), (nat_lit 527, Int.ofNat (nat_lit 204288)), (nat_lit 536, Int.ofNat (nat_lit 109440)), (nat_lit 537, Int.ofNat (nat_lit 210048)), (nat_lit 538, Int.ofNat (nat_lit 157608)), (nat_lit 539, Int.ofNat (nat_lit 241152)), (nat_lit 549, Int.ofNat (nat_lit 87552)), (nat_lit 550, Int.ofNat (nat_lit 150396)), (nat_lit 551, Int.ofNat (nat_lit 254208)), (nat_lit 562, Int.ofNat (nat_lit 41040)), (nat_lit 563, Int.ofNat (nat_lit 201786)), (nat_lit 575, Int.ofNat (nat_lit 152064)), (nat_lit 628, Int.ofNat (nat_lit 384)), (nat_lit 630, Int.ofNat (nat_lit 21696)), (nat_lit 632, Int.ofNat (nat_lit 5568)), (nat_lit 633, Int.ofNat (nat_lit 1152)), (nat_lit 635, Int.ofNat (nat_lit 6144)), (nat_lit 641, Int.ofNat (nat_lit 3840)), (nat_lit 642, Int.ofNat (nat_lit 28320)), (nat_lit 643, Int.ofNat (nat_lit 5760)), (nat_lit 644, Int.ofNat (nat_lit 28512)), (nat_lit 645, Int.ofNat (nat_lit 37488)), (nat_lit 646, Int.ofNat (nat_lit 48768)), (nat_lit 647, Int.ofNat (nat_lit 106344)), (nat_lit 654, Int.ofNat (nat_lit 48960)), (nat_lit 655, Int.ofNat (nat_lit 80064)), (nat_lit 656, Int.ofNat (nat_lit 153216)), (nat_lit 657, Int.ofNat (nat_lit 183168)), (nat_lit 658, Int.ofNat (nat_lit 102048)), (nat_lit 659, Int.ofNat (nat_lit 214656)), (nat_lit 667, Int.ofNat (nat_lit 38016))]
def block002_data_flat000 : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 167040))]
theorem block002_data_flat000_step : block002_data_flat000 = (CoefficientMerge.scale (167040 : Int) atom0160Coded) := by decide +kernel
theorem block002_data_flat000_original : block002_data_flat000 = (CoefficientMerge.scale (167040 : Int) atom0160Coded) := by
  rw [block002_data_flat000_step]
def block002_data_flat001 : CoefficientMerge.Poly := [(nat_lit 368, Int.ofNat (nat_lit 223104))]
theorem block002_data_flat001_step : block002_data_flat001 = (CoefficientMerge.scale (223104 : Int) atom0161Coded) := by decide +kernel
theorem block002_data_flat001_original : block002_data_flat001 = (CoefficientMerge.scale (223104 : Int) atom0161Coded) := by
  rw [block002_data_flat001_step]
def block002_data_flat002 : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 167040)), (nat_lit 368, Int.ofNat (nat_lit 223104))]
theorem block002_data_flat002_step : block002_data_flat002 = (CoefficientMerge.fastMerge block002_data_flat000 block002_data_flat001) := by decide +kernel
theorem block002_data_flat002_original : block002_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (167040 : Int) atom0160Coded) (CoefficientMerge.scale (223104 : Int) atom0161Coded)) := by
  rw [block002_data_flat002_step, block002_data_flat000_original, block002_data_flat001_original]
def block002_data_flat003 : CoefficientMerge.Poly := [(nat_lit 369, Int.ofNat (nat_lit 231552))]
theorem block002_data_flat003_step : block002_data_flat003 = (CoefficientMerge.scale (231552 : Int) atom0162Coded) := by decide +kernel
theorem block002_data_flat003_original : block002_data_flat003 = (CoefficientMerge.scale (231552 : Int) atom0162Coded) := by
  rw [block002_data_flat003_step]
def block002_data_flat004 : CoefficientMerge.Poly := [(nat_lit 370, Int.ofNat (nat_lit 122400))]
theorem block002_data_flat004_step : block002_data_flat004 = (CoefficientMerge.scale (122400 : Int) atom0163Coded) := by decide +kernel
theorem block002_data_flat004_original : block002_data_flat004 = (CoefficientMerge.scale (122400 : Int) atom0163Coded) := by
  rw [block002_data_flat004_step]
def block002_data_flat005 : CoefficientMerge.Poly := [(nat_lit 371, Int.ofNat (nat_lit 225744))]
theorem block002_data_flat005_step : block002_data_flat005 = (CoefficientMerge.scale (225744 : Int) atom0164Coded) := by decide +kernel
theorem block002_data_flat005_original : block002_data_flat005 = (CoefficientMerge.scale (225744 : Int) atom0164Coded) := by
  rw [block002_data_flat005_step]
def block002_data_flat006 : CoefficientMerge.Poly := [(nat_lit 370, Int.ofNat (nat_lit 122400)), (nat_lit 371, Int.ofNat (nat_lit 225744))]
theorem block002_data_flat006_step : block002_data_flat006 = (CoefficientMerge.fastMerge block002_data_flat004 block002_data_flat005) := by decide +kernel
theorem block002_data_flat006_original : block002_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (122400 : Int) atom0163Coded) (CoefficientMerge.scale (225744 : Int) atom0164Coded)) := by
  rw [block002_data_flat006_step, block002_data_flat004_original, block002_data_flat005_original]
def block002_data_flat007 : CoefficientMerge.Poly := [(nat_lit 369, Int.ofNat (nat_lit 231552)), (nat_lit 370, Int.ofNat (nat_lit 122400)), (nat_lit 371, Int.ofNat (nat_lit 225744))]
theorem block002_data_flat007_step : block002_data_flat007 = (CoefficientMerge.fastMerge block002_data_flat003 block002_data_flat006) := by decide +kernel
theorem block002_data_flat007_original : block002_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (231552 : Int) atom0162Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122400 : Int) atom0163Coded) (CoefficientMerge.scale (225744 : Int) atom0164Coded))) := by
  rw [block002_data_flat007_step, block002_data_flat003_original, block002_data_flat006_original]
def block002_data_flat008 : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 167040)), (nat_lit 368, Int.ofNat (nat_lit 223104)), (nat_lit 369, Int.ofNat (nat_lit 231552)), (nat_lit 370, Int.ofNat (nat_lit 122400)), (nat_lit 371, Int.ofNat (nat_lit 225744))]
theorem block002_data_flat008_step : block002_data_flat008 = (CoefficientMerge.fastMerge block002_data_flat002 block002_data_flat007) := by decide +kernel
theorem block002_data_flat008_original : block002_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167040 : Int) atom0160Coded) (CoefficientMerge.scale (223104 : Int) atom0161Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231552 : Int) atom0162Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122400 : Int) atom0163Coded) (CoefficientMerge.scale (225744 : Int) atom0164Coded)))) := by
  rw [block002_data_flat008_step, block002_data_flat002_original, block002_data_flat007_original]
def block002_data_flat009 : CoefficientMerge.Poly := [(nat_lit 379, Int.ofNat (nat_lit 79488))]
theorem block002_data_flat009_step : block002_data_flat009 = (CoefficientMerge.scale (79488 : Int) atom0165Coded) := by decide +kernel
theorem block002_data_flat009_original : block002_data_flat009 = (CoefficientMerge.scale (79488 : Int) atom0165Coded) := by
  rw [block002_data_flat009_step]
def block002_data_flat010 : CoefficientMerge.Poly := [(nat_lit 380, Int.ofNat (nat_lit 181440))]
theorem block002_data_flat010_step : block002_data_flat010 = (CoefficientMerge.scale (181440 : Int) atom0166Coded) := by decide +kernel
theorem block002_data_flat010_original : block002_data_flat010 = (CoefficientMerge.scale (181440 : Int) atom0166Coded) := by
  rw [block002_data_flat010_step]
def block002_data_flat011 : CoefficientMerge.Poly := [(nat_lit 379, Int.ofNat (nat_lit 79488)), (nat_lit 380, Int.ofNat (nat_lit 181440))]
theorem block002_data_flat011_step : block002_data_flat011 = (CoefficientMerge.fastMerge block002_data_flat009 block002_data_flat010) := by decide +kernel
theorem block002_data_flat011_original : block002_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (79488 : Int) atom0165Coded) (CoefficientMerge.scale (181440 : Int) atom0166Coded)) := by
  rw [block002_data_flat011_step, block002_data_flat009_original, block002_data_flat010_original]
def block002_data_flat012 : CoefficientMerge.Poly := [(nat_lit 381, Int.ofNat (nat_lit 223488))]
theorem block002_data_flat012_step : block002_data_flat012 = (CoefficientMerge.scale (223488 : Int) atom0167Coded) := by decide +kernel
theorem block002_data_flat012_original : block002_data_flat012 = (CoefficientMerge.scale (223488 : Int) atom0167Coded) := by
  rw [block002_data_flat012_step]
def block002_data_flat013 : CoefficientMerge.Poly := [(nat_lit 382, Int.ofNat (nat_lit 150336))]
theorem block002_data_flat013_step : block002_data_flat013 = (CoefficientMerge.scale (150336 : Int) atom0168Coded) := by decide +kernel
theorem block002_data_flat013_original : block002_data_flat013 = (CoefficientMerge.scale (150336 : Int) atom0168Coded) := by
  rw [block002_data_flat013_step]
def block002_data_flat014 : CoefficientMerge.Poly := [(nat_lit 383, Int.ofNat (nat_lit 195312))]
theorem block002_data_flat014_step : block002_data_flat014 = (CoefficientMerge.scale (195312 : Int) atom0169Coded) := by decide +kernel
theorem block002_data_flat014_original : block002_data_flat014 = (CoefficientMerge.scale (195312 : Int) atom0169Coded) := by
  rw [block002_data_flat014_step]
def block002_data_flat015 : CoefficientMerge.Poly := [(nat_lit 382, Int.ofNat (nat_lit 150336)), (nat_lit 383, Int.ofNat (nat_lit 195312))]
theorem block002_data_flat015_step : block002_data_flat015 = (CoefficientMerge.fastMerge block002_data_flat013 block002_data_flat014) := by decide +kernel
theorem block002_data_flat015_original : block002_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (150336 : Int) atom0168Coded) (CoefficientMerge.scale (195312 : Int) atom0169Coded)) := by
  rw [block002_data_flat015_step, block002_data_flat013_original, block002_data_flat014_original]
def block002_data_flat016 : CoefficientMerge.Poly := [(nat_lit 381, Int.ofNat (nat_lit 223488)), (nat_lit 382, Int.ofNat (nat_lit 150336)), (nat_lit 383, Int.ofNat (nat_lit 195312))]
theorem block002_data_flat016_step : block002_data_flat016 = (CoefficientMerge.fastMerge block002_data_flat012 block002_data_flat015) := by decide +kernel
theorem block002_data_flat016_original : block002_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (223488 : Int) atom0167Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150336 : Int) atom0168Coded) (CoefficientMerge.scale (195312 : Int) atom0169Coded))) := by
  rw [block002_data_flat016_step, block002_data_flat012_original, block002_data_flat015_original]
def block002_data_flat017 : CoefficientMerge.Poly := [(nat_lit 379, Int.ofNat (nat_lit 79488)), (nat_lit 380, Int.ofNat (nat_lit 181440)), (nat_lit 381, Int.ofNat (nat_lit 223488)), (nat_lit 382, Int.ofNat (nat_lit 150336)), (nat_lit 383, Int.ofNat (nat_lit 195312))]
theorem block002_data_flat017_step : block002_data_flat017 = (CoefficientMerge.fastMerge block002_data_flat011 block002_data_flat016) := by decide +kernel
theorem block002_data_flat017_original : block002_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79488 : Int) atom0165Coded) (CoefficientMerge.scale (181440 : Int) atom0166Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223488 : Int) atom0167Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150336 : Int) atom0168Coded) (CoefficientMerge.scale (195312 : Int) atom0169Coded)))) := by
  rw [block002_data_flat017_step, block002_data_flat011_original, block002_data_flat016_original]
def block002_data_flat018 : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 167040)), (nat_lit 368, Int.ofNat (nat_lit 223104)), (nat_lit 369, Int.ofNat (nat_lit 231552)), (nat_lit 370, Int.ofNat (nat_lit 122400)), (nat_lit 371, Int.ofNat (nat_lit 225744)), (nat_lit 379, Int.ofNat (nat_lit 79488)), (nat_lit 380, Int.ofNat (nat_lit 181440)), (nat_lit 381, Int.ofNat (nat_lit 223488)), (nat_lit 382, Int.ofNat (nat_lit 150336)), (nat_lit 383, Int.ofNat (nat_lit 195312))]
theorem block002_data_flat018_step : block002_data_flat018 = (CoefficientMerge.fastMerge block002_data_flat008 block002_data_flat017) := by decide +kernel
theorem block002_data_flat018_original : block002_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167040 : Int) atom0160Coded) (CoefficientMerge.scale (223104 : Int) atom0161Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231552 : Int) atom0162Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122400 : Int) atom0163Coded) (CoefficientMerge.scale (225744 : Int) atom0164Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79488 : Int) atom0165Coded) (CoefficientMerge.scale (181440 : Int) atom0166Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223488 : Int) atom0167Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150336 : Int) atom0168Coded) (CoefficientMerge.scale (195312 : Int) atom0169Coded))))) := by
  rw [block002_data_flat018_step, block002_data_flat008_original, block002_data_flat017_original]
def block002_data_flat019 : CoefficientMerge.Poly := [(nat_lit 392, Int.ofNat (nat_lit 119808))]
theorem block002_data_flat019_step : block002_data_flat019 = (CoefficientMerge.scale (119808 : Int) atom0170Coded) := by decide +kernel
theorem block002_data_flat019_original : block002_data_flat019 = (CoefficientMerge.scale (119808 : Int) atom0170Coded) := by
  rw [block002_data_flat019_step]
def block002_data_flat020 : CoefficientMerge.Poly := [(nat_lit 393, Int.ofNat (nat_lit 214272))]
theorem block002_data_flat020_step : block002_data_flat020 = (CoefficientMerge.scale (214272 : Int) atom0171Coded) := by decide +kernel
theorem block002_data_flat020_original : block002_data_flat020 = (CoefficientMerge.scale (214272 : Int) atom0171Coded) := by
  rw [block002_data_flat020_step]
def block002_data_flat021 : CoefficientMerge.Poly := [(nat_lit 392, Int.ofNat (nat_lit 119808)), (nat_lit 393, Int.ofNat (nat_lit 214272))]
theorem block002_data_flat021_step : block002_data_flat021 = (CoefficientMerge.fastMerge block002_data_flat019 block002_data_flat020) := by decide +kernel
theorem block002_data_flat021_original : block002_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (119808 : Int) atom0170Coded) (CoefficientMerge.scale (214272 : Int) atom0171Coded)) := by
  rw [block002_data_flat021_step, block002_data_flat019_original, block002_data_flat020_original]
def block002_data_flat022 : CoefficientMerge.Poly := [(nat_lit 394, Int.ofNat (nat_lit 152160))]
theorem block002_data_flat022_step : block002_data_flat022 = (CoefficientMerge.scale (152160 : Int) atom0172Coded) := by decide +kernel
theorem block002_data_flat022_original : block002_data_flat022 = (CoefficientMerge.scale (152160 : Int) atom0172Coded) := by
  rw [block002_data_flat022_step]
def block002_data_flat023 : CoefficientMerge.Poly := [(nat_lit 395, Int.ofNat (nat_lit 213168))]
theorem block002_data_flat023_step : block002_data_flat023 = (CoefficientMerge.scale (213168 : Int) atom0173Coded) := by decide +kernel
theorem block002_data_flat023_original : block002_data_flat023 = (CoefficientMerge.scale (213168 : Int) atom0173Coded) := by
  rw [block002_data_flat023_step]
def block002_data_flat024 : CoefficientMerge.Poly := [(nat_lit 405, Int.ofNat (nat_lit 84672))]
theorem block002_data_flat024_step : block002_data_flat024 = (CoefficientMerge.scale (84672 : Int) atom0174Coded) := by decide +kernel
theorem block002_data_flat024_original : block002_data_flat024 = (CoefficientMerge.scale (84672 : Int) atom0174Coded) := by
  rw [block002_data_flat024_step]
def block002_data_flat025 : CoefficientMerge.Poly := [(nat_lit 395, Int.ofNat (nat_lit 213168)), (nat_lit 405, Int.ofNat (nat_lit 84672))]
theorem block002_data_flat025_step : block002_data_flat025 = (CoefficientMerge.fastMerge block002_data_flat023 block002_data_flat024) := by decide +kernel
theorem block002_data_flat025_original : block002_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (213168 : Int) atom0173Coded) (CoefficientMerge.scale (84672 : Int) atom0174Coded)) := by
  rw [block002_data_flat025_step, block002_data_flat023_original, block002_data_flat024_original]
def block002_data_flat026 : CoefficientMerge.Poly := [(nat_lit 394, Int.ofNat (nat_lit 152160)), (nat_lit 395, Int.ofNat (nat_lit 213168)), (nat_lit 405, Int.ofNat (nat_lit 84672))]
theorem block002_data_flat026_step : block002_data_flat026 = (CoefficientMerge.fastMerge block002_data_flat022 block002_data_flat025) := by decide +kernel
theorem block002_data_flat026_original : block002_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (152160 : Int) atom0172Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213168 : Int) atom0173Coded) (CoefficientMerge.scale (84672 : Int) atom0174Coded))) := by
  rw [block002_data_flat026_step, block002_data_flat022_original, block002_data_flat025_original]
def block002_data_flat027 : CoefficientMerge.Poly := [(nat_lit 392, Int.ofNat (nat_lit 119808)), (nat_lit 393, Int.ofNat (nat_lit 214272)), (nat_lit 394, Int.ofNat (nat_lit 152160)), (nat_lit 395, Int.ofNat (nat_lit 213168)), (nat_lit 405, Int.ofNat (nat_lit 84672))]
theorem block002_data_flat027_step : block002_data_flat027 = (CoefficientMerge.fastMerge block002_data_flat021 block002_data_flat026) := by decide +kernel
theorem block002_data_flat027_original : block002_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (119808 : Int) atom0170Coded) (CoefficientMerge.scale (214272 : Int) atom0171Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152160 : Int) atom0172Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213168 : Int) atom0173Coded) (CoefficientMerge.scale (84672 : Int) atom0174Coded)))) := by
  rw [block002_data_flat027_step, block002_data_flat021_original, block002_data_flat026_original]
def block002_data_flat028 : CoefficientMerge.Poly := [(nat_lit 406, Int.ofNat (nat_lit 135504))]
theorem block002_data_flat028_step : block002_data_flat028 = (CoefficientMerge.scale (135504 : Int) atom0175Coded) := by decide +kernel
theorem block002_data_flat028_original : block002_data_flat028 = (CoefficientMerge.scale (135504 : Int) atom0175Coded) := by
  rw [block002_data_flat028_step]
def block002_data_flat029 : CoefficientMerge.Poly := [(nat_lit 407, Int.ofNat (nat_lit 208848))]
theorem block002_data_flat029_step : block002_data_flat029 = (CoefficientMerge.scale (208848 : Int) atom0176Coded) := by decide +kernel
theorem block002_data_flat029_original : block002_data_flat029 = (CoefficientMerge.scale (208848 : Int) atom0176Coded) := by
  rw [block002_data_flat029_step]
def block002_data_flat030 : CoefficientMerge.Poly := [(nat_lit 406, Int.ofNat (nat_lit 135504)), (nat_lit 407, Int.ofNat (nat_lit 208848))]
theorem block002_data_flat030_step : block002_data_flat030 = (CoefficientMerge.fastMerge block002_data_flat028 block002_data_flat029) := by decide +kernel
theorem block002_data_flat030_original : block002_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (135504 : Int) atom0175Coded) (CoefficientMerge.scale (208848 : Int) atom0176Coded)) := by
  rw [block002_data_flat030_step, block002_data_flat028_original, block002_data_flat029_original]
def block002_data_flat031 : CoefficientMerge.Poly := [(nat_lit 418, Int.ofNat (nat_lit 35712))]
theorem block002_data_flat031_step : block002_data_flat031 = (CoefficientMerge.scale (35712 : Int) atom0177Coded) := by decide +kernel
theorem block002_data_flat031_original : block002_data_flat031 = (CoefficientMerge.scale (35712 : Int) atom0177Coded) := by
  rw [block002_data_flat031_step]
def block002_data_flat032 : CoefficientMerge.Poly := [(nat_lit 419, Int.ofNat (nat_lit 152808))]
theorem block002_data_flat032_step : block002_data_flat032 = (CoefficientMerge.scale (152808 : Int) atom0178Coded) := by decide +kernel
theorem block002_data_flat032_original : block002_data_flat032 = (CoefficientMerge.scale (152808 : Int) atom0178Coded) := by
  rw [block002_data_flat032_step]
def block002_data_flat033 : CoefficientMerge.Poly := [(nat_lit 431, Int.ofNat (nat_lit 106704))]
theorem block002_data_flat033_step : block002_data_flat033 = (CoefficientMerge.scale (106704 : Int) atom0179Coded) := by decide +kernel
theorem block002_data_flat033_original : block002_data_flat033 = (CoefficientMerge.scale (106704 : Int) atom0179Coded) := by
  rw [block002_data_flat033_step]
def block002_data_flat034 : CoefficientMerge.Poly := [(nat_lit 419, Int.ofNat (nat_lit 152808)), (nat_lit 431, Int.ofNat (nat_lit 106704))]
theorem block002_data_flat034_step : block002_data_flat034 = (CoefficientMerge.fastMerge block002_data_flat032 block002_data_flat033) := by decide +kernel
theorem block002_data_flat034_original : block002_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808 : Int) atom0178Coded) (CoefficientMerge.scale (106704 : Int) atom0179Coded)) := by
  rw [block002_data_flat034_step, block002_data_flat032_original, block002_data_flat033_original]
def block002_data_flat035 : CoefficientMerge.Poly := [(nat_lit 418, Int.ofNat (nat_lit 35712)), (nat_lit 419, Int.ofNat (nat_lit 152808)), (nat_lit 431, Int.ofNat (nat_lit 106704))]
theorem block002_data_flat035_step : block002_data_flat035 = (CoefficientMerge.fastMerge block002_data_flat031 block002_data_flat034) := by decide +kernel
theorem block002_data_flat035_original : block002_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35712 : Int) atom0177Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808 : Int) atom0178Coded) (CoefficientMerge.scale (106704 : Int) atom0179Coded))) := by
  rw [block002_data_flat035_step, block002_data_flat031_original, block002_data_flat034_original]
def block002_data_flat036 : CoefficientMerge.Poly := [(nat_lit 406, Int.ofNat (nat_lit 135504)), (nat_lit 407, Int.ofNat (nat_lit 208848)), (nat_lit 418, Int.ofNat (nat_lit 35712)), (nat_lit 419, Int.ofNat (nat_lit 152808)), (nat_lit 431, Int.ofNat (nat_lit 106704))]
theorem block002_data_flat036_step : block002_data_flat036 = (CoefficientMerge.fastMerge block002_data_flat030 block002_data_flat035) := by decide +kernel
theorem block002_data_flat036_original : block002_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (135504 : Int) atom0175Coded) (CoefficientMerge.scale (208848 : Int) atom0176Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35712 : Int) atom0177Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808 : Int) atom0178Coded) (CoefficientMerge.scale (106704 : Int) atom0179Coded)))) := by
  rw [block002_data_flat036_step, block002_data_flat030_original, block002_data_flat035_original]
def block002_data_flat037 : CoefficientMerge.Poly := [(nat_lit 392, Int.ofNat (nat_lit 119808)), (nat_lit 393, Int.ofNat (nat_lit 214272)), (nat_lit 394, Int.ofNat (nat_lit 152160)), (nat_lit 395, Int.ofNat (nat_lit 213168)), (nat_lit 405, Int.ofNat (nat_lit 84672)), (nat_lit 406, Int.ofNat (nat_lit 135504)), (nat_lit 407, Int.ofNat (nat_lit 208848)), (nat_lit 418, Int.ofNat (nat_lit 35712)), (nat_lit 419, Int.ofNat (nat_lit 152808)), (nat_lit 431, Int.ofNat (nat_lit 106704))]
theorem block002_data_flat037_step : block002_data_flat037 = (CoefficientMerge.fastMerge block002_data_flat027 block002_data_flat036) := by decide +kernel
theorem block002_data_flat037_original : block002_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (119808 : Int) atom0170Coded) (CoefficientMerge.scale (214272 : Int) atom0171Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152160 : Int) atom0172Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213168 : Int) atom0173Coded) (CoefficientMerge.scale (84672 : Int) atom0174Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (135504 : Int) atom0175Coded) (CoefficientMerge.scale (208848 : Int) atom0176Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35712 : Int) atom0177Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808 : Int) atom0178Coded) (CoefficientMerge.scale (106704 : Int) atom0179Coded))))) := by
  rw [block002_data_flat037_step, block002_data_flat027_original, block002_data_flat036_original]
def block002_data_flat038 : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 167040)), (nat_lit 368, Int.ofNat (nat_lit 223104)), (nat_lit 369, Int.ofNat (nat_lit 231552)), (nat_lit 370, Int.ofNat (nat_lit 122400)), (nat_lit 371, Int.ofNat (nat_lit 225744)), (nat_lit 379, Int.ofNat (nat_lit 79488)), (nat_lit 380, Int.ofNat (nat_lit 181440)), (nat_lit 381, Int.ofNat (nat_lit 223488)), (nat_lit 382, Int.ofNat (nat_lit 150336)), (nat_lit 383, Int.ofNat (nat_lit 195312)), (nat_lit 392, Int.ofNat (nat_lit 119808)), (nat_lit 393, Int.ofNat (nat_lit 214272)), (nat_lit 394, Int.ofNat (nat_lit 152160)), (nat_lit 395, Int.ofNat (nat_lit 213168)), (nat_lit 405, Int.ofNat (nat_lit 84672)), (nat_lit 406, Int.ofNat (nat_lit 135504)), (nat_lit 407, Int.ofNat (nat_lit 208848)), (nat_lit 418, Int.ofNat (nat_lit 35712)), (nat_lit 419, Int.ofNat (nat_lit 152808)), (nat_lit 431, Int.ofNat (nat_lit 106704))]
theorem block002_data_flat038_step : block002_data_flat038 = (CoefficientMerge.fastMerge block002_data_flat018 block002_data_flat037) := by decide +kernel
theorem block002_data_flat038_original : block002_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167040 : Int) atom0160Coded) (CoefficientMerge.scale (223104 : Int) atom0161Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231552 : Int) atom0162Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122400 : Int) atom0163Coded) (CoefficientMerge.scale (225744 : Int) atom0164Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79488 : Int) atom0165Coded) (CoefficientMerge.scale (181440 : Int) atom0166Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223488 : Int) atom0167Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150336 : Int) atom0168Coded) (CoefficientMerge.scale (195312 : Int) atom0169Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (119808 : Int) atom0170Coded) (CoefficientMerge.scale (214272 : Int) atom0171Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152160 : Int) atom0172Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213168 : Int) atom0173Coded) (CoefficientMerge.scale (84672 : Int) atom0174Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (135504 : Int) atom0175Coded) (CoefficientMerge.scale (208848 : Int) atom0176Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35712 : Int) atom0177Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808 : Int) atom0178Coded) (CoefficientMerge.scale (106704 : Int) atom0179Coded)))))) := by
  rw [block002_data_flat038_step, block002_data_flat018_original, block002_data_flat037_original]
def block002_data_flat039 : CoefficientMerge.Poly := [(nat_lit 471, Int.ofNat (nat_lit 4608))]
theorem block002_data_flat039_step : block002_data_flat039 = (CoefficientMerge.scale (4608 : Int) atom0180Coded) := by decide +kernel
theorem block002_data_flat039_original : block002_data_flat039 = (CoefficientMerge.scale (4608 : Int) atom0180Coded) := by
  rw [block002_data_flat039_step]
def block002_data_flat040 : CoefficientMerge.Poly := [(nat_lit 474, Int.ofNat (nat_lit 36672))]
theorem block002_data_flat040_step : block002_data_flat040 = (CoefficientMerge.scale (36672 : Int) atom0181Coded) := by decide +kernel
theorem block002_data_flat040_original : block002_data_flat040 = (CoefficientMerge.scale (36672 : Int) atom0181Coded) := by
  rw [block002_data_flat040_step]
def block002_data_flat041 : CoefficientMerge.Poly := [(nat_lit 471, Int.ofNat (nat_lit 4608)), (nat_lit 474, Int.ofNat (nat_lit 36672))]
theorem block002_data_flat041_step : block002_data_flat041 = (CoefficientMerge.fastMerge block002_data_flat039 block002_data_flat040) := by decide +kernel
theorem block002_data_flat041_original : block002_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4608 : Int) atom0180Coded) (CoefficientMerge.scale (36672 : Int) atom0181Coded)) := by
  rw [block002_data_flat041_step, block002_data_flat039_original, block002_data_flat040_original]
def block002_data_flat042 : CoefficientMerge.Poly := [(nat_lit 475, Int.ofNat (nat_lit 96))]
theorem block002_data_flat042_step : block002_data_flat042 = (CoefficientMerge.scale (96 : Int) atom0182Coded) := by decide +kernel
theorem block002_data_flat042_original : block002_data_flat042 = (CoefficientMerge.scale (96 : Int) atom0182Coded) := by
  rw [block002_data_flat042_step]
def block002_data_flat043 : CoefficientMerge.Poly := [(nat_lit 476, Int.ofNat (nat_lit 10656))]
theorem block002_data_flat043_step : block002_data_flat043 = (CoefficientMerge.scale (10656 : Int) atom0183Coded) := by decide +kernel
theorem block002_data_flat043_original : block002_data_flat043 = (CoefficientMerge.scale (10656 : Int) atom0183Coded) := by
  rw [block002_data_flat043_step]
def block002_data_flat044 : CoefficientMerge.Poly := [(nat_lit 477, Int.ofNat (nat_lit 1584))]
theorem block002_data_flat044_step : block002_data_flat044 = (CoefficientMerge.scale (1584 : Int) atom0184Coded) := by decide +kernel
theorem block002_data_flat044_original : block002_data_flat044 = (CoefficientMerge.scale (1584 : Int) atom0184Coded) := by
  rw [block002_data_flat044_step]
def block002_data_flat045 : CoefficientMerge.Poly := [(nat_lit 476, Int.ofNat (nat_lit 10656)), (nat_lit 477, Int.ofNat (nat_lit 1584))]
theorem block002_data_flat045_step : block002_data_flat045 = (CoefficientMerge.fastMerge block002_data_flat043 block002_data_flat044) := by decide +kernel
theorem block002_data_flat045_original : block002_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10656 : Int) atom0183Coded) (CoefficientMerge.scale (1584 : Int) atom0184Coded)) := by
  rw [block002_data_flat045_step, block002_data_flat043_original, block002_data_flat044_original]
def block002_data_flat046 : CoefficientMerge.Poly := [(nat_lit 475, Int.ofNat (nat_lit 96)), (nat_lit 476, Int.ofNat (nat_lit 10656)), (nat_lit 477, Int.ofNat (nat_lit 1584))]
theorem block002_data_flat046_step : block002_data_flat046 = (CoefficientMerge.fastMerge block002_data_flat042 block002_data_flat045) := by decide +kernel
theorem block002_data_flat046_original : block002_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (96 : Int) atom0182Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10656 : Int) atom0183Coded) (CoefficientMerge.scale (1584 : Int) atom0184Coded))) := by
  rw [block002_data_flat046_step, block002_data_flat042_original, block002_data_flat045_original]
def block002_data_flat047 : CoefficientMerge.Poly := [(nat_lit 471, Int.ofNat (nat_lit 4608)), (nat_lit 474, Int.ofNat (nat_lit 36672)), (nat_lit 475, Int.ofNat (nat_lit 96)), (nat_lit 476, Int.ofNat (nat_lit 10656)), (nat_lit 477, Int.ofNat (nat_lit 1584))]
theorem block002_data_flat047_step : block002_data_flat047 = (CoefficientMerge.fastMerge block002_data_flat041 block002_data_flat046) := by decide +kernel
theorem block002_data_flat047_original : block002_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4608 : Int) atom0180Coded) (CoefficientMerge.scale (36672 : Int) atom0181Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96 : Int) atom0182Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10656 : Int) atom0183Coded) (CoefficientMerge.scale (1584 : Int) atom0184Coded)))) := by
  rw [block002_data_flat047_step, block002_data_flat041_original, block002_data_flat046_original]
def block002_data_flat048 : CoefficientMerge.Poly := [(nat_lit 479, Int.ofNat (nat_lit 1680))]
theorem block002_data_flat048_step : block002_data_flat048 = (CoefficientMerge.scale (1680 : Int) atom0185Coded) := by decide +kernel
theorem block002_data_flat048_original : block002_data_flat048 = (CoefficientMerge.scale (1680 : Int) atom0185Coded) := by
  rw [block002_data_flat048_step]
def block002_data_flat049 : CoefficientMerge.Poly := [(nat_lit 485, Int.ofNat (nat_lit 2112))]
theorem block002_data_flat049_step : block002_data_flat049 = (CoefficientMerge.scale (2112 : Int) atom0186Coded) := by decide +kernel
theorem block002_data_flat049_original : block002_data_flat049 = (CoefficientMerge.scale (2112 : Int) atom0186Coded) := by
  rw [block002_data_flat049_step]
def block002_data_flat050 : CoefficientMerge.Poly := [(nat_lit 479, Int.ofNat (nat_lit 1680)), (nat_lit 485, Int.ofNat (nat_lit 2112))]
theorem block002_data_flat050_step : block002_data_flat050 = (CoefficientMerge.fastMerge block002_data_flat048 block002_data_flat049) := by decide +kernel
theorem block002_data_flat050_original : block002_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1680 : Int) atom0185Coded) (CoefficientMerge.scale (2112 : Int) atom0186Coded)) := by
  rw [block002_data_flat050_step, block002_data_flat048_original, block002_data_flat049_original]
def block002_data_flat051 : CoefficientMerge.Poly := [(nat_lit 486, Int.ofNat (nat_lit 69696))]
theorem block002_data_flat051_step : block002_data_flat051 = (CoefficientMerge.scale (69696 : Int) atom0187Coded) := by decide +kernel
theorem block002_data_flat051_original : block002_data_flat051 = (CoefficientMerge.scale (69696 : Int) atom0187Coded) := by
  rw [block002_data_flat051_step]
def block002_data_flat052 : CoefficientMerge.Poly := [(nat_lit 487, Int.ofNat (nat_lit 20352))]
theorem block002_data_flat052_step : block002_data_flat052 = (CoefficientMerge.scale (20352 : Int) atom0188Coded) := by decide +kernel
theorem block002_data_flat052_original : block002_data_flat052 = (CoefficientMerge.scale (20352 : Int) atom0188Coded) := by
  rw [block002_data_flat052_step]
def block002_data_flat053 : CoefficientMerge.Poly := [(nat_lit 488, Int.ofNat (nat_lit 53184))]
theorem block002_data_flat053_step : block002_data_flat053 = (CoefficientMerge.scale (53184 : Int) atom0189Coded) := by decide +kernel
theorem block002_data_flat053_original : block002_data_flat053 = (CoefficientMerge.scale (53184 : Int) atom0189Coded) := by
  rw [block002_data_flat053_step]
def block002_data_flat054 : CoefficientMerge.Poly := [(nat_lit 487, Int.ofNat (nat_lit 20352)), (nat_lit 488, Int.ofNat (nat_lit 53184))]
theorem block002_data_flat054_step : block002_data_flat054 = (CoefficientMerge.fastMerge block002_data_flat052 block002_data_flat053) := by decide +kernel
theorem block002_data_flat054_original : block002_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20352 : Int) atom0188Coded) (CoefficientMerge.scale (53184 : Int) atom0189Coded)) := by
  rw [block002_data_flat054_step, block002_data_flat052_original, block002_data_flat053_original]
def block002_data_flat055 : CoefficientMerge.Poly := [(nat_lit 486, Int.ofNat (nat_lit 69696)), (nat_lit 487, Int.ofNat (nat_lit 20352)), (nat_lit 488, Int.ofNat (nat_lit 53184))]
theorem block002_data_flat055_step : block002_data_flat055 = (CoefficientMerge.fastMerge block002_data_flat051 block002_data_flat054) := by decide +kernel
theorem block002_data_flat055_original : block002_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (69696 : Int) atom0187Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20352 : Int) atom0188Coded) (CoefficientMerge.scale (53184 : Int) atom0189Coded))) := by
  rw [block002_data_flat055_step, block002_data_flat051_original, block002_data_flat054_original]
def block002_data_flat056 : CoefficientMerge.Poly := [(nat_lit 479, Int.ofNat (nat_lit 1680)), (nat_lit 485, Int.ofNat (nat_lit 2112)), (nat_lit 486, Int.ofNat (nat_lit 69696)), (nat_lit 487, Int.ofNat (nat_lit 20352)), (nat_lit 488, Int.ofNat (nat_lit 53184))]
theorem block002_data_flat056_step : block002_data_flat056 = (CoefficientMerge.fastMerge block002_data_flat050 block002_data_flat055) := by decide +kernel
theorem block002_data_flat056_original : block002_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1680 : Int) atom0185Coded) (CoefficientMerge.scale (2112 : Int) atom0186Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69696 : Int) atom0187Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20352 : Int) atom0188Coded) (CoefficientMerge.scale (53184 : Int) atom0189Coded)))) := by
  rw [block002_data_flat056_step, block002_data_flat050_original, block002_data_flat055_original]
def block002_data_flat057 : CoefficientMerge.Poly := [(nat_lit 471, Int.ofNat (nat_lit 4608)), (nat_lit 474, Int.ofNat (nat_lit 36672)), (nat_lit 475, Int.ofNat (nat_lit 96)), (nat_lit 476, Int.ofNat (nat_lit 10656)), (nat_lit 477, Int.ofNat (nat_lit 1584)), (nat_lit 479, Int.ofNat (nat_lit 1680)), (nat_lit 485, Int.ofNat (nat_lit 2112)), (nat_lit 486, Int.ofNat (nat_lit 69696)), (nat_lit 487, Int.ofNat (nat_lit 20352)), (nat_lit 488, Int.ofNat (nat_lit 53184))]
theorem block002_data_flat057_step : block002_data_flat057 = (CoefficientMerge.fastMerge block002_data_flat047 block002_data_flat056) := by decide +kernel
theorem block002_data_flat057_original : block002_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4608 : Int) atom0180Coded) (CoefficientMerge.scale (36672 : Int) atom0181Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96 : Int) atom0182Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10656 : Int) atom0183Coded) (CoefficientMerge.scale (1584 : Int) atom0184Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1680 : Int) atom0185Coded) (CoefficientMerge.scale (2112 : Int) atom0186Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69696 : Int) atom0187Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20352 : Int) atom0188Coded) (CoefficientMerge.scale (53184 : Int) atom0189Coded))))) := by
  rw [block002_data_flat057_step, block002_data_flat047_original, block002_data_flat056_original]
def block002_data_flat058 : CoefficientMerge.Poly := [(nat_lit 489, Int.ofNat (nat_lit 48288))]
theorem block002_data_flat058_step : block002_data_flat058 = (CoefficientMerge.scale (48288 : Int) atom0190Coded) := by decide +kernel
theorem block002_data_flat058_original : block002_data_flat058 = (CoefficientMerge.scale (48288 : Int) atom0190Coded) := by
  rw [block002_data_flat058_step]
def block002_data_flat059 : CoefficientMerge.Poly := [(nat_lit 490, Int.ofNat (nat_lit 60528))]
theorem block002_data_flat059_step : block002_data_flat059 = (CoefficientMerge.scale (60528 : Int) atom0191Coded) := by decide +kernel
theorem block002_data_flat059_original : block002_data_flat059 = (CoefficientMerge.scale (60528 : Int) atom0191Coded) := by
  rw [block002_data_flat059_step]
def block002_data_flat060 : CoefficientMerge.Poly := [(nat_lit 489, Int.ofNat (nat_lit 48288)), (nat_lit 490, Int.ofNat (nat_lit 60528))]
theorem block002_data_flat060_step : block002_data_flat060 = (CoefficientMerge.fastMerge block002_data_flat058 block002_data_flat059) := by decide +kernel
theorem block002_data_flat060_original : block002_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48288 : Int) atom0190Coded) (CoefficientMerge.scale (60528 : Int) atom0191Coded)) := by
  rw [block002_data_flat060_step, block002_data_flat058_original, block002_data_flat059_original]
def block002_data_flat061 : CoefficientMerge.Poly := [(nat_lit 491, Int.ofNat (nat_lit 86640))]
theorem block002_data_flat061_step : block002_data_flat061 = (CoefficientMerge.scale (86640 : Int) atom0192Coded) := by decide +kernel
theorem block002_data_flat061_original : block002_data_flat061 = (CoefficientMerge.scale (86640 : Int) atom0192Coded) := by
  rw [block002_data_flat061_step]
def block002_data_flat062 : CoefficientMerge.Poly := [(nat_lit 497, Int.ofNat (nat_lit 10368))]
theorem block002_data_flat062_step : block002_data_flat062 = (CoefficientMerge.scale (10368 : Int) atom0193Coded) := by decide +kernel
theorem block002_data_flat062_original : block002_data_flat062 = (CoefficientMerge.scale (10368 : Int) atom0193Coded) := by
  rw [block002_data_flat062_step]
def block002_data_flat063 : CoefficientMerge.Poly := [(nat_lit 498, Int.ofNat (nat_lit 72960))]
theorem block002_data_flat063_step : block002_data_flat063 = (CoefficientMerge.scale (72960 : Int) atom0194Coded) := by decide +kernel
theorem block002_data_flat063_original : block002_data_flat063 = (CoefficientMerge.scale (72960 : Int) atom0194Coded) := by
  rw [block002_data_flat063_step]
def block002_data_flat064 : CoefficientMerge.Poly := [(nat_lit 497, Int.ofNat (nat_lit 10368)), (nat_lit 498, Int.ofNat (nat_lit 72960))]
theorem block002_data_flat064_step : block002_data_flat064 = (CoefficientMerge.fastMerge block002_data_flat062 block002_data_flat063) := by decide +kernel
theorem block002_data_flat064_original : block002_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10368 : Int) atom0193Coded) (CoefficientMerge.scale (72960 : Int) atom0194Coded)) := by
  rw [block002_data_flat064_step, block002_data_flat062_original, block002_data_flat063_original]
def block002_data_flat065 : CoefficientMerge.Poly := [(nat_lit 491, Int.ofNat (nat_lit 86640)), (nat_lit 497, Int.ofNat (nat_lit 10368)), (nat_lit 498, Int.ofNat (nat_lit 72960))]
theorem block002_data_flat065_step : block002_data_flat065 = (CoefficientMerge.fastMerge block002_data_flat061 block002_data_flat064) := by decide +kernel
theorem block002_data_flat065_original : block002_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (86640 : Int) atom0192Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10368 : Int) atom0193Coded) (CoefficientMerge.scale (72960 : Int) atom0194Coded))) := by
  rw [block002_data_flat065_step, block002_data_flat061_original, block002_data_flat064_original]
def block002_data_flat066 : CoefficientMerge.Poly := [(nat_lit 489, Int.ofNat (nat_lit 48288)), (nat_lit 490, Int.ofNat (nat_lit 60528)), (nat_lit 491, Int.ofNat (nat_lit 86640)), (nat_lit 497, Int.ofNat (nat_lit 10368)), (nat_lit 498, Int.ofNat (nat_lit 72960))]
theorem block002_data_flat066_step : block002_data_flat066 = (CoefficientMerge.fastMerge block002_data_flat060 block002_data_flat065) := by decide +kernel
theorem block002_data_flat066_original : block002_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48288 : Int) atom0190Coded) (CoefficientMerge.scale (60528 : Int) atom0191Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86640 : Int) atom0192Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10368 : Int) atom0193Coded) (CoefficientMerge.scale (72960 : Int) atom0194Coded)))) := by
  rw [block002_data_flat066_step, block002_data_flat060_original, block002_data_flat065_original]
def block002_data_flat067 : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 46848))]
theorem block002_data_flat067_step : block002_data_flat067 = (CoefficientMerge.scale (46848 : Int) atom0195Coded) := by decide +kernel
theorem block002_data_flat067_original : block002_data_flat067 = (CoefficientMerge.scale (46848 : Int) atom0195Coded) := by
  rw [block002_data_flat067_step]
def block002_data_flat068 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 83712))]
theorem block002_data_flat068_step : block002_data_flat068 = (CoefficientMerge.scale (83712 : Int) atom0196Coded) := by decide +kernel
theorem block002_data_flat068_original : block002_data_flat068 = (CoefficientMerge.scale (83712 : Int) atom0196Coded) := by
  rw [block002_data_flat068_step]
def block002_data_flat069 : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 46848)), (nat_lit 500, Int.ofNat (nat_lit 83712))]
theorem block002_data_flat069_step : block002_data_flat069 = (CoefficientMerge.fastMerge block002_data_flat067 block002_data_flat068) := by decide +kernel
theorem block002_data_flat069_original : block002_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46848 : Int) atom0195Coded) (CoefficientMerge.scale (83712 : Int) atom0196Coded)) := by
  rw [block002_data_flat069_step, block002_data_flat067_original, block002_data_flat068_original]
def block002_data_flat070 : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 91392))]
theorem block002_data_flat070_step : block002_data_flat070 = (CoefficientMerge.scale (91392 : Int) atom0197Coded) := by decide +kernel
theorem block002_data_flat070_original : block002_data_flat070 = (CoefficientMerge.scale (91392 : Int) atom0197Coded) := by
  rw [block002_data_flat070_step]
def block002_data_flat071 : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 102000))]
theorem block002_data_flat071_step : block002_data_flat071 = (CoefficientMerge.scale (102000 : Int) atom0198Coded) := by decide +kernel
theorem block002_data_flat071_original : block002_data_flat071 = (CoefficientMerge.scale (102000 : Int) atom0198Coded) := by
  rw [block002_data_flat071_step]
def block002_data_flat072 : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 154368))]
theorem block002_data_flat072_step : block002_data_flat072 = (CoefficientMerge.scale (154368 : Int) atom0199Coded) := by decide +kernel
theorem block002_data_flat072_original : block002_data_flat072 = (CoefficientMerge.scale (154368 : Int) atom0199Coded) := by
  rw [block002_data_flat072_step]
def block002_data_flat073 : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 102000)), (nat_lit 503, Int.ofNat (nat_lit 154368))]
theorem block002_data_flat073_step : block002_data_flat073 = (CoefficientMerge.fastMerge block002_data_flat071 block002_data_flat072) := by decide +kernel
theorem block002_data_flat073_original : block002_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (102000 : Int) atom0198Coded) (CoefficientMerge.scale (154368 : Int) atom0199Coded)) := by
  rw [block002_data_flat073_step, block002_data_flat071_original, block002_data_flat072_original]
def block002_data_flat074 : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 91392)), (nat_lit 502, Int.ofNat (nat_lit 102000)), (nat_lit 503, Int.ofNat (nat_lit 154368))]
theorem block002_data_flat074_step : block002_data_flat074 = (CoefficientMerge.fastMerge block002_data_flat070 block002_data_flat073) := by decide +kernel
theorem block002_data_flat074_original : block002_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (91392 : Int) atom0197Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102000 : Int) atom0198Coded) (CoefficientMerge.scale (154368 : Int) atom0199Coded))) := by
  rw [block002_data_flat074_step, block002_data_flat070_original, block002_data_flat073_original]
def block002_data_flat075 : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 46848)), (nat_lit 500, Int.ofNat (nat_lit 83712)), (nat_lit 501, Int.ofNat (nat_lit 91392)), (nat_lit 502, Int.ofNat (nat_lit 102000)), (nat_lit 503, Int.ofNat (nat_lit 154368))]
theorem block002_data_flat075_step : block002_data_flat075 = (CoefficientMerge.fastMerge block002_data_flat069 block002_data_flat074) := by decide +kernel
theorem block002_data_flat075_original : block002_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46848 : Int) atom0195Coded) (CoefficientMerge.scale (83712 : Int) atom0196Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91392 : Int) atom0197Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102000 : Int) atom0198Coded) (CoefficientMerge.scale (154368 : Int) atom0199Coded)))) := by
  rw [block002_data_flat075_step, block002_data_flat069_original, block002_data_flat074_original]
def block002_data_flat076 : CoefficientMerge.Poly := [(nat_lit 489, Int.ofNat (nat_lit 48288)), (nat_lit 490, Int.ofNat (nat_lit 60528)), (nat_lit 491, Int.ofNat (nat_lit 86640)), (nat_lit 497, Int.ofNat (nat_lit 10368)), (nat_lit 498, Int.ofNat (nat_lit 72960)), (nat_lit 499, Int.ofNat (nat_lit 46848)), (nat_lit 500, Int.ofNat (nat_lit 83712)), (nat_lit 501, Int.ofNat (nat_lit 91392)), (nat_lit 502, Int.ofNat (nat_lit 102000)), (nat_lit 503, Int.ofNat (nat_lit 154368))]
theorem block002_data_flat076_step : block002_data_flat076 = (CoefficientMerge.fastMerge block002_data_flat066 block002_data_flat075) := by decide +kernel
theorem block002_data_flat076_original : block002_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48288 : Int) atom0190Coded) (CoefficientMerge.scale (60528 : Int) atom0191Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86640 : Int) atom0192Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10368 : Int) atom0193Coded) (CoefficientMerge.scale (72960 : Int) atom0194Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46848 : Int) atom0195Coded) (CoefficientMerge.scale (83712 : Int) atom0196Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91392 : Int) atom0197Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102000 : Int) atom0198Coded) (CoefficientMerge.scale (154368 : Int) atom0199Coded))))) := by
  rw [block002_data_flat076_step, block002_data_flat066_original, block002_data_flat075_original]
def block002_data_flat077 : CoefficientMerge.Poly := [(nat_lit 471, Int.ofNat (nat_lit 4608)), (nat_lit 474, Int.ofNat (nat_lit 36672)), (nat_lit 475, Int.ofNat (nat_lit 96)), (nat_lit 476, Int.ofNat (nat_lit 10656)), (nat_lit 477, Int.ofNat (nat_lit 1584)), (nat_lit 479, Int.ofNat (nat_lit 1680)), (nat_lit 485, Int.ofNat (nat_lit 2112)), (nat_lit 486, Int.ofNat (nat_lit 69696)), (nat_lit 487, Int.ofNat (nat_lit 20352)), (nat_lit 488, Int.ofNat (nat_lit 53184)), (nat_lit 489, Int.ofNat (nat_lit 48288)), (nat_lit 490, Int.ofNat (nat_lit 60528)), (nat_lit 491, Int.ofNat (nat_lit 86640)), (nat_lit 497, Int.ofNat (nat_lit 10368)), (nat_lit 498, Int.ofNat (nat_lit 72960)), (nat_lit 499, Int.ofNat (nat_lit 46848)), (nat_lit 500, Int.ofNat (nat_lit 83712)), (nat_lit 501, Int.ofNat (nat_lit 91392)), (nat_lit 502, Int.ofNat (nat_lit 102000)), (nat_lit 503, Int.ofNat (nat_lit 154368))]
theorem block002_data_flat077_step : block002_data_flat077 = (CoefficientMerge.fastMerge block002_data_flat057 block002_data_flat076) := by decide +kernel
theorem block002_data_flat077_original : block002_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4608 : Int) atom0180Coded) (CoefficientMerge.scale (36672 : Int) atom0181Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96 : Int) atom0182Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10656 : Int) atom0183Coded) (CoefficientMerge.scale (1584 : Int) atom0184Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1680 : Int) atom0185Coded) (CoefficientMerge.scale (2112 : Int) atom0186Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69696 : Int) atom0187Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20352 : Int) atom0188Coded) (CoefficientMerge.scale (53184 : Int) atom0189Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48288 : Int) atom0190Coded) (CoefficientMerge.scale (60528 : Int) atom0191Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86640 : Int) atom0192Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10368 : Int) atom0193Coded) (CoefficientMerge.scale (72960 : Int) atom0194Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46848 : Int) atom0195Coded) (CoefficientMerge.scale (83712 : Int) atom0196Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91392 : Int) atom0197Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102000 : Int) atom0198Coded) (CoefficientMerge.scale (154368 : Int) atom0199Coded)))))) := by
  rw [block002_data_flat077_step, block002_data_flat057_original, block002_data_flat076_original]
def block002_data_flat078 : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 167040)), (nat_lit 368, Int.ofNat (nat_lit 223104)), (nat_lit 369, Int.ofNat (nat_lit 231552)), (nat_lit 370, Int.ofNat (nat_lit 122400)), (nat_lit 371, Int.ofNat (nat_lit 225744)), (nat_lit 379, Int.ofNat (nat_lit 79488)), (nat_lit 380, Int.ofNat (nat_lit 181440)), (nat_lit 381, Int.ofNat (nat_lit 223488)), (nat_lit 382, Int.ofNat (nat_lit 150336)), (nat_lit 383, Int.ofNat (nat_lit 195312)), (nat_lit 392, Int.ofNat (nat_lit 119808)), (nat_lit 393, Int.ofNat (nat_lit 214272)), (nat_lit 394, Int.ofNat (nat_lit 152160)), (nat_lit 395, Int.ofNat (nat_lit 213168)), (nat_lit 405, Int.ofNat (nat_lit 84672)), (nat_lit 406, Int.ofNat (nat_lit 135504)), (nat_lit 407, Int.ofNat (nat_lit 208848)), (nat_lit 418, Int.ofNat (nat_lit 35712)), (nat_lit 419, Int.ofNat (nat_lit 152808)), (nat_lit 431, Int.ofNat (nat_lit 106704)), (nat_lit 471, Int.ofNat (nat_lit 4608)), (nat_lit 474, Int.ofNat (nat_lit 36672)), (nat_lit 475, Int.ofNat (nat_lit 96)), (nat_lit 476, Int.ofNat (nat_lit 10656)), (nat_lit 477, Int.ofNat (nat_lit 1584)), (nat_lit 479, Int.ofNat (nat_lit 1680)), (nat_lit 485, Int.ofNat (nat_lit 2112)), (nat_lit 486, Int.ofNat (nat_lit 69696)), (nat_lit 487, Int.ofNat (nat_lit 20352)), (nat_lit 488, Int.ofNat (nat_lit 53184)), (nat_lit 489, Int.ofNat (nat_lit 48288)), (nat_lit 490, Int.ofNat (nat_lit 60528)), (nat_lit 491, Int.ofNat (nat_lit 86640)), (nat_lit 497, Int.ofNat (nat_lit 10368)), (nat_lit 498, Int.ofNat (nat_lit 72960)), (nat_lit 499, Int.ofNat (nat_lit 46848)), (nat_lit 500, Int.ofNat (nat_lit 83712)), (nat_lit 501, Int.ofNat (nat_lit 91392)), (nat_lit 502, Int.ofNat (nat_lit 102000)), (nat_lit 503, Int.ofNat (nat_lit 154368))]
theorem block002_data_flat078_step : block002_data_flat078 = (CoefficientMerge.fastMerge block002_data_flat038 block002_data_flat077) := by decide +kernel
theorem block002_data_flat078_original : block002_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167040 : Int) atom0160Coded) (CoefficientMerge.scale (223104 : Int) atom0161Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231552 : Int) atom0162Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122400 : Int) atom0163Coded) (CoefficientMerge.scale (225744 : Int) atom0164Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79488 : Int) atom0165Coded) (CoefficientMerge.scale (181440 : Int) atom0166Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223488 : Int) atom0167Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150336 : Int) atom0168Coded) (CoefficientMerge.scale (195312 : Int) atom0169Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (119808 : Int) atom0170Coded) (CoefficientMerge.scale (214272 : Int) atom0171Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152160 : Int) atom0172Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213168 : Int) atom0173Coded) (CoefficientMerge.scale (84672 : Int) atom0174Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (135504 : Int) atom0175Coded) (CoefficientMerge.scale (208848 : Int) atom0176Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35712 : Int) atom0177Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808 : Int) atom0178Coded) (CoefficientMerge.scale (106704 : Int) atom0179Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4608 : Int) atom0180Coded) (CoefficientMerge.scale (36672 : Int) atom0181Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96 : Int) atom0182Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10656 : Int) atom0183Coded) (CoefficientMerge.scale (1584 : Int) atom0184Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1680 : Int) atom0185Coded) (CoefficientMerge.scale (2112 : Int) atom0186Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69696 : Int) atom0187Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20352 : Int) atom0188Coded) (CoefficientMerge.scale (53184 : Int) atom0189Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48288 : Int) atom0190Coded) (CoefficientMerge.scale (60528 : Int) atom0191Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86640 : Int) atom0192Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10368 : Int) atom0193Coded) (CoefficientMerge.scale (72960 : Int) atom0194Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46848 : Int) atom0195Coded) (CoefficientMerge.scale (83712 : Int) atom0196Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91392 : Int) atom0197Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102000 : Int) atom0198Coded) (CoefficientMerge.scale (154368 : Int) atom0199Coded))))))) := by
  rw [block002_data_flat078_step, block002_data_flat038_original, block002_data_flat077_original]
def block002_data_flat079 : CoefficientMerge.Poly := [(nat_lit 510, Int.ofNat (nat_lit 77184))]
theorem block002_data_flat079_step : block002_data_flat079 = (CoefficientMerge.scale (77184 : Int) atom0200Coded) := by decide +kernel
theorem block002_data_flat079_original : block002_data_flat079 = (CoefficientMerge.scale (77184 : Int) atom0200Coded) := by
  rw [block002_data_flat079_step]
def block002_data_flat080 : CoefficientMerge.Poly := [(nat_lit 511, Int.ofNat (nat_lit 121344))]
theorem block002_data_flat080_step : block002_data_flat080 = (CoefficientMerge.scale (121344 : Int) atom0201Coded) := by decide +kernel
theorem block002_data_flat080_original : block002_data_flat080 = (CoefficientMerge.scale (121344 : Int) atom0201Coded) := by
  rw [block002_data_flat080_step]
def block002_data_flat081 : CoefficientMerge.Poly := [(nat_lit 510, Int.ofNat (nat_lit 77184)), (nat_lit 511, Int.ofNat (nat_lit 121344))]
theorem block002_data_flat081_step : block002_data_flat081 = (CoefficientMerge.fastMerge block002_data_flat079 block002_data_flat080) := by decide +kernel
theorem block002_data_flat081_original : block002_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (77184 : Int) atom0200Coded) (CoefficientMerge.scale (121344 : Int) atom0201Coded)) := by
  rw [block002_data_flat081_step, block002_data_flat079_original, block002_data_flat080_original]
def block002_data_flat082 : CoefficientMerge.Poly := [(nat_lit 512, Int.ofNat (nat_lit 188160))]
theorem block002_data_flat082_step : block002_data_flat082 = (CoefficientMerge.scale (188160 : Int) atom0202Coded) := by decide +kernel
theorem block002_data_flat082_original : block002_data_flat082 = (CoefficientMerge.scale (188160 : Int) atom0202Coded) := by
  rw [block002_data_flat082_step]
def block002_data_flat083 : CoefficientMerge.Poly := [(nat_lit 513, Int.ofNat (nat_lit 207360))]
theorem block002_data_flat083_step : block002_data_flat083 = (CoefficientMerge.scale (207360 : Int) atom0203Coded) := by decide +kernel
theorem block002_data_flat083_original : block002_data_flat083 = (CoefficientMerge.scale (207360 : Int) atom0203Coded) := by
  rw [block002_data_flat083_step]
def block002_data_flat084 : CoefficientMerge.Poly := [(nat_lit 514, Int.ofNat (nat_lit 115800))]
theorem block002_data_flat084_step : block002_data_flat084 = (CoefficientMerge.scale (115800 : Int) atom0204Coded) := by decide +kernel
theorem block002_data_flat084_original : block002_data_flat084 = (CoefficientMerge.scale (115800 : Int) atom0204Coded) := by
  rw [block002_data_flat084_step]
def block002_data_flat085 : CoefficientMerge.Poly := [(nat_lit 513, Int.ofNat (nat_lit 207360)), (nat_lit 514, Int.ofNat (nat_lit 115800))]
theorem block002_data_flat085_step : block002_data_flat085 = (CoefficientMerge.fastMerge block002_data_flat083 block002_data_flat084) := by decide +kernel
theorem block002_data_flat085_original : block002_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (207360 : Int) atom0203Coded) (CoefficientMerge.scale (115800 : Int) atom0204Coded)) := by
  rw [block002_data_flat085_step, block002_data_flat083_original, block002_data_flat084_original]
def block002_data_flat086 : CoefficientMerge.Poly := [(nat_lit 512, Int.ofNat (nat_lit 188160)), (nat_lit 513, Int.ofNat (nat_lit 207360)), (nat_lit 514, Int.ofNat (nat_lit 115800))]
theorem block002_data_flat086_step : block002_data_flat086 = (CoefficientMerge.fastMerge block002_data_flat082 block002_data_flat085) := by decide +kernel
theorem block002_data_flat086_original : block002_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (188160 : Int) atom0202Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207360 : Int) atom0203Coded) (CoefficientMerge.scale (115800 : Int) atom0204Coded))) := by
  rw [block002_data_flat086_step, block002_data_flat082_original, block002_data_flat085_original]
def block002_data_flat087 : CoefficientMerge.Poly := [(nat_lit 510, Int.ofNat (nat_lit 77184)), (nat_lit 511, Int.ofNat (nat_lit 121344)), (nat_lit 512, Int.ofNat (nat_lit 188160)), (nat_lit 513, Int.ofNat (nat_lit 207360)), (nat_lit 514, Int.ofNat (nat_lit 115800))]
theorem block002_data_flat087_step : block002_data_flat087 = (CoefficientMerge.fastMerge block002_data_flat081 block002_data_flat086) := by decide +kernel
theorem block002_data_flat087_original : block002_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77184 : Int) atom0200Coded) (CoefficientMerge.scale (121344 : Int) atom0201Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (188160 : Int) atom0202Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207360 : Int) atom0203Coded) (CoefficientMerge.scale (115800 : Int) atom0204Coded)))) := by
  rw [block002_data_flat087_step, block002_data_flat081_original, block002_data_flat086_original]
def block002_data_flat088 : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 217344))]
theorem block002_data_flat088_step : block002_data_flat088 = (CoefficientMerge.scale (217344 : Int) atom0205Coded) := by decide +kernel
theorem block002_data_flat088_original : block002_data_flat088 = (CoefficientMerge.scale (217344 : Int) atom0205Coded) := by
  rw [block002_data_flat088_step]
def block002_data_flat089 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 58752))]
theorem block002_data_flat089_step : block002_data_flat089 = (CoefficientMerge.scale (58752 : Int) atom0206Coded) := by decide +kernel
theorem block002_data_flat089_original : block002_data_flat089 = (CoefficientMerge.scale (58752 : Int) atom0206Coded) := by
  rw [block002_data_flat089_step]
def block002_data_flat090 : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 217344)), (nat_lit 523, Int.ofNat (nat_lit 58752))]
theorem block002_data_flat090_step : block002_data_flat090 = (CoefficientMerge.fastMerge block002_data_flat088 block002_data_flat089) := by decide +kernel
theorem block002_data_flat090_original : block002_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (217344 : Int) atom0205Coded) (CoefficientMerge.scale (58752 : Int) atom0206Coded)) := by
  rw [block002_data_flat090_step, block002_data_flat088_original, block002_data_flat089_original]
def block002_data_flat091 : CoefficientMerge.Poly := [(nat_lit 524, Int.ofNat (nat_lit 153600))]
theorem block002_data_flat091_step : block002_data_flat091 = (CoefficientMerge.scale (153600 : Int) atom0207Coded) := by decide +kernel
theorem block002_data_flat091_original : block002_data_flat091 = (CoefficientMerge.scale (153600 : Int) atom0207Coded) := by
  rw [block002_data_flat091_step]
def block002_data_flat092 : CoefficientMerge.Poly := [(nat_lit 525, Int.ofNat (nat_lit 209280))]
theorem block002_data_flat092_step : block002_data_flat092 = (CoefficientMerge.scale (209280 : Int) atom0208Coded) := by decide +kernel
theorem block002_data_flat092_original : block002_data_flat092 = (CoefficientMerge.scale (209280 : Int) atom0208Coded) := by
  rw [block002_data_flat092_step]
def block002_data_flat093 : CoefficientMerge.Poly := [(nat_lit 526, Int.ofNat (nat_lit 149760))]
theorem block002_data_flat093_step : block002_data_flat093 = (CoefficientMerge.scale (149760 : Int) atom0209Coded) := by decide +kernel
theorem block002_data_flat093_original : block002_data_flat093 = (CoefficientMerge.scale (149760 : Int) atom0209Coded) := by
  rw [block002_data_flat093_step]
def block002_data_flat094 : CoefficientMerge.Poly := [(nat_lit 525, Int.ofNat (nat_lit 209280)), (nat_lit 526, Int.ofNat (nat_lit 149760))]
theorem block002_data_flat094_step : block002_data_flat094 = (CoefficientMerge.fastMerge block002_data_flat092 block002_data_flat093) := by decide +kernel
theorem block002_data_flat094_original : block002_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (209280 : Int) atom0208Coded) (CoefficientMerge.scale (149760 : Int) atom0209Coded)) := by
  rw [block002_data_flat094_step, block002_data_flat092_original, block002_data_flat093_original]
def block002_data_flat095 : CoefficientMerge.Poly := [(nat_lit 524, Int.ofNat (nat_lit 153600)), (nat_lit 525, Int.ofNat (nat_lit 209280)), (nat_lit 526, Int.ofNat (nat_lit 149760))]
theorem block002_data_flat095_step : block002_data_flat095 = (CoefficientMerge.fastMerge block002_data_flat091 block002_data_flat094) := by decide +kernel
theorem block002_data_flat095_original : block002_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (153600 : Int) atom0207Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209280 : Int) atom0208Coded) (CoefficientMerge.scale (149760 : Int) atom0209Coded))) := by
  rw [block002_data_flat095_step, block002_data_flat091_original, block002_data_flat094_original]
def block002_data_flat096 : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 217344)), (nat_lit 523, Int.ofNat (nat_lit 58752)), (nat_lit 524, Int.ofNat (nat_lit 153600)), (nat_lit 525, Int.ofNat (nat_lit 209280)), (nat_lit 526, Int.ofNat (nat_lit 149760))]
theorem block002_data_flat096_step : block002_data_flat096 = (CoefficientMerge.fastMerge block002_data_flat090 block002_data_flat095) := by decide +kernel
theorem block002_data_flat096_original : block002_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (217344 : Int) atom0205Coded) (CoefficientMerge.scale (58752 : Int) atom0206Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153600 : Int) atom0207Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209280 : Int) atom0208Coded) (CoefficientMerge.scale (149760 : Int) atom0209Coded)))) := by
  rw [block002_data_flat096_step, block002_data_flat090_original, block002_data_flat095_original]
def block002_data_flat097 : CoefficientMerge.Poly := [(nat_lit 510, Int.ofNat (nat_lit 77184)), (nat_lit 511, Int.ofNat (nat_lit 121344)), (nat_lit 512, Int.ofNat (nat_lit 188160)), (nat_lit 513, Int.ofNat (nat_lit 207360)), (nat_lit 514, Int.ofNat (nat_lit 115800)), (nat_lit 515, Int.ofNat (nat_lit 217344)), (nat_lit 523, Int.ofNat (nat_lit 58752)), (nat_lit 524, Int.ofNat (nat_lit 153600)), (nat_lit 525, Int.ofNat (nat_lit 209280)), (nat_lit 526, Int.ofNat (nat_lit 149760))]
theorem block002_data_flat097_step : block002_data_flat097 = (CoefficientMerge.fastMerge block002_data_flat087 block002_data_flat096) := by decide +kernel
theorem block002_data_flat097_original : block002_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77184 : Int) atom0200Coded) (CoefficientMerge.scale (121344 : Int) atom0201Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (188160 : Int) atom0202Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207360 : Int) atom0203Coded) (CoefficientMerge.scale (115800 : Int) atom0204Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (217344 : Int) atom0205Coded) (CoefficientMerge.scale (58752 : Int) atom0206Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153600 : Int) atom0207Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209280 : Int) atom0208Coded) (CoefficientMerge.scale (149760 : Int) atom0209Coded))))) := by
  rw [block002_data_flat097_step, block002_data_flat087_original, block002_data_flat096_original]
def block002_data_flat098 : CoefficientMerge.Poly := [(nat_lit 527, Int.ofNat (nat_lit 204288))]
theorem block002_data_flat098_step : block002_data_flat098 = (CoefficientMerge.scale (204288 : Int) atom0210Coded) := by decide +kernel
theorem block002_data_flat098_original : block002_data_flat098 = (CoefficientMerge.scale (204288 : Int) atom0210Coded) := by
  rw [block002_data_flat098_step]
def block002_data_flat099 : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 109440))]
theorem block002_data_flat099_step : block002_data_flat099 = (CoefficientMerge.scale (109440 : Int) atom0211Coded) := by decide +kernel
theorem block002_data_flat099_original : block002_data_flat099 = (CoefficientMerge.scale (109440 : Int) atom0211Coded) := by
  rw [block002_data_flat099_step]
def block002_data_flat100 : CoefficientMerge.Poly := [(nat_lit 527, Int.ofNat (nat_lit 204288)), (nat_lit 536, Int.ofNat (nat_lit 109440))]
theorem block002_data_flat100_step : block002_data_flat100 = (CoefficientMerge.fastMerge block002_data_flat098 block002_data_flat099) := by decide +kernel
theorem block002_data_flat100_original : block002_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (204288 : Int) atom0210Coded) (CoefficientMerge.scale (109440 : Int) atom0211Coded)) := by
  rw [block002_data_flat100_step, block002_data_flat098_original, block002_data_flat099_original]
def block002_data_flat101 : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 210048))]
theorem block002_data_flat101_step : block002_data_flat101 = (CoefficientMerge.scale (210048 : Int) atom0212Coded) := by decide +kernel
theorem block002_data_flat101_original : block002_data_flat101 = (CoefficientMerge.scale (210048 : Int) atom0212Coded) := by
  rw [block002_data_flat101_step]
def block002_data_flat102 : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 157608))]
theorem block002_data_flat102_step : block002_data_flat102 = (CoefficientMerge.scale (157608 : Int) atom0213Coded) := by decide +kernel
theorem block002_data_flat102_original : block002_data_flat102 = (CoefficientMerge.scale (157608 : Int) atom0213Coded) := by
  rw [block002_data_flat102_step]
def block002_data_flat103 : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 241152))]
theorem block002_data_flat103_step : block002_data_flat103 = (CoefficientMerge.scale (241152 : Int) atom0214Coded) := by decide +kernel
theorem block002_data_flat103_original : block002_data_flat103 = (CoefficientMerge.scale (241152 : Int) atom0214Coded) := by
  rw [block002_data_flat103_step]
def block002_data_flat104 : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 157608)), (nat_lit 539, Int.ofNat (nat_lit 241152))]
theorem block002_data_flat104_step : block002_data_flat104 = (CoefficientMerge.fastMerge block002_data_flat102 block002_data_flat103) := by decide +kernel
theorem block002_data_flat104_original : block002_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608 : Int) atom0213Coded) (CoefficientMerge.scale (241152 : Int) atom0214Coded)) := by
  rw [block002_data_flat104_step, block002_data_flat102_original, block002_data_flat103_original]
def block002_data_flat105 : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 210048)), (nat_lit 538, Int.ofNat (nat_lit 157608)), (nat_lit 539, Int.ofNat (nat_lit 241152))]
theorem block002_data_flat105_step : block002_data_flat105 = (CoefficientMerge.fastMerge block002_data_flat101 block002_data_flat104) := by decide +kernel
theorem block002_data_flat105_original : block002_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (210048 : Int) atom0212Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608 : Int) atom0213Coded) (CoefficientMerge.scale (241152 : Int) atom0214Coded))) := by
  rw [block002_data_flat105_step, block002_data_flat101_original, block002_data_flat104_original]
def block002_data_flat106 : CoefficientMerge.Poly := [(nat_lit 527, Int.ofNat (nat_lit 204288)), (nat_lit 536, Int.ofNat (nat_lit 109440)), (nat_lit 537, Int.ofNat (nat_lit 210048)), (nat_lit 538, Int.ofNat (nat_lit 157608)), (nat_lit 539, Int.ofNat (nat_lit 241152))]
theorem block002_data_flat106_step : block002_data_flat106 = (CoefficientMerge.fastMerge block002_data_flat100 block002_data_flat105) := by decide +kernel
theorem block002_data_flat106_original : block002_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204288 : Int) atom0210Coded) (CoefficientMerge.scale (109440 : Int) atom0211Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210048 : Int) atom0212Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608 : Int) atom0213Coded) (CoefficientMerge.scale (241152 : Int) atom0214Coded)))) := by
  rw [block002_data_flat106_step, block002_data_flat100_original, block002_data_flat105_original]
def block002_data_flat107 : CoefficientMerge.Poly := [(nat_lit 549, Int.ofNat (nat_lit 87552))]
theorem block002_data_flat107_step : block002_data_flat107 = (CoefficientMerge.scale (87552 : Int) atom0215Coded) := by decide +kernel
theorem block002_data_flat107_original : block002_data_flat107 = (CoefficientMerge.scale (87552 : Int) atom0215Coded) := by
  rw [block002_data_flat107_step]
def block002_data_flat108 : CoefficientMerge.Poly := [(nat_lit 550, Int.ofNat (nat_lit 150396))]
theorem block002_data_flat108_step : block002_data_flat108 = (CoefficientMerge.scale (150396 : Int) atom0216Coded) := by decide +kernel
theorem block002_data_flat108_original : block002_data_flat108 = (CoefficientMerge.scale (150396 : Int) atom0216Coded) := by
  rw [block002_data_flat108_step]
def block002_data_flat109 : CoefficientMerge.Poly := [(nat_lit 549, Int.ofNat (nat_lit 87552)), (nat_lit 550, Int.ofNat (nat_lit 150396))]
theorem block002_data_flat109_step : block002_data_flat109 = (CoefficientMerge.fastMerge block002_data_flat107 block002_data_flat108) := by decide +kernel
theorem block002_data_flat109_original : block002_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (87552 : Int) atom0215Coded) (CoefficientMerge.scale (150396 : Int) atom0216Coded)) := by
  rw [block002_data_flat109_step, block002_data_flat107_original, block002_data_flat108_original]
def block002_data_flat110 : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 254208))]
theorem block002_data_flat110_step : block002_data_flat110 = (CoefficientMerge.scale (254208 : Int) atom0217Coded) := by decide +kernel
theorem block002_data_flat110_original : block002_data_flat110 = (CoefficientMerge.scale (254208 : Int) atom0217Coded) := by
  rw [block002_data_flat110_step]
def block002_data_flat111 : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 41040))]
theorem block002_data_flat111_step : block002_data_flat111 = (CoefficientMerge.scale (41040 : Int) atom0218Coded) := by decide +kernel
theorem block002_data_flat111_original : block002_data_flat111 = (CoefficientMerge.scale (41040 : Int) atom0218Coded) := by
  rw [block002_data_flat111_step]
def block002_data_flat112 : CoefficientMerge.Poly := [(nat_lit 563, Int.ofNat (nat_lit 201786))]
theorem block002_data_flat112_step : block002_data_flat112 = (CoefficientMerge.scale (201786 : Int) atom0219Coded) := by decide +kernel
theorem block002_data_flat112_original : block002_data_flat112 = (CoefficientMerge.scale (201786 : Int) atom0219Coded) := by
  rw [block002_data_flat112_step]
def block002_data_flat113 : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 41040)), (nat_lit 563, Int.ofNat (nat_lit 201786))]
theorem block002_data_flat113_step : block002_data_flat113 = (CoefficientMerge.fastMerge block002_data_flat111 block002_data_flat112) := by decide +kernel
theorem block002_data_flat113_original : block002_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41040 : Int) atom0218Coded) (CoefficientMerge.scale (201786 : Int) atom0219Coded)) := by
  rw [block002_data_flat113_step, block002_data_flat111_original, block002_data_flat112_original]
def block002_data_flat114 : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 254208)), (nat_lit 562, Int.ofNat (nat_lit 41040)), (nat_lit 563, Int.ofNat (nat_lit 201786))]
theorem block002_data_flat114_step : block002_data_flat114 = (CoefficientMerge.fastMerge block002_data_flat110 block002_data_flat113) := by decide +kernel
theorem block002_data_flat114_original : block002_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (254208 : Int) atom0217Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41040 : Int) atom0218Coded) (CoefficientMerge.scale (201786 : Int) atom0219Coded))) := by
  rw [block002_data_flat114_step, block002_data_flat110_original, block002_data_flat113_original]
def block002_data_flat115 : CoefficientMerge.Poly := [(nat_lit 549, Int.ofNat (nat_lit 87552)), (nat_lit 550, Int.ofNat (nat_lit 150396)), (nat_lit 551, Int.ofNat (nat_lit 254208)), (nat_lit 562, Int.ofNat (nat_lit 41040)), (nat_lit 563, Int.ofNat (nat_lit 201786))]
theorem block002_data_flat115_step : block002_data_flat115 = (CoefficientMerge.fastMerge block002_data_flat109 block002_data_flat114) := by decide +kernel
theorem block002_data_flat115_original : block002_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87552 : Int) atom0215Coded) (CoefficientMerge.scale (150396 : Int) atom0216Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254208 : Int) atom0217Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41040 : Int) atom0218Coded) (CoefficientMerge.scale (201786 : Int) atom0219Coded)))) := by
  rw [block002_data_flat115_step, block002_data_flat109_original, block002_data_flat114_original]
def block002_data_flat116 : CoefficientMerge.Poly := [(nat_lit 527, Int.ofNat (nat_lit 204288)), (nat_lit 536, Int.ofNat (nat_lit 109440)), (nat_lit 537, Int.ofNat (nat_lit 210048)), (nat_lit 538, Int.ofNat (nat_lit 157608)), (nat_lit 539, Int.ofNat (nat_lit 241152)), (nat_lit 549, Int.ofNat (nat_lit 87552)), (nat_lit 550, Int.ofNat (nat_lit 150396)), (nat_lit 551, Int.ofNat (nat_lit 254208)), (nat_lit 562, Int.ofNat (nat_lit 41040)), (nat_lit 563, Int.ofNat (nat_lit 201786))]
theorem block002_data_flat116_step : block002_data_flat116 = (CoefficientMerge.fastMerge block002_data_flat106 block002_data_flat115) := by decide +kernel
theorem block002_data_flat116_original : block002_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204288 : Int) atom0210Coded) (CoefficientMerge.scale (109440 : Int) atom0211Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210048 : Int) atom0212Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608 : Int) atom0213Coded) (CoefficientMerge.scale (241152 : Int) atom0214Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87552 : Int) atom0215Coded) (CoefficientMerge.scale (150396 : Int) atom0216Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254208 : Int) atom0217Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41040 : Int) atom0218Coded) (CoefficientMerge.scale (201786 : Int) atom0219Coded))))) := by
  rw [block002_data_flat116_step, block002_data_flat106_original, block002_data_flat115_original]
def block002_data_flat117 : CoefficientMerge.Poly := [(nat_lit 510, Int.ofNat (nat_lit 77184)), (nat_lit 511, Int.ofNat (nat_lit 121344)), (nat_lit 512, Int.ofNat (nat_lit 188160)), (nat_lit 513, Int.ofNat (nat_lit 207360)), (nat_lit 514, Int.ofNat (nat_lit 115800)), (nat_lit 515, Int.ofNat (nat_lit 217344)), (nat_lit 523, Int.ofNat (nat_lit 58752)), (nat_lit 524, Int.ofNat (nat_lit 153600)), (nat_lit 525, Int.ofNat (nat_lit 209280)), (nat_lit 526, Int.ofNat (nat_lit 149760)), (nat_lit 527, Int.ofNat (nat_lit 204288)), (nat_lit 536, Int.ofNat (nat_lit 109440)), (nat_lit 537, Int.ofNat (nat_lit 210048)), (nat_lit 538, Int.ofNat (nat_lit 157608)), (nat_lit 539, Int.ofNat (nat_lit 241152)), (nat_lit 549, Int.ofNat (nat_lit 87552)), (nat_lit 550, Int.ofNat (nat_lit 150396)), (nat_lit 551, Int.ofNat (nat_lit 254208)), (nat_lit 562, Int.ofNat (nat_lit 41040)), (nat_lit 563, Int.ofNat (nat_lit 201786))]
theorem block002_data_flat117_step : block002_data_flat117 = (CoefficientMerge.fastMerge block002_data_flat097 block002_data_flat116) := by decide +kernel
theorem block002_data_flat117_original : block002_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77184 : Int) atom0200Coded) (CoefficientMerge.scale (121344 : Int) atom0201Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (188160 : Int) atom0202Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207360 : Int) atom0203Coded) (CoefficientMerge.scale (115800 : Int) atom0204Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (217344 : Int) atom0205Coded) (CoefficientMerge.scale (58752 : Int) atom0206Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153600 : Int) atom0207Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209280 : Int) atom0208Coded) (CoefficientMerge.scale (149760 : Int) atom0209Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204288 : Int) atom0210Coded) (CoefficientMerge.scale (109440 : Int) atom0211Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210048 : Int) atom0212Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608 : Int) atom0213Coded) (CoefficientMerge.scale (241152 : Int) atom0214Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87552 : Int) atom0215Coded) (CoefficientMerge.scale (150396 : Int) atom0216Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254208 : Int) atom0217Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41040 : Int) atom0218Coded) (CoefficientMerge.scale (201786 : Int) atom0219Coded)))))) := by
  rw [block002_data_flat117_step, block002_data_flat097_original, block002_data_flat116_original]
def block002_data_flat118 : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 152064))]
theorem block002_data_flat118_step : block002_data_flat118 = (CoefficientMerge.scale (152064 : Int) atom0220Coded) := by decide +kernel
theorem block002_data_flat118_original : block002_data_flat118 = (CoefficientMerge.scale (152064 : Int) atom0220Coded) := by
  rw [block002_data_flat118_step]
def block002_data_flat119 : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 384))]
theorem block002_data_flat119_step : block002_data_flat119 = (CoefficientMerge.scale (384 : Int) atom0221Coded) := by decide +kernel
theorem block002_data_flat119_original : block002_data_flat119 = (CoefficientMerge.scale (384 : Int) atom0221Coded) := by
  rw [block002_data_flat119_step]
def block002_data_flat120 : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 152064)), (nat_lit 628, Int.ofNat (nat_lit 384))]
theorem block002_data_flat120_step : block002_data_flat120 = (CoefficientMerge.fastMerge block002_data_flat118 block002_data_flat119) := by decide +kernel
theorem block002_data_flat120_original : block002_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (152064 : Int) atom0220Coded) (CoefficientMerge.scale (384 : Int) atom0221Coded)) := by
  rw [block002_data_flat120_step, block002_data_flat118_original, block002_data_flat119_original]
def block002_data_flat121 : CoefficientMerge.Poly := [(nat_lit 630, Int.ofNat (nat_lit 21696))]
theorem block002_data_flat121_step : block002_data_flat121 = (CoefficientMerge.scale (21696 : Int) atom0222Coded) := by decide +kernel
theorem block002_data_flat121_original : block002_data_flat121 = (CoefficientMerge.scale (21696 : Int) atom0222Coded) := by
  rw [block002_data_flat121_step]
def block002_data_flat122 : CoefficientMerge.Poly := [(nat_lit 632, Int.ofNat (nat_lit 5568))]
theorem block002_data_flat122_step : block002_data_flat122 = (CoefficientMerge.scale (5568 : Int) atom0223Coded) := by decide +kernel
theorem block002_data_flat122_original : block002_data_flat122 = (CoefficientMerge.scale (5568 : Int) atom0223Coded) := by
  rw [block002_data_flat122_step]
def block002_data_flat123 : CoefficientMerge.Poly := [(nat_lit 633, Int.ofNat (nat_lit 1152))]
theorem block002_data_flat123_step : block002_data_flat123 = (CoefficientMerge.scale (1152 : Int) atom0224Coded) := by decide +kernel
theorem block002_data_flat123_original : block002_data_flat123 = (CoefficientMerge.scale (1152 : Int) atom0224Coded) := by
  rw [block002_data_flat123_step]
def block002_data_flat124 : CoefficientMerge.Poly := [(nat_lit 632, Int.ofNat (nat_lit 5568)), (nat_lit 633, Int.ofNat (nat_lit 1152))]
theorem block002_data_flat124_step : block002_data_flat124 = (CoefficientMerge.fastMerge block002_data_flat122 block002_data_flat123) := by decide +kernel
theorem block002_data_flat124_original : block002_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5568 : Int) atom0223Coded) (CoefficientMerge.scale (1152 : Int) atom0224Coded)) := by
  rw [block002_data_flat124_step, block002_data_flat122_original, block002_data_flat123_original]
def block002_data_flat125 : CoefficientMerge.Poly := [(nat_lit 630, Int.ofNat (nat_lit 21696)), (nat_lit 632, Int.ofNat (nat_lit 5568)), (nat_lit 633, Int.ofNat (nat_lit 1152))]
theorem block002_data_flat125_step : block002_data_flat125 = (CoefficientMerge.fastMerge block002_data_flat121 block002_data_flat124) := by decide +kernel
theorem block002_data_flat125_original : block002_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21696 : Int) atom0222Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5568 : Int) atom0223Coded) (CoefficientMerge.scale (1152 : Int) atom0224Coded))) := by
  rw [block002_data_flat125_step, block002_data_flat121_original, block002_data_flat124_original]
def block002_data_flat126 : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 152064)), (nat_lit 628, Int.ofNat (nat_lit 384)), (nat_lit 630, Int.ofNat (nat_lit 21696)), (nat_lit 632, Int.ofNat (nat_lit 5568)), (nat_lit 633, Int.ofNat (nat_lit 1152))]
theorem block002_data_flat126_step : block002_data_flat126 = (CoefficientMerge.fastMerge block002_data_flat120 block002_data_flat125) := by decide +kernel
theorem block002_data_flat126_original : block002_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152064 : Int) atom0220Coded) (CoefficientMerge.scale (384 : Int) atom0221Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21696 : Int) atom0222Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5568 : Int) atom0223Coded) (CoefficientMerge.scale (1152 : Int) atom0224Coded)))) := by
  rw [block002_data_flat126_step, block002_data_flat120_original, block002_data_flat125_original]
def block002_data_flat127 : CoefficientMerge.Poly := [(nat_lit 635, Int.ofNat (nat_lit 6144))]
theorem block002_data_flat127_step : block002_data_flat127 = (CoefficientMerge.scale (6144 : Int) atom0225Coded) := by decide +kernel
theorem block002_data_flat127_original : block002_data_flat127 = (CoefficientMerge.scale (6144 : Int) atom0225Coded) := by
  rw [block002_data_flat127_step]
def block002_data_flat128 : CoefficientMerge.Poly := [(nat_lit 641, Int.ofNat (nat_lit 3840))]
theorem block002_data_flat128_step : block002_data_flat128 = (CoefficientMerge.scale (3840 : Int) atom0226Coded) := by decide +kernel
theorem block002_data_flat128_original : block002_data_flat128 = (CoefficientMerge.scale (3840 : Int) atom0226Coded) := by
  rw [block002_data_flat128_step]
def block002_data_flat129 : CoefficientMerge.Poly := [(nat_lit 635, Int.ofNat (nat_lit 6144)), (nat_lit 641, Int.ofNat (nat_lit 3840))]
theorem block002_data_flat129_step : block002_data_flat129 = (CoefficientMerge.fastMerge block002_data_flat127 block002_data_flat128) := by decide +kernel
theorem block002_data_flat129_original : block002_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6144 : Int) atom0225Coded) (CoefficientMerge.scale (3840 : Int) atom0226Coded)) := by
  rw [block002_data_flat129_step, block002_data_flat127_original, block002_data_flat128_original]
def block002_data_flat130 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 28320))]
theorem block002_data_flat130_step : block002_data_flat130 = (CoefficientMerge.scale (28320 : Int) atom0227Coded) := by decide +kernel
theorem block002_data_flat130_original : block002_data_flat130 = (CoefficientMerge.scale (28320 : Int) atom0227Coded) := by
  rw [block002_data_flat130_step]
def block002_data_flat131 : CoefficientMerge.Poly := [(nat_lit 643, Int.ofNat (nat_lit 5760))]
theorem block002_data_flat131_step : block002_data_flat131 = (CoefficientMerge.scale (5760 : Int) atom0228Coded) := by decide +kernel
theorem block002_data_flat131_original : block002_data_flat131 = (CoefficientMerge.scale (5760 : Int) atom0228Coded) := by
  rw [block002_data_flat131_step]
def block002_data_flat132 : CoefficientMerge.Poly := [(nat_lit 644, Int.ofNat (nat_lit 28512))]
theorem block002_data_flat132_step : block002_data_flat132 = (CoefficientMerge.scale (28512 : Int) atom0229Coded) := by decide +kernel
theorem block002_data_flat132_original : block002_data_flat132 = (CoefficientMerge.scale (28512 : Int) atom0229Coded) := by
  rw [block002_data_flat132_step]
def block002_data_flat133 : CoefficientMerge.Poly := [(nat_lit 643, Int.ofNat (nat_lit 5760)), (nat_lit 644, Int.ofNat (nat_lit 28512))]
theorem block002_data_flat133_step : block002_data_flat133 = (CoefficientMerge.fastMerge block002_data_flat131 block002_data_flat132) := by decide +kernel
theorem block002_data_flat133_original : block002_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5760 : Int) atom0228Coded) (CoefficientMerge.scale (28512 : Int) atom0229Coded)) := by
  rw [block002_data_flat133_step, block002_data_flat131_original, block002_data_flat132_original]
def block002_data_flat134 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 28320)), (nat_lit 643, Int.ofNat (nat_lit 5760)), (nat_lit 644, Int.ofNat (nat_lit 28512))]
theorem block002_data_flat134_step : block002_data_flat134 = (CoefficientMerge.fastMerge block002_data_flat130 block002_data_flat133) := by decide +kernel
theorem block002_data_flat134_original : block002_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28320 : Int) atom0227Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5760 : Int) atom0228Coded) (CoefficientMerge.scale (28512 : Int) atom0229Coded))) := by
  rw [block002_data_flat134_step, block002_data_flat130_original, block002_data_flat133_original]
def block002_data_flat135 : CoefficientMerge.Poly := [(nat_lit 635, Int.ofNat (nat_lit 6144)), (nat_lit 641, Int.ofNat (nat_lit 3840)), (nat_lit 642, Int.ofNat (nat_lit 28320)), (nat_lit 643, Int.ofNat (nat_lit 5760)), (nat_lit 644, Int.ofNat (nat_lit 28512))]
theorem block002_data_flat135_step : block002_data_flat135 = (CoefficientMerge.fastMerge block002_data_flat129 block002_data_flat134) := by decide +kernel
theorem block002_data_flat135_original : block002_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6144 : Int) atom0225Coded) (CoefficientMerge.scale (3840 : Int) atom0226Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28320 : Int) atom0227Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5760 : Int) atom0228Coded) (CoefficientMerge.scale (28512 : Int) atom0229Coded)))) := by
  rw [block002_data_flat135_step, block002_data_flat129_original, block002_data_flat134_original]
def block002_data_flat136 : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 152064)), (nat_lit 628, Int.ofNat (nat_lit 384)), (nat_lit 630, Int.ofNat (nat_lit 21696)), (nat_lit 632, Int.ofNat (nat_lit 5568)), (nat_lit 633, Int.ofNat (nat_lit 1152)), (nat_lit 635, Int.ofNat (nat_lit 6144)), (nat_lit 641, Int.ofNat (nat_lit 3840)), (nat_lit 642, Int.ofNat (nat_lit 28320)), (nat_lit 643, Int.ofNat (nat_lit 5760)), (nat_lit 644, Int.ofNat (nat_lit 28512))]
theorem block002_data_flat136_step : block002_data_flat136 = (CoefficientMerge.fastMerge block002_data_flat126 block002_data_flat135) := by decide +kernel
theorem block002_data_flat136_original : block002_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152064 : Int) atom0220Coded) (CoefficientMerge.scale (384 : Int) atom0221Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21696 : Int) atom0222Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5568 : Int) atom0223Coded) (CoefficientMerge.scale (1152 : Int) atom0224Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6144 : Int) atom0225Coded) (CoefficientMerge.scale (3840 : Int) atom0226Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28320 : Int) atom0227Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5760 : Int) atom0228Coded) (CoefficientMerge.scale (28512 : Int) atom0229Coded))))) := by
  rw [block002_data_flat136_step, block002_data_flat126_original, block002_data_flat135_original]
def block002_data_flat137 : CoefficientMerge.Poly := [(nat_lit 645, Int.ofNat (nat_lit 37488))]
theorem block002_data_flat137_step : block002_data_flat137 = (CoefficientMerge.scale (37488 : Int) atom0230Coded) := by decide +kernel
theorem block002_data_flat137_original : block002_data_flat137 = (CoefficientMerge.scale (37488 : Int) atom0230Coded) := by
  rw [block002_data_flat137_step]
def block002_data_flat138 : CoefficientMerge.Poly := [(nat_lit 646, Int.ofNat (nat_lit 48768))]
theorem block002_data_flat138_step : block002_data_flat138 = (CoefficientMerge.scale (48768 : Int) atom0231Coded) := by decide +kernel
theorem block002_data_flat138_original : block002_data_flat138 = (CoefficientMerge.scale (48768 : Int) atom0231Coded) := by
  rw [block002_data_flat138_step]
def block002_data_flat139 : CoefficientMerge.Poly := [(nat_lit 645, Int.ofNat (nat_lit 37488)), (nat_lit 646, Int.ofNat (nat_lit 48768))]
theorem block002_data_flat139_step : block002_data_flat139 = (CoefficientMerge.fastMerge block002_data_flat137 block002_data_flat138) := by decide +kernel
theorem block002_data_flat139_original : block002_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37488 : Int) atom0230Coded) (CoefficientMerge.scale (48768 : Int) atom0231Coded)) := by
  rw [block002_data_flat139_step, block002_data_flat137_original, block002_data_flat138_original]
def block002_data_flat140 : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 106344))]
theorem block002_data_flat140_step : block002_data_flat140 = (CoefficientMerge.scale (106344 : Int) atom0232Coded) := by decide +kernel
theorem block002_data_flat140_original : block002_data_flat140 = (CoefficientMerge.scale (106344 : Int) atom0232Coded) := by
  rw [block002_data_flat140_step]
def block002_data_flat141 : CoefficientMerge.Poly := [(nat_lit 654, Int.ofNat (nat_lit 48960))]
theorem block002_data_flat141_step : block002_data_flat141 = (CoefficientMerge.scale (48960 : Int) atom0233Coded) := by decide +kernel
theorem block002_data_flat141_original : block002_data_flat141 = (CoefficientMerge.scale (48960 : Int) atom0233Coded) := by
  rw [block002_data_flat141_step]
def block002_data_flat142 : CoefficientMerge.Poly := [(nat_lit 655, Int.ofNat (nat_lit 80064))]
theorem block002_data_flat142_step : block002_data_flat142 = (CoefficientMerge.scale (80064 : Int) atom0234Coded) := by decide +kernel
theorem block002_data_flat142_original : block002_data_flat142 = (CoefficientMerge.scale (80064 : Int) atom0234Coded) := by
  rw [block002_data_flat142_step]
def block002_data_flat143 : CoefficientMerge.Poly := [(nat_lit 654, Int.ofNat (nat_lit 48960)), (nat_lit 655, Int.ofNat (nat_lit 80064))]
theorem block002_data_flat143_step : block002_data_flat143 = (CoefficientMerge.fastMerge block002_data_flat141 block002_data_flat142) := by decide +kernel
theorem block002_data_flat143_original : block002_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48960 : Int) atom0233Coded) (CoefficientMerge.scale (80064 : Int) atom0234Coded)) := by
  rw [block002_data_flat143_step, block002_data_flat141_original, block002_data_flat142_original]
def block002_data_flat144 : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 106344)), (nat_lit 654, Int.ofNat (nat_lit 48960)), (nat_lit 655, Int.ofNat (nat_lit 80064))]
theorem block002_data_flat144_step : block002_data_flat144 = (CoefficientMerge.fastMerge block002_data_flat140 block002_data_flat143) := by decide +kernel
theorem block002_data_flat144_original : block002_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (106344 : Int) atom0232Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48960 : Int) atom0233Coded) (CoefficientMerge.scale (80064 : Int) atom0234Coded))) := by
  rw [block002_data_flat144_step, block002_data_flat140_original, block002_data_flat143_original]
def block002_data_flat145 : CoefficientMerge.Poly := [(nat_lit 645, Int.ofNat (nat_lit 37488)), (nat_lit 646, Int.ofNat (nat_lit 48768)), (nat_lit 647, Int.ofNat (nat_lit 106344)), (nat_lit 654, Int.ofNat (nat_lit 48960)), (nat_lit 655, Int.ofNat (nat_lit 80064))]
theorem block002_data_flat145_step : block002_data_flat145 = (CoefficientMerge.fastMerge block002_data_flat139 block002_data_flat144) := by decide +kernel
theorem block002_data_flat145_original : block002_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37488 : Int) atom0230Coded) (CoefficientMerge.scale (48768 : Int) atom0231Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (106344 : Int) atom0232Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48960 : Int) atom0233Coded) (CoefficientMerge.scale (80064 : Int) atom0234Coded)))) := by
  rw [block002_data_flat145_step, block002_data_flat139_original, block002_data_flat144_original]
def block002_data_flat146 : CoefficientMerge.Poly := [(nat_lit 656, Int.ofNat (nat_lit 153216))]
theorem block002_data_flat146_step : block002_data_flat146 = (CoefficientMerge.scale (153216 : Int) atom0235Coded) := by decide +kernel
theorem block002_data_flat146_original : block002_data_flat146 = (CoefficientMerge.scale (153216 : Int) atom0235Coded) := by
  rw [block002_data_flat146_step]
def block002_data_flat147 : CoefficientMerge.Poly := [(nat_lit 657, Int.ofNat (nat_lit 183168))]
theorem block002_data_flat147_step : block002_data_flat147 = (CoefficientMerge.scale (183168 : Int) atom0236Coded) := by decide +kernel
theorem block002_data_flat147_original : block002_data_flat147 = (CoefficientMerge.scale (183168 : Int) atom0236Coded) := by
  rw [block002_data_flat147_step]
def block002_data_flat148 : CoefficientMerge.Poly := [(nat_lit 656, Int.ofNat (nat_lit 153216)), (nat_lit 657, Int.ofNat (nat_lit 183168))]
theorem block002_data_flat148_step : block002_data_flat148 = (CoefficientMerge.fastMerge block002_data_flat146 block002_data_flat147) := by decide +kernel
theorem block002_data_flat148_original : block002_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (153216 : Int) atom0235Coded) (CoefficientMerge.scale (183168 : Int) atom0236Coded)) := by
  rw [block002_data_flat148_step, block002_data_flat146_original, block002_data_flat147_original]
def block002_data_flat149 : CoefficientMerge.Poly := [(nat_lit 658, Int.ofNat (nat_lit 102048))]
theorem block002_data_flat149_step : block002_data_flat149 = (CoefficientMerge.scale (102048 : Int) atom0237Coded) := by decide +kernel
theorem block002_data_flat149_original : block002_data_flat149 = (CoefficientMerge.scale (102048 : Int) atom0237Coded) := by
  rw [block002_data_flat149_step]
def block002_data_flat150 : CoefficientMerge.Poly := [(nat_lit 659, Int.ofNat (nat_lit 214656))]
theorem block002_data_flat150_step : block002_data_flat150 = (CoefficientMerge.scale (214656 : Int) atom0238Coded) := by decide +kernel
theorem block002_data_flat150_original : block002_data_flat150 = (CoefficientMerge.scale (214656 : Int) atom0238Coded) := by
  rw [block002_data_flat150_step]
def block002_data_flat151 : CoefficientMerge.Poly := [(nat_lit 667, Int.ofNat (nat_lit 38016))]
theorem block002_data_flat151_step : block002_data_flat151 = (CoefficientMerge.scale (38016 : Int) atom0239Coded) := by decide +kernel
theorem block002_data_flat151_original : block002_data_flat151 = (CoefficientMerge.scale (38016 : Int) atom0239Coded) := by
  rw [block002_data_flat151_step]
def block002_data_flat152 : CoefficientMerge.Poly := [(nat_lit 659, Int.ofNat (nat_lit 214656)), (nat_lit 667, Int.ofNat (nat_lit 38016))]
theorem block002_data_flat152_step : block002_data_flat152 = (CoefficientMerge.fastMerge block002_data_flat150 block002_data_flat151) := by decide +kernel
theorem block002_data_flat152_original : block002_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (214656 : Int) atom0238Coded) (CoefficientMerge.scale (38016 : Int) atom0239Coded)) := by
  rw [block002_data_flat152_step, block002_data_flat150_original, block002_data_flat151_original]
def block002_data_flat153 : CoefficientMerge.Poly := [(nat_lit 658, Int.ofNat (nat_lit 102048)), (nat_lit 659, Int.ofNat (nat_lit 214656)), (nat_lit 667, Int.ofNat (nat_lit 38016))]
theorem block002_data_flat153_step : block002_data_flat153 = (CoefficientMerge.fastMerge block002_data_flat149 block002_data_flat152) := by decide +kernel
theorem block002_data_flat153_original : block002_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (102048 : Int) atom0237Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214656 : Int) atom0238Coded) (CoefficientMerge.scale (38016 : Int) atom0239Coded))) := by
  rw [block002_data_flat153_step, block002_data_flat149_original, block002_data_flat152_original]
def block002_data_flat154 : CoefficientMerge.Poly := [(nat_lit 656, Int.ofNat (nat_lit 153216)), (nat_lit 657, Int.ofNat (nat_lit 183168)), (nat_lit 658, Int.ofNat (nat_lit 102048)), (nat_lit 659, Int.ofNat (nat_lit 214656)), (nat_lit 667, Int.ofNat (nat_lit 38016))]
theorem block002_data_flat154_step : block002_data_flat154 = (CoefficientMerge.fastMerge block002_data_flat148 block002_data_flat153) := by decide +kernel
theorem block002_data_flat154_original : block002_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153216 : Int) atom0235Coded) (CoefficientMerge.scale (183168 : Int) atom0236Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102048 : Int) atom0237Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214656 : Int) atom0238Coded) (CoefficientMerge.scale (38016 : Int) atom0239Coded)))) := by
  rw [block002_data_flat154_step, block002_data_flat148_original, block002_data_flat153_original]
def block002_data_flat155 : CoefficientMerge.Poly := [(nat_lit 645, Int.ofNat (nat_lit 37488)), (nat_lit 646, Int.ofNat (nat_lit 48768)), (nat_lit 647, Int.ofNat (nat_lit 106344)), (nat_lit 654, Int.ofNat (nat_lit 48960)), (nat_lit 655, Int.ofNat (nat_lit 80064)), (nat_lit 656, Int.ofNat (nat_lit 153216)), (nat_lit 657, Int.ofNat (nat_lit 183168)), (nat_lit 658, Int.ofNat (nat_lit 102048)), (nat_lit 659, Int.ofNat (nat_lit 214656)), (nat_lit 667, Int.ofNat (nat_lit 38016))]
theorem block002_data_flat155_step : block002_data_flat155 = (CoefficientMerge.fastMerge block002_data_flat145 block002_data_flat154) := by decide +kernel
theorem block002_data_flat155_original : block002_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37488 : Int) atom0230Coded) (CoefficientMerge.scale (48768 : Int) atom0231Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (106344 : Int) atom0232Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48960 : Int) atom0233Coded) (CoefficientMerge.scale (80064 : Int) atom0234Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153216 : Int) atom0235Coded) (CoefficientMerge.scale (183168 : Int) atom0236Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102048 : Int) atom0237Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214656 : Int) atom0238Coded) (CoefficientMerge.scale (38016 : Int) atom0239Coded))))) := by
  rw [block002_data_flat155_step, block002_data_flat145_original, block002_data_flat154_original]
def block002_data_flat156 : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 152064)), (nat_lit 628, Int.ofNat (nat_lit 384)), (nat_lit 630, Int.ofNat (nat_lit 21696)), (nat_lit 632, Int.ofNat (nat_lit 5568)), (nat_lit 633, Int.ofNat (nat_lit 1152)), (nat_lit 635, Int.ofNat (nat_lit 6144)), (nat_lit 641, Int.ofNat (nat_lit 3840)), (nat_lit 642, Int.ofNat (nat_lit 28320)), (nat_lit 643, Int.ofNat (nat_lit 5760)), (nat_lit 644, Int.ofNat (nat_lit 28512)), (nat_lit 645, Int.ofNat (nat_lit 37488)), (nat_lit 646, Int.ofNat (nat_lit 48768)), (nat_lit 647, Int.ofNat (nat_lit 106344)), (nat_lit 654, Int.ofNat (nat_lit 48960)), (nat_lit 655, Int.ofNat (nat_lit 80064)), (nat_lit 656, Int.ofNat (nat_lit 153216)), (nat_lit 657, Int.ofNat (nat_lit 183168)), (nat_lit 658, Int.ofNat (nat_lit 102048)), (nat_lit 659, Int.ofNat (nat_lit 214656)), (nat_lit 667, Int.ofNat (nat_lit 38016))]
theorem block002_data_flat156_step : block002_data_flat156 = (CoefficientMerge.fastMerge block002_data_flat136 block002_data_flat155) := by decide +kernel
theorem block002_data_flat156_original : block002_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152064 : Int) atom0220Coded) (CoefficientMerge.scale (384 : Int) atom0221Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21696 : Int) atom0222Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5568 : Int) atom0223Coded) (CoefficientMerge.scale (1152 : Int) atom0224Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6144 : Int) atom0225Coded) (CoefficientMerge.scale (3840 : Int) atom0226Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28320 : Int) atom0227Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5760 : Int) atom0228Coded) (CoefficientMerge.scale (28512 : Int) atom0229Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37488 : Int) atom0230Coded) (CoefficientMerge.scale (48768 : Int) atom0231Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (106344 : Int) atom0232Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48960 : Int) atom0233Coded) (CoefficientMerge.scale (80064 : Int) atom0234Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153216 : Int) atom0235Coded) (CoefficientMerge.scale (183168 : Int) atom0236Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102048 : Int) atom0237Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214656 : Int) atom0238Coded) (CoefficientMerge.scale (38016 : Int) atom0239Coded)))))) := by
  rw [block002_data_flat156_step, block002_data_flat136_original, block002_data_flat155_original]
def block002_data_flat157 : CoefficientMerge.Poly := [(nat_lit 510, Int.ofNat (nat_lit 77184)), (nat_lit 511, Int.ofNat (nat_lit 121344)), (nat_lit 512, Int.ofNat (nat_lit 188160)), (nat_lit 513, Int.ofNat (nat_lit 207360)), (nat_lit 514, Int.ofNat (nat_lit 115800)), (nat_lit 515, Int.ofNat (nat_lit 217344)), (nat_lit 523, Int.ofNat (nat_lit 58752)), (nat_lit 524, Int.ofNat (nat_lit 153600)), (nat_lit 525, Int.ofNat (nat_lit 209280)), (nat_lit 526, Int.ofNat (nat_lit 149760)), (nat_lit 527, Int.ofNat (nat_lit 204288)), (nat_lit 536, Int.ofNat (nat_lit 109440)), (nat_lit 537, Int.ofNat (nat_lit 210048)), (nat_lit 538, Int.ofNat (nat_lit 157608)), (nat_lit 539, Int.ofNat (nat_lit 241152)), (nat_lit 549, Int.ofNat (nat_lit 87552)), (nat_lit 550, Int.ofNat (nat_lit 150396)), (nat_lit 551, Int.ofNat (nat_lit 254208)), (nat_lit 562, Int.ofNat (nat_lit 41040)), (nat_lit 563, Int.ofNat (nat_lit 201786)), (nat_lit 575, Int.ofNat (nat_lit 152064)), (nat_lit 628, Int.ofNat (nat_lit 384)), (nat_lit 630, Int.ofNat (nat_lit 21696)), (nat_lit 632, Int.ofNat (nat_lit 5568)), (nat_lit 633, Int.ofNat (nat_lit 1152)), (nat_lit 635, Int.ofNat (nat_lit 6144)), (nat_lit 641, Int.ofNat (nat_lit 3840)), (nat_lit 642, Int.ofNat (nat_lit 28320)), (nat_lit 643, Int.ofNat (nat_lit 5760)), (nat_lit 644, Int.ofNat (nat_lit 28512)), (nat_lit 645, Int.ofNat (nat_lit 37488)), (nat_lit 646, Int.ofNat (nat_lit 48768)), (nat_lit 647, Int.ofNat (nat_lit 106344)), (nat_lit 654, Int.ofNat (nat_lit 48960)), (nat_lit 655, Int.ofNat (nat_lit 80064)), (nat_lit 656, Int.ofNat (nat_lit 153216)), (nat_lit 657, Int.ofNat (nat_lit 183168)), (nat_lit 658, Int.ofNat (nat_lit 102048)), (nat_lit 659, Int.ofNat (nat_lit 214656)), (nat_lit 667, Int.ofNat (nat_lit 38016))]
theorem block002_data_flat157_step : block002_data_flat157 = (CoefficientMerge.fastMerge block002_data_flat117 block002_data_flat156) := by decide +kernel
theorem block002_data_flat157_original : block002_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77184 : Int) atom0200Coded) (CoefficientMerge.scale (121344 : Int) atom0201Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (188160 : Int) atom0202Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207360 : Int) atom0203Coded) (CoefficientMerge.scale (115800 : Int) atom0204Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (217344 : Int) atom0205Coded) (CoefficientMerge.scale (58752 : Int) atom0206Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153600 : Int) atom0207Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209280 : Int) atom0208Coded) (CoefficientMerge.scale (149760 : Int) atom0209Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204288 : Int) atom0210Coded) (CoefficientMerge.scale (109440 : Int) atom0211Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210048 : Int) atom0212Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608 : Int) atom0213Coded) (CoefficientMerge.scale (241152 : Int) atom0214Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87552 : Int) atom0215Coded) (CoefficientMerge.scale (150396 : Int) atom0216Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254208 : Int) atom0217Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41040 : Int) atom0218Coded) (CoefficientMerge.scale (201786 : Int) atom0219Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152064 : Int) atom0220Coded) (CoefficientMerge.scale (384 : Int) atom0221Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21696 : Int) atom0222Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5568 : Int) atom0223Coded) (CoefficientMerge.scale (1152 : Int) atom0224Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6144 : Int) atom0225Coded) (CoefficientMerge.scale (3840 : Int) atom0226Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28320 : Int) atom0227Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5760 : Int) atom0228Coded) (CoefficientMerge.scale (28512 : Int) atom0229Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37488 : Int) atom0230Coded) (CoefficientMerge.scale (48768 : Int) atom0231Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (106344 : Int) atom0232Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48960 : Int) atom0233Coded) (CoefficientMerge.scale (80064 : Int) atom0234Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153216 : Int) atom0235Coded) (CoefficientMerge.scale (183168 : Int) atom0236Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102048 : Int) atom0237Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214656 : Int) atom0238Coded) (CoefficientMerge.scale (38016 : Int) atom0239Coded))))))) := by
  rw [block002_data_flat157_step, block002_data_flat117_original, block002_data_flat156_original]
def block002_data_flat158 : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 167040)), (nat_lit 368, Int.ofNat (nat_lit 223104)), (nat_lit 369, Int.ofNat (nat_lit 231552)), (nat_lit 370, Int.ofNat (nat_lit 122400)), (nat_lit 371, Int.ofNat (nat_lit 225744)), (nat_lit 379, Int.ofNat (nat_lit 79488)), (nat_lit 380, Int.ofNat (nat_lit 181440)), (nat_lit 381, Int.ofNat (nat_lit 223488)), (nat_lit 382, Int.ofNat (nat_lit 150336)), (nat_lit 383, Int.ofNat (nat_lit 195312)), (nat_lit 392, Int.ofNat (nat_lit 119808)), (nat_lit 393, Int.ofNat (nat_lit 214272)), (nat_lit 394, Int.ofNat (nat_lit 152160)), (nat_lit 395, Int.ofNat (nat_lit 213168)), (nat_lit 405, Int.ofNat (nat_lit 84672)), (nat_lit 406, Int.ofNat (nat_lit 135504)), (nat_lit 407, Int.ofNat (nat_lit 208848)), (nat_lit 418, Int.ofNat (nat_lit 35712)), (nat_lit 419, Int.ofNat (nat_lit 152808)), (nat_lit 431, Int.ofNat (nat_lit 106704)), (nat_lit 471, Int.ofNat (nat_lit 4608)), (nat_lit 474, Int.ofNat (nat_lit 36672)), (nat_lit 475, Int.ofNat (nat_lit 96)), (nat_lit 476, Int.ofNat (nat_lit 10656)), (nat_lit 477, Int.ofNat (nat_lit 1584)), (nat_lit 479, Int.ofNat (nat_lit 1680)), (nat_lit 485, Int.ofNat (nat_lit 2112)), (nat_lit 486, Int.ofNat (nat_lit 69696)), (nat_lit 487, Int.ofNat (nat_lit 20352)), (nat_lit 488, Int.ofNat (nat_lit 53184)), (nat_lit 489, Int.ofNat (nat_lit 48288)), (nat_lit 490, Int.ofNat (nat_lit 60528)), (nat_lit 491, Int.ofNat (nat_lit 86640)), (nat_lit 497, Int.ofNat (nat_lit 10368)), (nat_lit 498, Int.ofNat (nat_lit 72960)), (nat_lit 499, Int.ofNat (nat_lit 46848)), (nat_lit 500, Int.ofNat (nat_lit 83712)), (nat_lit 501, Int.ofNat (nat_lit 91392)), (nat_lit 502, Int.ofNat (nat_lit 102000)), (nat_lit 503, Int.ofNat (nat_lit 154368)), (nat_lit 510, Int.ofNat (nat_lit 77184)), (nat_lit 511, Int.ofNat (nat_lit 121344)), (nat_lit 512, Int.ofNat (nat_lit 188160)), (nat_lit 513, Int.ofNat (nat_lit 207360)), (nat_lit 514, Int.ofNat (nat_lit 115800)), (nat_lit 515, Int.ofNat (nat_lit 217344)), (nat_lit 523, Int.ofNat (nat_lit 58752)), (nat_lit 524, Int.ofNat (nat_lit 153600)), (nat_lit 525, Int.ofNat (nat_lit 209280)), (nat_lit 526, Int.ofNat (nat_lit 149760)), (nat_lit 527, Int.ofNat (nat_lit 204288)), (nat_lit 536, Int.ofNat (nat_lit 109440)), (nat_lit 537, Int.ofNat (nat_lit 210048)), (nat_lit 538, Int.ofNat (nat_lit 157608)), (nat_lit 539, Int.ofNat (nat_lit 241152)), (nat_lit 549, Int.ofNat (nat_lit 87552)), (nat_lit 550, Int.ofNat (nat_lit 150396)), (nat_lit 551, Int.ofNat (nat_lit 254208)), (nat_lit 562, Int.ofNat (nat_lit 41040)), (nat_lit 563, Int.ofNat (nat_lit 201786)), (nat_lit 575, Int.ofNat (nat_lit 152064)), (nat_lit 628, Int.ofNat (nat_lit 384)), (nat_lit 630, Int.ofNat (nat_lit 21696)), (nat_lit 632, Int.ofNat (nat_lit 5568)), (nat_lit 633, Int.ofNat (nat_lit 1152)), (nat_lit 635, Int.ofNat (nat_lit 6144)), (nat_lit 641, Int.ofNat (nat_lit 3840)), (nat_lit 642, Int.ofNat (nat_lit 28320)), (nat_lit 643, Int.ofNat (nat_lit 5760)), (nat_lit 644, Int.ofNat (nat_lit 28512)), (nat_lit 645, Int.ofNat (nat_lit 37488)), (nat_lit 646, Int.ofNat (nat_lit 48768)), (nat_lit 647, Int.ofNat (nat_lit 106344)), (nat_lit 654, Int.ofNat (nat_lit 48960)), (nat_lit 655, Int.ofNat (nat_lit 80064)), (nat_lit 656, Int.ofNat (nat_lit 153216)), (nat_lit 657, Int.ofNat (nat_lit 183168)), (nat_lit 658, Int.ofNat (nat_lit 102048)), (nat_lit 659, Int.ofNat (nat_lit 214656)), (nat_lit 667, Int.ofNat (nat_lit 38016))]
theorem block002_data_flat158_step : block002_data_flat158 = (CoefficientMerge.fastMerge block002_data_flat078 block002_data_flat157) := by decide +kernel
theorem block002_data_flat158_original : block002_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167040 : Int) atom0160Coded) (CoefficientMerge.scale (223104 : Int) atom0161Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231552 : Int) atom0162Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122400 : Int) atom0163Coded) (CoefficientMerge.scale (225744 : Int) atom0164Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79488 : Int) atom0165Coded) (CoefficientMerge.scale (181440 : Int) atom0166Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223488 : Int) atom0167Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150336 : Int) atom0168Coded) (CoefficientMerge.scale (195312 : Int) atom0169Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (119808 : Int) atom0170Coded) (CoefficientMerge.scale (214272 : Int) atom0171Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152160 : Int) atom0172Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213168 : Int) atom0173Coded) (CoefficientMerge.scale (84672 : Int) atom0174Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (135504 : Int) atom0175Coded) (CoefficientMerge.scale (208848 : Int) atom0176Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35712 : Int) atom0177Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808 : Int) atom0178Coded) (CoefficientMerge.scale (106704 : Int) atom0179Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4608 : Int) atom0180Coded) (CoefficientMerge.scale (36672 : Int) atom0181Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96 : Int) atom0182Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10656 : Int) atom0183Coded) (CoefficientMerge.scale (1584 : Int) atom0184Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1680 : Int) atom0185Coded) (CoefficientMerge.scale (2112 : Int) atom0186Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69696 : Int) atom0187Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20352 : Int) atom0188Coded) (CoefficientMerge.scale (53184 : Int) atom0189Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48288 : Int) atom0190Coded) (CoefficientMerge.scale (60528 : Int) atom0191Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86640 : Int) atom0192Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10368 : Int) atom0193Coded) (CoefficientMerge.scale (72960 : Int) atom0194Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46848 : Int) atom0195Coded) (CoefficientMerge.scale (83712 : Int) atom0196Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91392 : Int) atom0197Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102000 : Int) atom0198Coded) (CoefficientMerge.scale (154368 : Int) atom0199Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77184 : Int) atom0200Coded) (CoefficientMerge.scale (121344 : Int) atom0201Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (188160 : Int) atom0202Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207360 : Int) atom0203Coded) (CoefficientMerge.scale (115800 : Int) atom0204Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (217344 : Int) atom0205Coded) (CoefficientMerge.scale (58752 : Int) atom0206Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153600 : Int) atom0207Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209280 : Int) atom0208Coded) (CoefficientMerge.scale (149760 : Int) atom0209Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204288 : Int) atom0210Coded) (CoefficientMerge.scale (109440 : Int) atom0211Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210048 : Int) atom0212Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608 : Int) atom0213Coded) (CoefficientMerge.scale (241152 : Int) atom0214Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87552 : Int) atom0215Coded) (CoefficientMerge.scale (150396 : Int) atom0216Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254208 : Int) atom0217Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41040 : Int) atom0218Coded) (CoefficientMerge.scale (201786 : Int) atom0219Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152064 : Int) atom0220Coded) (CoefficientMerge.scale (384 : Int) atom0221Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21696 : Int) atom0222Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5568 : Int) atom0223Coded) (CoefficientMerge.scale (1152 : Int) atom0224Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6144 : Int) atom0225Coded) (CoefficientMerge.scale (3840 : Int) atom0226Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28320 : Int) atom0227Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5760 : Int) atom0228Coded) (CoefficientMerge.scale (28512 : Int) atom0229Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37488 : Int) atom0230Coded) (CoefficientMerge.scale (48768 : Int) atom0231Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (106344 : Int) atom0232Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48960 : Int) atom0233Coded) (CoefficientMerge.scale (80064 : Int) atom0234Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153216 : Int) atom0235Coded) (CoefficientMerge.scale (183168 : Int) atom0236Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102048 : Int) atom0237Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214656 : Int) atom0238Coded) (CoefficientMerge.scale (38016 : Int) atom0239Coded)))))))) := by
  rw [block002_data_flat158_step, block002_data_flat078_original, block002_data_flat157_original]
def block002_data_flat159 : CoefficientMerge.Poly := [(nat_lit 367, Int.ofNat (nat_lit 167040)), (nat_lit 368, Int.ofNat (nat_lit 223104)), (nat_lit 369, Int.ofNat (nat_lit 231552)), (nat_lit 370, Int.ofNat (nat_lit 122400)), (nat_lit 371, Int.ofNat (nat_lit 225744)), (nat_lit 379, Int.ofNat (nat_lit 79488)), (nat_lit 380, Int.ofNat (nat_lit 181440)), (nat_lit 381, Int.ofNat (nat_lit 223488)), (nat_lit 382, Int.ofNat (nat_lit 150336)), (nat_lit 383, Int.ofNat (nat_lit 195312)), (nat_lit 392, Int.ofNat (nat_lit 119808)), (nat_lit 393, Int.ofNat (nat_lit 214272)), (nat_lit 394, Int.ofNat (nat_lit 152160)), (nat_lit 395, Int.ofNat (nat_lit 213168)), (nat_lit 405, Int.ofNat (nat_lit 84672)), (nat_lit 406, Int.ofNat (nat_lit 135504)), (nat_lit 407, Int.ofNat (nat_lit 208848)), (nat_lit 418, Int.ofNat (nat_lit 35712)), (nat_lit 419, Int.ofNat (nat_lit 152808)), (nat_lit 431, Int.ofNat (nat_lit 106704)), (nat_lit 471, Int.ofNat (nat_lit 4608)), (nat_lit 474, Int.ofNat (nat_lit 36672)), (nat_lit 475, Int.ofNat (nat_lit 96)), (nat_lit 476, Int.ofNat (nat_lit 10656)), (nat_lit 477, Int.ofNat (nat_lit 1584)), (nat_lit 479, Int.ofNat (nat_lit 1680)), (nat_lit 485, Int.ofNat (nat_lit 2112)), (nat_lit 486, Int.ofNat (nat_lit 69696)), (nat_lit 487, Int.ofNat (nat_lit 20352)), (nat_lit 488, Int.ofNat (nat_lit 53184)), (nat_lit 489, Int.ofNat (nat_lit 48288)), (nat_lit 490, Int.ofNat (nat_lit 60528)), (nat_lit 491, Int.ofNat (nat_lit 86640)), (nat_lit 497, Int.ofNat (nat_lit 10368)), (nat_lit 498, Int.ofNat (nat_lit 72960)), (nat_lit 499, Int.ofNat (nat_lit 46848)), (nat_lit 500, Int.ofNat (nat_lit 83712)), (nat_lit 501, Int.ofNat (nat_lit 91392)), (nat_lit 502, Int.ofNat (nat_lit 102000)), (nat_lit 503, Int.ofNat (nat_lit 154368)), (nat_lit 510, Int.ofNat (nat_lit 77184)), (nat_lit 511, Int.ofNat (nat_lit 121344)), (nat_lit 512, Int.ofNat (nat_lit 188160)), (nat_lit 513, Int.ofNat (nat_lit 207360)), (nat_lit 514, Int.ofNat (nat_lit 115800)), (nat_lit 515, Int.ofNat (nat_lit 217344)), (nat_lit 523, Int.ofNat (nat_lit 58752)), (nat_lit 524, Int.ofNat (nat_lit 153600)), (nat_lit 525, Int.ofNat (nat_lit 209280)), (nat_lit 526, Int.ofNat (nat_lit 149760)), (nat_lit 527, Int.ofNat (nat_lit 204288)), (nat_lit 536, Int.ofNat (nat_lit 109440)), (nat_lit 537, Int.ofNat (nat_lit 210048)), (nat_lit 538, Int.ofNat (nat_lit 157608)), (nat_lit 539, Int.ofNat (nat_lit 241152)), (nat_lit 549, Int.ofNat (nat_lit 87552)), (nat_lit 550, Int.ofNat (nat_lit 150396)), (nat_lit 551, Int.ofNat (nat_lit 254208)), (nat_lit 562, Int.ofNat (nat_lit 41040)), (nat_lit 563, Int.ofNat (nat_lit 201786)), (nat_lit 575, Int.ofNat (nat_lit 152064)), (nat_lit 628, Int.ofNat (nat_lit 384)), (nat_lit 630, Int.ofNat (nat_lit 21696)), (nat_lit 632, Int.ofNat (nat_lit 5568)), (nat_lit 633, Int.ofNat (nat_lit 1152)), (nat_lit 635, Int.ofNat (nat_lit 6144)), (nat_lit 641, Int.ofNat (nat_lit 3840)), (nat_lit 642, Int.ofNat (nat_lit 28320)), (nat_lit 643, Int.ofNat (nat_lit 5760)), (nat_lit 644, Int.ofNat (nat_lit 28512)), (nat_lit 645, Int.ofNat (nat_lit 37488)), (nat_lit 646, Int.ofNat (nat_lit 48768)), (nat_lit 647, Int.ofNat (nat_lit 106344)), (nat_lit 654, Int.ofNat (nat_lit 48960)), (nat_lit 655, Int.ofNat (nat_lit 80064)), (nat_lit 656, Int.ofNat (nat_lit 153216)), (nat_lit 657, Int.ofNat (nat_lit 183168)), (nat_lit 658, Int.ofNat (nat_lit 102048)), (nat_lit 659, Int.ofNat (nat_lit 214656)), (nat_lit 667, Int.ofNat (nat_lit 38016))]
theorem block002_data_flat159_step : block002_data_flat159 = (CoefficientMerge.trim block002_data_flat158) := by decide +kernel
theorem block002_data_flat159_original : block002_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167040 : Int) atom0160Coded) (CoefficientMerge.scale (223104 : Int) atom0161Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231552 : Int) atom0162Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122400 : Int) atom0163Coded) (CoefficientMerge.scale (225744 : Int) atom0164Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79488 : Int) atom0165Coded) (CoefficientMerge.scale (181440 : Int) atom0166Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223488 : Int) atom0167Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150336 : Int) atom0168Coded) (CoefficientMerge.scale (195312 : Int) atom0169Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (119808 : Int) atom0170Coded) (CoefficientMerge.scale (214272 : Int) atom0171Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152160 : Int) atom0172Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213168 : Int) atom0173Coded) (CoefficientMerge.scale (84672 : Int) atom0174Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (135504 : Int) atom0175Coded) (CoefficientMerge.scale (208848 : Int) atom0176Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35712 : Int) atom0177Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808 : Int) atom0178Coded) (CoefficientMerge.scale (106704 : Int) atom0179Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4608 : Int) atom0180Coded) (CoefficientMerge.scale (36672 : Int) atom0181Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96 : Int) atom0182Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10656 : Int) atom0183Coded) (CoefficientMerge.scale (1584 : Int) atom0184Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1680 : Int) atom0185Coded) (CoefficientMerge.scale (2112 : Int) atom0186Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69696 : Int) atom0187Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20352 : Int) atom0188Coded) (CoefficientMerge.scale (53184 : Int) atom0189Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48288 : Int) atom0190Coded) (CoefficientMerge.scale (60528 : Int) atom0191Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86640 : Int) atom0192Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10368 : Int) atom0193Coded) (CoefficientMerge.scale (72960 : Int) atom0194Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46848 : Int) atom0195Coded) (CoefficientMerge.scale (83712 : Int) atom0196Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91392 : Int) atom0197Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102000 : Int) atom0198Coded) (CoefficientMerge.scale (154368 : Int) atom0199Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77184 : Int) atom0200Coded) (CoefficientMerge.scale (121344 : Int) atom0201Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (188160 : Int) atom0202Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207360 : Int) atom0203Coded) (CoefficientMerge.scale (115800 : Int) atom0204Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (217344 : Int) atom0205Coded) (CoefficientMerge.scale (58752 : Int) atom0206Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153600 : Int) atom0207Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209280 : Int) atom0208Coded) (CoefficientMerge.scale (149760 : Int) atom0209Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204288 : Int) atom0210Coded) (CoefficientMerge.scale (109440 : Int) atom0211Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210048 : Int) atom0212Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608 : Int) atom0213Coded) (CoefficientMerge.scale (241152 : Int) atom0214Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87552 : Int) atom0215Coded) (CoefficientMerge.scale (150396 : Int) atom0216Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254208 : Int) atom0217Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41040 : Int) atom0218Coded) (CoefficientMerge.scale (201786 : Int) atom0219Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152064 : Int) atom0220Coded) (CoefficientMerge.scale (384 : Int) atom0221Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21696 : Int) atom0222Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5568 : Int) atom0223Coded) (CoefficientMerge.scale (1152 : Int) atom0224Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6144 : Int) atom0225Coded) (CoefficientMerge.scale (3840 : Int) atom0226Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28320 : Int) atom0227Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5760 : Int) atom0228Coded) (CoefficientMerge.scale (28512 : Int) atom0229Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37488 : Int) atom0230Coded) (CoefficientMerge.scale (48768 : Int) atom0231Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (106344 : Int) atom0232Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48960 : Int) atom0233Coded) (CoefficientMerge.scale (80064 : Int) atom0234Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153216 : Int) atom0235Coded) (CoefficientMerge.scale (183168 : Int) atom0236Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102048 : Int) atom0237Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214656 : Int) atom0238Coded) (CoefficientMerge.scale (38016 : Int) atom0239Coded))))))))) := by
  rw [block002_data_flat159_step, block002_data_flat158_original]
theorem block002_data : block002 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167040 : Int) atom0160Coded) (CoefficientMerge.scale (223104 : Int) atom0161Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231552 : Int) atom0162Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122400 : Int) atom0163Coded) (CoefficientMerge.scale (225744 : Int) atom0164Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (79488 : Int) atom0165Coded) (CoefficientMerge.scale (181440 : Int) atom0166Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223488 : Int) atom0167Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150336 : Int) atom0168Coded) (CoefficientMerge.scale (195312 : Int) atom0169Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (119808 : Int) atom0170Coded) (CoefficientMerge.scale (214272 : Int) atom0171Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152160 : Int) atom0172Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213168 : Int) atom0173Coded) (CoefficientMerge.scale (84672 : Int) atom0174Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (135504 : Int) atom0175Coded) (CoefficientMerge.scale (208848 : Int) atom0176Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35712 : Int) atom0177Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808 : Int) atom0178Coded) (CoefficientMerge.scale (106704 : Int) atom0179Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4608 : Int) atom0180Coded) (CoefficientMerge.scale (36672 : Int) atom0181Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96 : Int) atom0182Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10656 : Int) atom0183Coded) (CoefficientMerge.scale (1584 : Int) atom0184Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1680 : Int) atom0185Coded) (CoefficientMerge.scale (2112 : Int) atom0186Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69696 : Int) atom0187Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20352 : Int) atom0188Coded) (CoefficientMerge.scale (53184 : Int) atom0189Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48288 : Int) atom0190Coded) (CoefficientMerge.scale (60528 : Int) atom0191Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86640 : Int) atom0192Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10368 : Int) atom0193Coded) (CoefficientMerge.scale (72960 : Int) atom0194Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46848 : Int) atom0195Coded) (CoefficientMerge.scale (83712 : Int) atom0196Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91392 : Int) atom0197Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102000 : Int) atom0198Coded) (CoefficientMerge.scale (154368 : Int) atom0199Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77184 : Int) atom0200Coded) (CoefficientMerge.scale (121344 : Int) atom0201Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (188160 : Int) atom0202Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207360 : Int) atom0203Coded) (CoefficientMerge.scale (115800 : Int) atom0204Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (217344 : Int) atom0205Coded) (CoefficientMerge.scale (58752 : Int) atom0206Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153600 : Int) atom0207Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209280 : Int) atom0208Coded) (CoefficientMerge.scale (149760 : Int) atom0209Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (204288 : Int) atom0210Coded) (CoefficientMerge.scale (109440 : Int) atom0211Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210048 : Int) atom0212Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157608 : Int) atom0213Coded) (CoefficientMerge.scale (241152 : Int) atom0214Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87552 : Int) atom0215Coded) (CoefficientMerge.scale (150396 : Int) atom0216Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254208 : Int) atom0217Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41040 : Int) atom0218Coded) (CoefficientMerge.scale (201786 : Int) atom0219Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (152064 : Int) atom0220Coded) (CoefficientMerge.scale (384 : Int) atom0221Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21696 : Int) atom0222Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5568 : Int) atom0223Coded) (CoefficientMerge.scale (1152 : Int) atom0224Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6144 : Int) atom0225Coded) (CoefficientMerge.scale (3840 : Int) atom0226Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28320 : Int) atom0227Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5760 : Int) atom0228Coded) (CoefficientMerge.scale (28512 : Int) atom0229Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37488 : Int) atom0230Coded) (CoefficientMerge.scale (48768 : Int) atom0231Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (106344 : Int) atom0232Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48960 : Int) atom0233Coded) (CoefficientMerge.scale (80064 : Int) atom0234Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153216 : Int) atom0235Coded) (CoefficientMerge.scale (183168 : Int) atom0236Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102048 : Int) atom0237Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214656 : Int) atom0238Coded) (CoefficientMerge.scale (38016 : Int) atom0239Coded)))))))) := by
  have h : block002 = block002_data_flat159 := by decide +kernel
  exact h.trans block002_data_flat159_original
theorem block002_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) block002 := by
  rw [block002_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0160Coded_nonneg g hg hA hB) (atom0161Coded_nonneg g hg hA hB)) (add_nonneg (atom0162Coded_nonneg g hg hA hB) (add_nonneg (atom0163Coded_nonneg g hg hA hB) (atom0164Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0165Coded_nonneg g hg hA hB) (atom0166Coded_nonneg g hg hA hB)) (add_nonneg (atom0167Coded_nonneg g hg hA hB) (add_nonneg (atom0168Coded_nonneg g hg hA hB) (atom0169Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0170Coded_nonneg g hg hA hB) (atom0171Coded_nonneg g hg hA hB)) (add_nonneg (atom0172Coded_nonneg g hg hA hB) (add_nonneg (atom0173Coded_nonneg g hg hA hB) (atom0174Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0175Coded_nonneg g hg hA hB) (atom0176Coded_nonneg g hg hA hB)) (add_nonneg (atom0177Coded_nonneg g hg hA hB) (add_nonneg (atom0178Coded_nonneg g hg hA hB) (atom0179Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0180Coded_nonneg g hg hA hB) (atom0181Coded_nonneg g hg hA hB)) (add_nonneg (atom0182Coded_nonneg g hg hA hB) (add_nonneg (atom0183Coded_nonneg g hg hA hB) (atom0184Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0185Coded_nonneg g hg hA hB) (atom0186Coded_nonneg g hg hA hB)) (add_nonneg (atom0187Coded_nonneg g hg hA hB) (add_nonneg (atom0188Coded_nonneg g hg hA hB) (atom0189Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0190Coded_nonneg g hg hA hB) (atom0191Coded_nonneg g hg hA hB)) (add_nonneg (atom0192Coded_nonneg g hg hA hB) (add_nonneg (atom0193Coded_nonneg g hg hA hB) (atom0194Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0195Coded_nonneg g hg hA hB) (atom0196Coded_nonneg g hg hA hB)) (add_nonneg (atom0197Coded_nonneg g hg hA hB) (add_nonneg (atom0198Coded_nonneg g hg hA hB) (atom0199Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0200Coded_nonneg g hg hA hB) (atom0201Coded_nonneg g hg hA hB)) (add_nonneg (atom0202Coded_nonneg g hg hA hB) (add_nonneg (atom0203Coded_nonneg g hg hA hB) (atom0204Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0205Coded_nonneg g hg hA hB) (atom0206Coded_nonneg g hg hA hB)) (add_nonneg (atom0207Coded_nonneg g hg hA hB) (add_nonneg (atom0208Coded_nonneg g hg hA hB) (atom0209Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0210Coded_nonneg g hg hA hB) (atom0211Coded_nonneg g hg hA hB)) (add_nonneg (atom0212Coded_nonneg g hg hA hB) (add_nonneg (atom0213Coded_nonneg g hg hA hB) (atom0214Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0215Coded_nonneg g hg hA hB) (atom0216Coded_nonneg g hg hA hB)) (add_nonneg (atom0217Coded_nonneg g hg hA hB) (add_nonneg (atom0218Coded_nonneg g hg hA hB) (atom0219Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0220Coded_nonneg g hg hA hB) (atom0221Coded_nonneg g hg hA hB)) (add_nonneg (atom0222Coded_nonneg g hg hA hB) (add_nonneg (atom0223Coded_nonneg g hg hA hB) (atom0224Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0225Coded_nonneg g hg hA hB) (atom0226Coded_nonneg g hg hA hB)) (add_nonneg (atom0227Coded_nonneg g hg hA hB) (add_nonneg (atom0228Coded_nonneg g hg hA hB) (atom0229Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0230Coded_nonneg g hg hA hB) (atom0231Coded_nonneg g hg hA hB)) (add_nonneg (atom0232Coded_nonneg g hg hA hB) (add_nonneg (atom0233Coded_nonneg g hg hA hB) (atom0234Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0235Coded_nonneg g hg hA hB) (atom0236Coded_nonneg g hg hA hB)) (add_nonneg (atom0237Coded_nonneg g hg hA hB) (add_nonneg (atom0238Coded_nonneg g hg hA hB) (atom0239Coded_nonneg g hg hA hB))))))))

end APPT.Finite12
