-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0233 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0233 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0233 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0233_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90512640 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0233Coded : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 1))]
theorem atom0233Coded_decode : atom0233 = SparsePolynomial.decodeCubic 15 atom0233Coded := by decide +kernel
theorem atom0233Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (90512640 : Int) atom0233Coded) := by
  have h := atom0233_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0233Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0234 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0234 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0234 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0234_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68604840 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234Coded : CoefficientMerge.Poly := [(nat_lit 325, Int.ofNat (nat_lit 1))]
theorem atom0234Coded_decode : atom0234 = SparsePolynomial.decodeCubic 15 atom0234Coded := by decide +kernel
theorem atom0234Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (68604840 : Int) atom0234Coded) := by
  have h := atom0234_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0234Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0235 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0235 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0235 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0235_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82191240 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235Coded : CoefficientMerge.Poly := [(nat_lit 326, Int.ofNat (nat_lit 1))]
theorem atom0235Coded_decode : atom0235 = SparsePolynomial.decodeCubic 15 atom0235Coded := by decide +kernel
theorem atom0235Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (82191240 : Int) atom0235Coded) := by
  have h := atom0235_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0235Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0236 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0236 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0236 = ((g 1) * (g 6) * (g 12)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0236_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91916280 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236Coded : CoefficientMerge.Poly := [(nat_lit 327, Int.ofNat (nat_lit 1))]
theorem atom0236Coded_decode : atom0236 = SparsePolynomial.decodeCubic 15 atom0236Coded := by decide +kernel
theorem atom0236Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (91916280 : Int) atom0236Coded) := by
  have h := atom0236_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0236Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0237 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0237 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0237 = ((g 1) * (g 6) * (g 13)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0237_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98458200 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237Coded : CoefficientMerge.Poly := [(nat_lit 328, Int.ofNat (nat_lit 1))]
theorem atom0237Coded_decode : atom0237 = SparsePolynomial.decodeCubic 15 atom0237Coded := by decide +kernel
theorem atom0237Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (98458200 : Int) atom0237Coded) := by
  have h := atom0237_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0237Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0238 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0238 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0238 = ((g 1) * (g 6) * (g 14)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0238_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105000120 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238Coded : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 1))]
theorem atom0238Coded_decode : atom0238 = SparsePolynomial.decodeCubic 15 atom0238Coded := by decide +kernel
theorem atom0238Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105000120 : Int) atom0238Coded) := by
  have h := atom0238_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0238Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0239 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0239 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0239 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0239_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34030080 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239Coded : CoefficientMerge.Poly := [(nat_lit 337, Int.ofNat (nat_lit 1))]
theorem atom0239Coded_decode : atom0239 = SparsePolynomial.decodeCubic 15 atom0239Coded := by decide +kernel
theorem atom0239Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (34030080 : Int) atom0239Coded) := by
  have h := atom0239_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0239Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0240 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0240 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0240 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0240_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61189760 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0240Coded : CoefficientMerge.Poly := [(nat_lit 338, Int.ofNat (nat_lit 1))]
theorem atom0240Coded_decode : atom0240 = SparsePolynomial.decodeCubic 15 atom0240Coded := by decide +kernel
theorem atom0240Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (61189760 : Int) atom0240Coded) := by
  have h := atom0240_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0240Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0241 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0241 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0241 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0241_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95363520 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241Coded : CoefficientMerge.Poly := [(nat_lit 339, Int.ofNat (nat_lit 1))]
theorem atom0241Coded_decode : atom0241 = SparsePolynomial.decodeCubic 15 atom0241Coded := by decide +kernel
theorem atom0241Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (95363520 : Int) atom0241Coded) := by
  have h := atom0241_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0241Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0242 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0242 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0242 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0242_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75650880 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242Coded : CoefficientMerge.Poly := [(nat_lit 340, Int.ofNat (nat_lit 1))]
theorem atom0242Coded_decode : atom0242 = SparsePolynomial.decodeCubic 15 atom0242Coded := by decide +kernel
theorem atom0242Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (75650880 : Int) atom0242Coded) := by
  have h := atom0242_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0242Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0243 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0243 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0243 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0243_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90831240 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243Coded : CoefficientMerge.Poly := [(nat_lit 341, Int.ofNat (nat_lit 1))]
theorem atom0243Coded_decode : atom0243 = SparsePolynomial.decodeCubic 15 atom0243Coded := by decide +kernel
theorem atom0243Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (90831240 : Int) atom0243Coded) := by
  have h := atom0243_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0243Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0244 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0244 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0244 = ((g 1) * (g 7) * (g 12)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0244_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98742720 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244Coded : CoefficientMerge.Poly := [(nat_lit 342, Int.ofNat (nat_lit 1))]
theorem atom0244Coded_decode : atom0244 = SparsePolynomial.decodeCubic 15 atom0244Coded := by decide +kernel
theorem atom0244Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (98742720 : Int) atom0244Coded) := by
  have h := atom0244_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0244Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0245 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0245 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0245 = ((g 1) * (g 7) * (g 13)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0245_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105417600 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245Coded : CoefficientMerge.Poly := [(nat_lit 343, Int.ofNat (nat_lit 1))]
theorem atom0245Coded_decode : atom0245 = SparsePolynomial.decodeCubic 15 atom0245Coded := by decide +kernel
theorem atom0245Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105417600 : Int) atom0245Coded) := by
  have h := atom0245_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0245Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0246 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0246 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0246 = ((g 1) * (g 7) * (g 14)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0246_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (112092480 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246Coded : CoefficientMerge.Poly := [(nat_lit 344, Int.ofNat (nat_lit 1))]
theorem atom0246Coded_decode : atom0246 = SparsePolynomial.decodeCubic 15 atom0246Coded := by decide +kernel
theorem atom0246Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (112092480 : Int) atom0246Coded) := by
  have h := atom0246_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0246Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0247 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0247 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0247 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0247_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42281280 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247Coded : CoefficientMerge.Poly := [(nat_lit 353, Int.ofNat (nat_lit 1))]
theorem atom0247Coded_decode : atom0247 = SparsePolynomial.decodeCubic 15 atom0247Coded := by decide +kernel
theorem atom0247Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (42281280 : Int) atom0247Coded) := by
  have h := atom0247_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0247Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0248 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0248 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0248 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0248_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105534000 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248Coded : CoefficientMerge.Poly := [(nat_lit 354, Int.ofNat (nat_lit 1))]
theorem atom0248Coded_decode : atom0248 = SparsePolynomial.decodeCubic 15 atom0248Coded := by decide +kernel
theorem atom0248Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105534000 : Int) atom0248Coded) := by
  have h := atom0248_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0248Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0249 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0249 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0249 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0249_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83431440 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249Coded : CoefficientMerge.Poly := [(nat_lit 355, Int.ofNat (nat_lit 1))]
theorem atom0249Coded_decode : atom0249 = SparsePolynomial.decodeCubic 15 atom0249Coded := by decide +kernel
theorem atom0249Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (83431440 : Int) atom0249Coded) := by
  have h := atom0249_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0249Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0250 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0250 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0250 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0250_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98601480 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250Coded : CoefficientMerge.Poly := [(nat_lit 356, Int.ofNat (nat_lit 1))]
theorem atom0250Coded_decode : atom0250 = SparsePolynomial.decodeCubic 15 atom0250Coded := by decide +kernel
theorem atom0250Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (98601480 : Int) atom0250Coded) := by
  have h := atom0250_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0250Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0251 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0251 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0251 = ((g 1) * (g 8) * (g 12)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0251_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105713280 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251Coded : CoefficientMerge.Poly := [(nat_lit 357, Int.ofNat (nat_lit 1))]
theorem atom0251Coded_decode : atom0251 = SparsePolynomial.decodeCubic 15 atom0251Coded := by decide +kernel
theorem atom0251Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105713280 : Int) atom0251Coded) := by
  have h := atom0251_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0251Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0252 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0252 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0252 = ((g 1) * (g 8) * (g 13)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0252_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105421680 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252Coded : CoefficientMerge.Poly := [(nat_lit 358, Int.ofNat (nat_lit 1))]
theorem atom0252Coded_decode : atom0252 = SparsePolynomial.decodeCubic 15 atom0252Coded := by decide +kernel
theorem atom0252Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105421680 : Int) atom0252Coded) := by
  have h := atom0252_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0252Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0253 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0253 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0253 = ((g 1) * (g 8) * (g 14)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0253_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123972480 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253Coded : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 1))]
theorem atom0253Coded_decode : atom0253 = SparsePolynomial.decodeCubic 15 atom0253Coded := by decide +kernel
theorem atom0253Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (123972480 : Int) atom0253Coded) := by
  have h := atom0253_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0253Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0254 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0254 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0254 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0254_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78278400 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254Coded : CoefficientMerge.Poly := [(nat_lit 369, Int.ofNat (nat_lit 1))]
theorem atom0254Coded_decode : atom0254 = SparsePolynomial.decodeCubic 15 atom0254Coded := by decide +kernel
theorem atom0254Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (78278400 : Int) atom0254Coded) := by
  have h := atom0254_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0254Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0255 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0255 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0255 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0255_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (124610400 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0255Coded : CoefficientMerge.Poly := [(nat_lit 370, Int.ofNat (nat_lit 1))]
theorem atom0255Coded_decode : atom0255 = SparsePolynomial.decodeCubic 15 atom0255Coded := by decide +kernel
theorem atom0255Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (124610400 : Int) atom0255Coded) := by
  have h := atom0255_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0255Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0256 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0256 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0256 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0256, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0256_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (162543240 : Int) atom0256) := by
  rw [SparsePolynomial.eval_scale, eval_atom0256]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0256Coded : CoefficientMerge.Poly := [(nat_lit 371, Int.ofNat (nat_lit 1))]
theorem atom0256Coded_decode : atom0256 = SparsePolynomial.decodeCubic 15 atom0256Coded := by decide +kernel
theorem atom0256Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (162543240 : Int) atom0256Coded) := by
  have h := atom0256_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0256Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0257 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0257 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0257 = ((g 1) * (g 9) * (g 12)) := by
  norm_num [atom0257, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0257_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171695520 : Int) atom0257) := by
  rw [SparsePolynomial.eval_scale, eval_atom0257]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0257Coded : CoefficientMerge.Poly := [(nat_lit 372, Int.ofNat (nat_lit 1))]
theorem atom0257Coded_decode : atom0257 = SparsePolynomial.decodeCubic 15 atom0257Coded := by decide +kernel
theorem atom0257Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (171695520 : Int) atom0257Coded) := by
  have h := atom0257_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0257Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0258 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0258 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0258 = ((g 1) * (g 9) * (g 13)) := by
  norm_num [atom0258, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0258_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110190240 : Int) atom0258) := by
  rw [SparsePolynomial.eval_scale, eval_atom0258]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0258Coded : CoefficientMerge.Poly := [(nat_lit 373, Int.ofNat (nat_lit 1))]
theorem atom0258Coded_decode : atom0258 = SparsePolynomial.decodeCubic 15 atom0258Coded := by decide +kernel
theorem atom0258Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (110190240 : Int) atom0258Coded) := by
  have h := atom0258_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0258Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0259 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0259 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0259 = ((g 1) * (g 9) * (g 14)) := by
  norm_num [atom0259, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0259_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132083640 : Int) atom0259) := by
  rw [SparsePolynomial.eval_scale, eval_atom0259]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0259Coded : CoefficientMerge.Poly := [(nat_lit 374, Int.ofNat (nat_lit 1))]
theorem atom0259Coded_decode : atom0259 = SparsePolynomial.decodeCubic 15 atom0259Coded := by decide +kernel
theorem atom0259Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (132083640 : Int) atom0259Coded) := by
  have h := atom0259_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0259Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0260 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0260 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0260 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0260, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0260_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50720688 : Int) atom0260) := by
  rw [SparsePolynomial.eval_scale, eval_atom0260]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0260Coded : CoefficientMerge.Poly := [(nat_lit 385, Int.ofNat (nat_lit 1))]
theorem atom0260Coded_decode : atom0260 = SparsePolynomial.decodeCubic 15 atom0260Coded := by decide +kernel
theorem atom0260Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (50720688 : Int) atom0260Coded) := by
  have h := atom0260_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0260Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0261 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0261 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0261 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0261, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0261_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119681280 : Int) atom0261) := by
  rw [SparsePolynomial.eval_scale, eval_atom0261]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0261Coded : CoefficientMerge.Poly := [(nat_lit 386, Int.ofNat (nat_lit 1))]
theorem atom0261Coded_decode : atom0261 = SparsePolynomial.decodeCubic 15 atom0261Coded := by decide +kernel
theorem atom0261Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (119681280 : Int) atom0261Coded) := by
  have h := atom0261_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0261Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0262 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0262 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0262 = ((g 1) * (g 10) * (g 12)) := by
  norm_num [atom0262, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0262_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (148644360 : Int) atom0262) := by
  rw [SparsePolynomial.eval_scale, eval_atom0262]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0262Coded : CoefficientMerge.Poly := [(nat_lit 387, Int.ofNat (nat_lit 1))]
theorem atom0262Coded_decode : atom0262 = SparsePolynomial.decodeCubic 15 atom0262Coded := by decide +kernel
theorem atom0262Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (148644360 : Int) atom0262Coded) := by
  have h := atom0262_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0262Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0263 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0263 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0263 = ((g 1) * (g 10) * (g 13)) := by
  norm_num [atom0263, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0263_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109284120 : Int) atom0263) := by
  rw [SparsePolynomial.eval_scale, eval_atom0263]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0263Coded : CoefficientMerge.Poly := [(nat_lit 388, Int.ofNat (nat_lit 1))]
theorem atom0263Coded_decode : atom0263 = SparsePolynomial.decodeCubic 15 atom0263Coded := by decide +kernel
theorem atom0263Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (109284120 : Int) atom0263Coded) := by
  have h := atom0263_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0263Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0264 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0264 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0264 = ((g 1) * (g 10) * (g 14)) := by
  norm_num [atom0264, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0264_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121793040 : Int) atom0264) := by
  rw [SparsePolynomial.eval_scale, eval_atom0264]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0264Coded : CoefficientMerge.Poly := [(nat_lit 389, Int.ofNat (nat_lit 1))]
theorem atom0264Coded_decode : atom0264 = SparsePolynomial.decodeCubic 15 atom0264Coded := by decide +kernel
theorem atom0264Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (121793040 : Int) atom0264Coded) := by
  have h := atom0264_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0264Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0265 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0265 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0265 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0265, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0265_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86289840 : Int) atom0265) := by
  rw [SparsePolynomial.eval_scale, eval_atom0265]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0265Coded : CoefficientMerge.Poly := [(nat_lit 401, Int.ofNat (nat_lit 1))]
theorem atom0265Coded_decode : atom0265 = SparsePolynomial.decodeCubic 15 atom0265Coded := by decide +kernel
theorem atom0265Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (86289840 : Int) atom0265Coded) := by
  have h := atom0265_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0265Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0266 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0266 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0266 = ((g 1) * (g 11) * (g 12)) := by
  norm_num [atom0266, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0266_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150873120 : Int) atom0266) := by
  rw [SparsePolynomial.eval_scale, eval_atom0266]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0266Coded : CoefficientMerge.Poly := [(nat_lit 402, Int.ofNat (nat_lit 1))]
theorem atom0266Coded_decode : atom0266 = SparsePolynomial.decodeCubic 15 atom0266Coded := by decide +kernel
theorem atom0266Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (150873120 : Int) atom0266Coded) := by
  have h := atom0266_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0266Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0267 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0267 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0267 = ((g 1) * (g 11) * (g 13)) := by
  norm_num [atom0267, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0267_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111926880 : Int) atom0267) := by
  rw [SparsePolynomial.eval_scale, eval_atom0267]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0267Coded : CoefficientMerge.Poly := [(nat_lit 403, Int.ofNat (nat_lit 1))]
theorem atom0267Coded_decode : atom0267 = SparsePolynomial.decodeCubic 15 atom0267Coded := by decide +kernel
theorem atom0267Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (111926880 : Int) atom0267Coded) := by
  have h := atom0267_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0267Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0268 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0268 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0268 = ((g 1) * (g 11) * (g 14)) := by
  norm_num [atom0268, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0268_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129163320 : Int) atom0268) := by
  rw [SparsePolynomial.eval_scale, eval_atom0268]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0268Coded : CoefficientMerge.Poly := [(nat_lit 404, Int.ofNat (nat_lit 1))]
theorem atom0268Coded_decode : atom0268 = SparsePolynomial.decodeCubic 15 atom0268Coded := by decide +kernel
theorem atom0268Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (129163320 : Int) atom0268Coded) := by
  have h := atom0268_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0268Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0269 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0269 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0269 = ((g 1) * (g 12) * (g 12)) := by
  norm_num [atom0269, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0269_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60586920 : Int) atom0269) := by
  rw [SparsePolynomial.eval_scale, eval_atom0269]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0269Coded : CoefficientMerge.Poly := [(nat_lit 417, Int.ofNat (nat_lit 1))]
theorem atom0269Coded_decode : atom0269 = SparsePolynomial.decodeCubic 15 atom0269Coded := by decide +kernel
theorem atom0269Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (60586920 : Int) atom0269Coded) := by
  have h := atom0269_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0269Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0270 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0270 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0270 = ((g 1) * (g 12) * (g 13)) := by
  norm_num [atom0270, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0270_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82651680 : Int) atom0270) := by
  rw [SparsePolynomial.eval_scale, eval_atom0270]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0270Coded : CoefficientMerge.Poly := [(nat_lit 418, Int.ofNat (nat_lit 1))]
theorem atom0270Coded_decode : atom0270 = SparsePolynomial.decodeCubic 15 atom0270Coded := by decide +kernel
theorem atom0270Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (82651680 : Int) atom0270Coded) := by
  have h := atom0270_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0270Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0271 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0271 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0271 = ((g 1) * (g 12) * (g 14)) := by
  norm_num [atom0271, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0271_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99339120 : Int) atom0271) := by
  rw [SparsePolynomial.eval_scale, eval_atom0271]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0271Coded : CoefficientMerge.Poly := [(nat_lit 419, Int.ofNat (nat_lit 1))]
theorem atom0271Coded_decode : atom0271 = SparsePolynomial.decodeCubic 15 atom0271Coded := by decide +kernel
theorem atom0271Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (99339120 : Int) atom0271Coded) := by
  have h := atom0271_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0271Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0272 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0272 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0272 = ((g 1) * (g 13) * (g 13)) := by
  norm_num [atom0272, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0272_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15121080 : Int) atom0272) := by
  rw [SparsePolynomial.eval_scale, eval_atom0272]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0272Coded : CoefficientMerge.Poly := [(nat_lit 433, Int.ofNat (nat_lit 1))]
theorem atom0272Coded_decode : atom0272 = SparsePolynomial.decodeCubic 15 atom0272Coded := by decide +kernel
theorem atom0272Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (15121080 : Int) atom0272Coded) := by
  have h := atom0272_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0272Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0273 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0273 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0273 = ((g 1) * (g 13) * (g 14)) := by
  norm_num [atom0273, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0273_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38720880 : Int) atom0273) := by
  rw [SparsePolynomial.eval_scale, eval_atom0273]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0273Coded : CoefficientMerge.Poly := [(nat_lit 434, Int.ofNat (nat_lit 1))]
theorem atom0273Coded_decode : atom0273 = SparsePolynomial.decodeCubic 15 atom0273Coded := by decide +kernel
theorem atom0273Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (38720880 : Int) atom0273Coded) := by
  have h := atom0273_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0273Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0274 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0274 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0274 = ((g 1) * (g 14) * (g 14)) := by
  norm_num [atom0274, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0274_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13514040 : Int) atom0274) := by
  rw [SparsePolynomial.eval_scale, eval_atom0274]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0274Coded : CoefficientMerge.Poly := [(nat_lit 449, Int.ofNat (nat_lit 1))]
theorem atom0274Coded_decode : atom0274 = SparsePolynomial.decodeCubic 15 atom0274Coded := by decide +kernel
theorem atom0274Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (13514040 : Int) atom0274Coded) := by
  have h := atom0274_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0274Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0275 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0275 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0275 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0275, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0275_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10108800 : Int) atom0275) := by
  rw [SparsePolynomial.eval_scale, eval_atom0275]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0275Coded : CoefficientMerge.Poly := [(nat_lit 482, Int.ofNat (nat_lit 1))]
theorem atom0275Coded_decode : atom0275 = SparsePolynomial.decodeCubic 15 atom0275Coded := by decide +kernel
theorem atom0275Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (10108800 : Int) atom0275Coded) := by
  have h := atom0275_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0275Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0276 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0276 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0276 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0276, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0276_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28200960 : Int) atom0276) := by
  rw [SparsePolynomial.eval_scale, eval_atom0276]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0276Coded : CoefficientMerge.Poly := [(nat_lit 483, Int.ofNat (nat_lit 1))]
theorem atom0276Coded_decode : atom0276 = SparsePolynomial.decodeCubic 15 atom0276Coded := by decide +kernel
theorem atom0276Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (28200960 : Int) atom0276Coded) := by
  have h := atom0276_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0276Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0277 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0277 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0277 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0277, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0277_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26075520 : Int) atom0277) := by
  rw [SparsePolynomial.eval_scale, eval_atom0277]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0277Coded : CoefficientMerge.Poly := [(nat_lit 484, Int.ofNat (nat_lit 1))]
theorem atom0277Coded_decode : atom0277 = SparsePolynomial.decodeCubic 15 atom0277Coded := by decide +kernel
theorem atom0277Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (26075520 : Int) atom0277Coded) := by
  have h := atom0277_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0277Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0278 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0278 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0278 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0278, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0278_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23950080 : Int) atom0278) := by
  rw [SparsePolynomial.eval_scale, eval_atom0278]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0278Coded : CoefficientMerge.Poly := [(nat_lit 485, Int.ofNat (nat_lit 1))]
theorem atom0278Coded_decode : atom0278 = SparsePolynomial.decodeCubic 15 atom0278Coded := by decide +kernel
theorem atom0278Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (23950080 : Int) atom0278Coded) := by
  have h := atom0278_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0278Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0279 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0279 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0279 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0279, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0279_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21824640 : Int) atom0279) := by
  rw [SparsePolynomial.eval_scale, eval_atom0279]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0279Coded : CoefficientMerge.Poly := [(nat_lit 486, Int.ofNat (nat_lit 1))]
theorem atom0279Coded_decode : atom0279 = SparsePolynomial.decodeCubic 15 atom0279Coded := by decide +kernel
theorem atom0279Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (21824640 : Int) atom0279Coded) := by
  have h := atom0279_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0279Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0280 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0280 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0280 = ((g 2) * (g 2) * (g 7)) := by
  norm_num [atom0280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0280_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19699200 : Int) atom0280) := by
  rw [SparsePolynomial.eval_scale, eval_atom0280]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0280Coded : CoefficientMerge.Poly := [(nat_lit 487, Int.ofNat (nat_lit 1))]
theorem atom0280Coded_decode : atom0280 = SparsePolynomial.decodeCubic 15 atom0280Coded := by decide +kernel
theorem atom0280Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (19699200 : Int) atom0280Coded) := by
  have h := atom0280_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0280Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0281 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0281 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0281 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0281, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0281_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17573760 : Int) atom0281) := by
  rw [SparsePolynomial.eval_scale, eval_atom0281]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0281Coded : CoefficientMerge.Poly := [(nat_lit 488, Int.ofNat (nat_lit 1))]
theorem atom0281Coded_decode : atom0281 = SparsePolynomial.decodeCubic 15 atom0281Coded := by decide +kernel
theorem atom0281Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (17573760 : Int) atom0281Coded) := by
  have h := atom0281_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0281Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0282 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0282 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0282 = ((g 2) * (g 2) * (g 9)) := by
  norm_num [atom0282, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0282_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42664320 : Int) atom0282) := by
  rw [SparsePolynomial.eval_scale, eval_atom0282]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0282Coded : CoefficientMerge.Poly := [(nat_lit 489, Int.ofNat (nat_lit 1))]
theorem atom0282Coded_decode : atom0282 = SparsePolynomial.decodeCubic 15 atom0282Coded := by decide +kernel
theorem atom0282Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (42664320 : Int) atom0282Coded) := by
  have h := atom0282_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0282Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0283 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0283 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0283 = ((g 2) * (g 2) * (g 10)) := by
  norm_num [atom0283, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0283_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13322880 : Int) atom0283) := by
  rw [SparsePolynomial.eval_scale, eval_atom0283]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0283Coded : CoefficientMerge.Poly := [(nat_lit 490, Int.ofNat (nat_lit 1))]
theorem atom0283Coded_decode : atom0283 = SparsePolynomial.decodeCubic 15 atom0283Coded := by decide +kernel
theorem atom0283Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (13322880 : Int) atom0283Coded) := by
  have h := atom0283_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0283Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0284 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0284 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0284 = ((g 2) * (g 2) * (g 11)) := by
  norm_num [atom0284, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0284_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23926320 : Int) atom0284) := by
  rw [SparsePolynomial.eval_scale, eval_atom0284]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0284Coded : CoefficientMerge.Poly := [(nat_lit 491, Int.ofNat (nat_lit 1))]
theorem atom0284Coded_decode : atom0284 = SparsePolynomial.decodeCubic 15 atom0284Coded := by decide +kernel
theorem atom0284Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (23926320 : Int) atom0284Coded) := by
  have h := atom0284_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0284Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0285 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0285 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0285 = ((g 2) * (g 2) * (g 12)) := by
  norm_num [atom0285, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0285_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9072000 : Int) atom0285) := by
  rw [SparsePolynomial.eval_scale, eval_atom0285]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0285Coded : CoefficientMerge.Poly := [(nat_lit 492, Int.ofNat (nat_lit 1))]
theorem atom0285Coded_decode : atom0285 = SparsePolynomial.decodeCubic 15 atom0285Coded := by decide +kernel
theorem atom0285Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (9072000 : Int) atom0285Coded) := by
  have h := atom0285_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0285Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0286 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0286 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0286 = ((g 2) * (g 2) * (g 14)) := by
  norm_num [atom0286, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0286_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13262400 : Int) atom0286) := by
  rw [SparsePolynomial.eval_scale, eval_atom0286]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0286Coded : CoefficientMerge.Poly := [(nat_lit 494, Int.ofNat (nat_lit 1))]
theorem atom0286Coded_decode : atom0286 = SparsePolynomial.decodeCubic 15 atom0286Coded := by decide +kernel
theorem atom0286Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (13262400 : Int) atom0286Coded) := by
  have h := atom0286_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0286Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0287 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0287 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0287 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0287, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0287_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21772800 : Int) atom0287) := by
  rw [SparsePolynomial.eval_scale, eval_atom0287]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0287Coded : CoefficientMerge.Poly := [(nat_lit 498, Int.ofNat (nat_lit 1))]
theorem atom0287Coded_decode : atom0287 = SparsePolynomial.decodeCubic 15 atom0287Coded := by decide +kernel
theorem atom0287Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (21772800 : Int) atom0287Coded) := by
  have h := atom0287_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0287Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0288 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0288 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0288 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0288, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0288_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40072320 : Int) atom0288) := by
  rw [SparsePolynomial.eval_scale, eval_atom0288]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0288Coded : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 1))]
theorem atom0288Coded_decode : atom0288 = SparsePolynomial.decodeCubic 15 atom0288Coded := by decide +kernel
theorem atom0288Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (40072320 : Int) atom0288Coded) := by
  have h := atom0288_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0288Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0289 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0289 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0289 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0289, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0289_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39398400 : Int) atom0289) := by
  rw [SparsePolynomial.eval_scale, eval_atom0289]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0289Coded : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 1))]
theorem atom0289Coded_decode : atom0289 = SparsePolynomial.decodeCubic 15 atom0289Coded := by decide +kernel
theorem atom0289Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (39398400 : Int) atom0289Coded) := by
  have h := atom0289_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0289Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0290 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0290 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0290 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0290, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0290_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38724480 : Int) atom0290) := by
  rw [SparsePolynomial.eval_scale, eval_atom0290]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0290Coded : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 1))]
theorem atom0290Coded_decode : atom0290 = SparsePolynomial.decodeCubic 15 atom0290Coded := by decide +kernel
theorem atom0290Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (38724480 : Int) atom0290Coded) := by
  have h := atom0290_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0290Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0291 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0291 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0291 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0291, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0291_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38499840 : Int) atom0291) := by
  rw [SparsePolynomial.eval_scale, eval_atom0291]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0291Coded : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 1))]
theorem atom0291Coded_decode : atom0291 = SparsePolynomial.decodeCubic 15 atom0291Coded := by decide +kernel
theorem atom0291Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (38499840 : Int) atom0291Coded) := by
  have h := atom0291_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0291Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0292 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0292 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0292 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0292, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0292_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38275200 : Int) atom0292) := by
  rw [SparsePolynomial.eval_scale, eval_atom0292]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0292Coded : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 1))]
theorem atom0292Coded_decode : atom0292 = SparsePolynomial.decodeCubic 15 atom0292Coded := by decide +kernel
theorem atom0292Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (38275200 : Int) atom0292Coded) := by
  have h := atom0292_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0292Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0293 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0293 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0293 = ((g 2) * (g 3) * (g 9)) := by
  norm_num [atom0293, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0293_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91134720 : Int) atom0293) := by
  rw [SparsePolynomial.eval_scale, eval_atom0293]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0293Coded : CoefficientMerge.Poly := [(nat_lit 504, Int.ofNat (nat_lit 1))]
theorem atom0293Coded_decode : atom0293 = SparsePolynomial.decodeCubic 15 atom0293Coded := by decide +kernel
theorem atom0293Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (91134720 : Int) atom0293Coded) := by
  have h := atom0293_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0293Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0294 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0294 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0294 = ((g 2) * (g 3) * (g 10)) := by
  norm_num [atom0294, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0294_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38350800 : Int) atom0294) := by
  rw [SparsePolynomial.eval_scale, eval_atom0294]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0294Coded : CoefficientMerge.Poly := [(nat_lit 505, Int.ofNat (nat_lit 1))]
theorem atom0294Coded_decode : atom0294 = SparsePolynomial.decodeCubic 15 atom0294Coded := by decide +kernel
theorem atom0294Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (38350800 : Int) atom0294Coded) := by
  have h := atom0294_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0294Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0295 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0295 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0295 = ((g 2) * (g 3) * (g 11)) := by
  norm_num [atom0295, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0295_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60812640 : Int) atom0295) := by
  rw [SparsePolynomial.eval_scale, eval_atom0295]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0295Coded : CoefficientMerge.Poly := [(nat_lit 506, Int.ofNat (nat_lit 1))]
theorem atom0295Coded_decode : atom0295 = SparsePolynomial.decodeCubic 15 atom0295Coded := by decide +kernel
theorem atom0295Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (60812640 : Int) atom0295Coded) := by
  have h := atom0295_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0295Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0296 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0296 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0296 = ((g 2) * (g 3) * (g 12)) := by
  norm_num [atom0296, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0296_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38951280 : Int) atom0296) := by
  rw [SparsePolynomial.eval_scale, eval_atom0296]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0296Coded : CoefficientMerge.Poly := [(nat_lit 507, Int.ofNat (nat_lit 1))]
theorem atom0296Coded_decode : atom0296 = SparsePolynomial.decodeCubic 15 atom0296Coded := by decide +kernel
theorem atom0296Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (38951280 : Int) atom0296Coded) := by
  have h := atom0296_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0296Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0297 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0297 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0297 = ((g 2) * (g 3) * (g 13)) := by
  norm_num [atom0297, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0297_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32479920 : Int) atom0297) := by
  rw [SparsePolynomial.eval_scale, eval_atom0297]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0297Coded : CoefficientMerge.Poly := [(nat_lit 508, Int.ofNat (nat_lit 1))]
theorem atom0297Coded_decode : atom0297 = SparsePolynomial.decodeCubic 15 atom0297Coded := by decide +kernel
theorem atom0297Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (32479920 : Int) atom0297Coded) := by
  have h := atom0297_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0297Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0298 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0298 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0298 = ((g 2) * (g 3) * (g 14)) := by
  norm_num [atom0298, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0298_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48342960 : Int) atom0298) := by
  rw [SparsePolynomial.eval_scale, eval_atom0298]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0298Coded : CoefficientMerge.Poly := [(nat_lit 509, Int.ofNat (nat_lit 1))]
theorem atom0298Coded_decode : atom0298 = SparsePolynomial.decodeCubic 15 atom0298Coded := by decide +kernel
theorem atom0298Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (48342960 : Int) atom0298Coded) := by
  have h := atom0298_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0298Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0299 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0299 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0299 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0299, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0299_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27296640 : Int) atom0299) := by
  rw [SparsePolynomial.eval_scale, eval_atom0299]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0299Coded : CoefficientMerge.Poly := [(nat_lit 514, Int.ofNat (nat_lit 1))]
theorem atom0299Coded_decode : atom0299 = SparsePolynomial.decodeCubic 15 atom0299Coded := by decide +kernel
theorem atom0299Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (27296640 : Int) atom0299Coded) := by
  have h := atom0299_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0299Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0300 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0300 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0300 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0300, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0300_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46281600 : Int) atom0300) := by
  rw [SparsePolynomial.eval_scale, eval_atom0300]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0300Coded : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 1))]
theorem atom0300Coded_decode : atom0300 = SparsePolynomial.decodeCubic 15 atom0300Coded := by decide +kernel
theorem atom0300Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (46281600 : Int) atom0300Coded) := by
  have h := atom0300_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0300Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0301 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0301 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0301 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0301, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0301_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46765440 : Int) atom0301) := by
  rw [SparsePolynomial.eval_scale, eval_atom0301]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0301Coded : CoefficientMerge.Poly := [(nat_lit 516, Int.ofNat (nat_lit 1))]
theorem atom0301Coded_decode : atom0301 = SparsePolynomial.decodeCubic 15 atom0301Coded := by decide +kernel
theorem atom0301Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (46765440 : Int) atom0301Coded) := by
  have h := atom0301_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0301Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0302 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0302 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0302 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0302, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0302_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47249280 : Int) atom0302) := by
  rw [SparsePolynomial.eval_scale, eval_atom0302]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0302Coded : CoefficientMerge.Poly := [(nat_lit 517, Int.ofNat (nat_lit 1))]
theorem atom0302Coded_decode : atom0302 = SparsePolynomial.decodeCubic 15 atom0302Coded := by decide +kernel
theorem atom0302Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (47249280 : Int) atom0302Coded) := by
  have h := atom0302_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0302Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0303 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0303 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0303 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0303, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0303_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47733120 : Int) atom0303) := by
  rw [SparsePolynomial.eval_scale, eval_atom0303]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0303Coded : CoefficientMerge.Poly := [(nat_lit 518, Int.ofNat (nat_lit 1))]
theorem atom0303Coded_decode : atom0303 = SparsePolynomial.decodeCubic 15 atom0303Coded := by decide +kernel
theorem atom0303Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (47733120 : Int) atom0303Coded) := by
  have h := atom0303_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0303Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0304 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0304 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0304 = ((g 2) * (g 4) * (g 9)) := by
  norm_num [atom0304, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0304_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96940800 : Int) atom0304) := by
  rw [SparsePolynomial.eval_scale, eval_atom0304]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0304Coded : CoefficientMerge.Poly := [(nat_lit 519, Int.ofNat (nat_lit 1))]
theorem atom0304Coded_decode : atom0304 = SparsePolynomial.decodeCubic 15 atom0304Coded := by decide +kernel
theorem atom0304Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (96940800 : Int) atom0304Coded) := by
  have h := atom0304_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0304Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0305 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0305 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0305 = ((g 2) * (g 4) * (g 10)) := by
  norm_num [atom0305, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0305_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53688240 : Int) atom0305) := by
  rw [SparsePolynomial.eval_scale, eval_atom0305]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0305Coded : CoefficientMerge.Poly := [(nat_lit 520, Int.ofNat (nat_lit 1))]
theorem atom0305Coded_decode : atom0305 = SparsePolynomial.decodeCubic 15 atom0305Coded := by decide +kernel
theorem atom0305Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (53688240 : Int) atom0305Coded) := by
  have h := atom0305_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0305Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0306 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0306 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0306 = ((g 2) * (g 4) * (g 11)) := by
  norm_num [atom0306, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0306_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73772640 : Int) atom0306) := by
  rw [SparsePolynomial.eval_scale, eval_atom0306]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0306Coded : CoefficientMerge.Poly := [(nat_lit 521, Int.ofNat (nat_lit 1))]
theorem atom0306Coded_decode : atom0306 = SparsePolynomial.decodeCubic 15 atom0306Coded := by decide +kernel
theorem atom0306Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (73772640 : Int) atom0306Coded) := by
  have h := atom0306_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0306Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0307 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0307 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0307 = ((g 2) * (g 4) * (g 12)) := by
  norm_num [atom0307, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0307_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64630800 : Int) atom0307) := by
  rw [SparsePolynomial.eval_scale, eval_atom0307]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0307Coded : CoefficientMerge.Poly := [(nat_lit 522, Int.ofNat (nat_lit 1))]
theorem atom0307Coded_decode : atom0307 = SparsePolynomial.decodeCubic 15 atom0307Coded := by decide +kernel
theorem atom0307Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (64630800 : Int) atom0307Coded) := by
  have h := atom0307_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0307Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0308 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0308 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0308 = ((g 2) * (g 4) * (g 13)) := by
  norm_num [atom0308, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0308_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64818000 : Int) atom0308) := by
  rw [SparsePolynomial.eval_scale, eval_atom0308]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0308Coded : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 1))]
theorem atom0308Coded_decode : atom0308 = SparsePolynomial.decodeCubic 15 atom0308Coded := by decide +kernel
theorem atom0308Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (64818000 : Int) atom0308Coded) := by
  have h := atom0308_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0308Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0309 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0309 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0309 = ((g 2) * (g 4) * (g 14)) := by
  norm_num [atom0309, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0309_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87339600 : Int) atom0309) := by
  rw [SparsePolynomial.eval_scale, eval_atom0309]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0309Coded : CoefficientMerge.Poly := [(nat_lit 524, Int.ofNat (nat_lit 1))]
theorem atom0309Coded_decode : atom0309 = SparsePolynomial.decodeCubic 15 atom0309Coded := by decide +kernel
theorem atom0309Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (87339600 : Int) atom0309Coded) := by
  have h := atom0309_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0309Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0310 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0310 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0310 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0310, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0310_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31582080 : Int) atom0310) := by
  rw [SparsePolynomial.eval_scale, eval_atom0310]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0310Coded : CoefficientMerge.Poly := [(nat_lit 530, Int.ofNat (nat_lit 1))]
theorem atom0310Coded_decode : atom0310 = SparsePolynomial.decodeCubic 15 atom0310Coded := by decide +kernel
theorem atom0310Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (31582080 : Int) atom0310Coded) := by
  have h := atom0310_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0310Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0311 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0311 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0311 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0311, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0311_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61263360 : Int) atom0311) := by
  rw [SparsePolynomial.eval_scale, eval_atom0311]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0311Coded : CoefficientMerge.Poly := [(nat_lit 531, Int.ofNat (nat_lit 1))]
theorem atom0311Coded_decode : atom0311 = SparsePolynomial.decodeCubic 15 atom0311Coded := by decide +kernel
theorem atom0311Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (61263360 : Int) atom0311Coded) := by
  have h := atom0311_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0311Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0312 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0312 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0312 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0312, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0312_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61263360 : Int) atom0312) := by
  rw [SparsePolynomial.eval_scale, eval_atom0312]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0312Coded : CoefficientMerge.Poly := [(nat_lit 532, Int.ofNat (nat_lit 1))]
theorem atom0312Coded_decode : atom0312 = SparsePolynomial.decodeCubic 15 atom0312Coded := by decide +kernel
theorem atom0312Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (61263360 : Int) atom0312Coded) := by
  have h := atom0312_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0312Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block003 : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 90512640)), (nat_lit 325, Int.ofNat (nat_lit 68604840)), (nat_lit 326, Int.ofNat (nat_lit 82191240)), (nat_lit 327, Int.ofNat (nat_lit 91916280)), (nat_lit 328, Int.ofNat (nat_lit 98458200)), (nat_lit 329, Int.ofNat (nat_lit 105000120)), (nat_lit 337, Int.ofNat (nat_lit 34030080)), (nat_lit 338, Int.ofNat (nat_lit 61189760)), (nat_lit 339, Int.ofNat (nat_lit 95363520)), (nat_lit 340, Int.ofNat (nat_lit 75650880)), (nat_lit 341, Int.ofNat (nat_lit 90831240)), (nat_lit 342, Int.ofNat (nat_lit 98742720)), (nat_lit 343, Int.ofNat (nat_lit 105417600)), (nat_lit 344, Int.ofNat (nat_lit 112092480)), (nat_lit 353, Int.ofNat (nat_lit 42281280)), (nat_lit 354, Int.ofNat (nat_lit 105534000)), (nat_lit 355, Int.ofNat (nat_lit 83431440)), (nat_lit 356, Int.ofNat (nat_lit 98601480)), (nat_lit 357, Int.ofNat (nat_lit 105713280)), (nat_lit 358, Int.ofNat (nat_lit 105421680)), (nat_lit 359, Int.ofNat (nat_lit 123972480)), (nat_lit 369, Int.ofNat (nat_lit 78278400)), (nat_lit 370, Int.ofNat (nat_lit 124610400)), (nat_lit 371, Int.ofNat (nat_lit 162543240)), (nat_lit 372, Int.ofNat (nat_lit 171695520)), (nat_lit 373, Int.ofNat (nat_lit 110190240)), (nat_lit 374, Int.ofNat (nat_lit 132083640)), (nat_lit 385, Int.ofNat (nat_lit 50720688)), (nat_lit 386, Int.ofNat (nat_lit 119681280)), (nat_lit 387, Int.ofNat (nat_lit 148644360)), (nat_lit 388, Int.ofNat (nat_lit 109284120)), (nat_lit 389, Int.ofNat (nat_lit 121793040)), (nat_lit 401, Int.ofNat (nat_lit 86289840)), (nat_lit 402, Int.ofNat (nat_lit 150873120)), (nat_lit 403, Int.ofNat (nat_lit 111926880)), (nat_lit 404, Int.ofNat (nat_lit 129163320)), (nat_lit 417, Int.ofNat (nat_lit 60586920)), (nat_lit 418, Int.ofNat (nat_lit 82651680)), (nat_lit 419, Int.ofNat (nat_lit 99339120)), (nat_lit 433, Int.ofNat (nat_lit 15121080)), (nat_lit 434, Int.ofNat (nat_lit 38720880)), (nat_lit 449, Int.ofNat (nat_lit 13514040)), (nat_lit 482, Int.ofNat (nat_lit 10108800)), (nat_lit 483, Int.ofNat (nat_lit 28200960)), (nat_lit 484, Int.ofNat (nat_lit 26075520)), (nat_lit 485, Int.ofNat (nat_lit 23950080)), (nat_lit 486, Int.ofNat (nat_lit 21824640)), (nat_lit 487, Int.ofNat (nat_lit 19699200)), (nat_lit 488, Int.ofNat (nat_lit 17573760)), (nat_lit 489, Int.ofNat (nat_lit 42664320)), (nat_lit 490, Int.ofNat (nat_lit 13322880)), (nat_lit 491, Int.ofNat (nat_lit 23926320)), (nat_lit 492, Int.ofNat (nat_lit 9072000)), (nat_lit 494, Int.ofNat (nat_lit 13262400)), (nat_lit 498, Int.ofNat (nat_lit 21772800)), (nat_lit 499, Int.ofNat (nat_lit 40072320)), (nat_lit 500, Int.ofNat (nat_lit 39398400)), (nat_lit 501, Int.ofNat (nat_lit 38724480)), (nat_lit 502, Int.ofNat (nat_lit 38499840)), (nat_lit 503, Int.ofNat (nat_lit 38275200)), (nat_lit 504, Int.ofNat (nat_lit 91134720)), (nat_lit 505, Int.ofNat (nat_lit 38350800)), (nat_lit 506, Int.ofNat (nat_lit 60812640)), (nat_lit 507, Int.ofNat (nat_lit 38951280)), (nat_lit 508, Int.ofNat (nat_lit 32479920)), (nat_lit 509, Int.ofNat (nat_lit 48342960)), (nat_lit 514, Int.ofNat (nat_lit 27296640)), (nat_lit 515, Int.ofNat (nat_lit 46281600)), (nat_lit 516, Int.ofNat (nat_lit 46765440)), (nat_lit 517, Int.ofNat (nat_lit 47249280)), (nat_lit 518, Int.ofNat (nat_lit 47733120)), (nat_lit 519, Int.ofNat (nat_lit 96940800)), (nat_lit 520, Int.ofNat (nat_lit 53688240)), (nat_lit 521, Int.ofNat (nat_lit 73772640)), (nat_lit 522, Int.ofNat (nat_lit 64630800)), (nat_lit 523, Int.ofNat (nat_lit 64818000)), (nat_lit 524, Int.ofNat (nat_lit 87339600)), (nat_lit 530, Int.ofNat (nat_lit 31582080)), (nat_lit 531, Int.ofNat (nat_lit 61263360)), (nat_lit 532, Int.ofNat (nat_lit 61263360))]
def block003_data_flat000 : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 90512640))]
theorem block003_data_flat000_step : block003_data_flat000 = (CoefficientMerge.scale (90512640 : Int) atom0233Coded) := by decide +kernel
theorem block003_data_flat000_original : block003_data_flat000 = (CoefficientMerge.scale (90512640 : Int) atom0233Coded) := by
  rw [block003_data_flat000_step]
def block003_data_flat001 : CoefficientMerge.Poly := [(nat_lit 325, Int.ofNat (nat_lit 68604840))]
theorem block003_data_flat001_step : block003_data_flat001 = (CoefficientMerge.scale (68604840 : Int) atom0234Coded) := by decide +kernel
theorem block003_data_flat001_original : block003_data_flat001 = (CoefficientMerge.scale (68604840 : Int) atom0234Coded) := by
  rw [block003_data_flat001_step]
def block003_data_flat002 : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 90512640)), (nat_lit 325, Int.ofNat (nat_lit 68604840))]
theorem block003_data_flat002_step : block003_data_flat002 = (CoefficientMerge.fastMerge block003_data_flat000 block003_data_flat001) := by decide +kernel
theorem block003_data_flat002_original : block003_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (90512640 : Int) atom0233Coded) (CoefficientMerge.scale (68604840 : Int) atom0234Coded)) := by
  rw [block003_data_flat002_step, block003_data_flat000_original, block003_data_flat001_original]
def block003_data_flat003 : CoefficientMerge.Poly := [(nat_lit 326, Int.ofNat (nat_lit 82191240))]
theorem block003_data_flat003_step : block003_data_flat003 = (CoefficientMerge.scale (82191240 : Int) atom0235Coded) := by decide +kernel
theorem block003_data_flat003_original : block003_data_flat003 = (CoefficientMerge.scale (82191240 : Int) atom0235Coded) := by
  rw [block003_data_flat003_step]
def block003_data_flat004 : CoefficientMerge.Poly := [(nat_lit 327, Int.ofNat (nat_lit 91916280))]
theorem block003_data_flat004_step : block003_data_flat004 = (CoefficientMerge.scale (91916280 : Int) atom0236Coded) := by decide +kernel
theorem block003_data_flat004_original : block003_data_flat004 = (CoefficientMerge.scale (91916280 : Int) atom0236Coded) := by
  rw [block003_data_flat004_step]
def block003_data_flat005 : CoefficientMerge.Poly := [(nat_lit 328, Int.ofNat (nat_lit 98458200))]
theorem block003_data_flat005_step : block003_data_flat005 = (CoefficientMerge.scale (98458200 : Int) atom0237Coded) := by decide +kernel
theorem block003_data_flat005_original : block003_data_flat005 = (CoefficientMerge.scale (98458200 : Int) atom0237Coded) := by
  rw [block003_data_flat005_step]
def block003_data_flat006 : CoefficientMerge.Poly := [(nat_lit 327, Int.ofNat (nat_lit 91916280)), (nat_lit 328, Int.ofNat (nat_lit 98458200))]
theorem block003_data_flat006_step : block003_data_flat006 = (CoefficientMerge.fastMerge block003_data_flat004 block003_data_flat005) := by decide +kernel
theorem block003_data_flat006_original : block003_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (91916280 : Int) atom0236Coded) (CoefficientMerge.scale (98458200 : Int) atom0237Coded)) := by
  rw [block003_data_flat006_step, block003_data_flat004_original, block003_data_flat005_original]
def block003_data_flat007 : CoefficientMerge.Poly := [(nat_lit 326, Int.ofNat (nat_lit 82191240)), (nat_lit 327, Int.ofNat (nat_lit 91916280)), (nat_lit 328, Int.ofNat (nat_lit 98458200))]
theorem block003_data_flat007_step : block003_data_flat007 = (CoefficientMerge.fastMerge block003_data_flat003 block003_data_flat006) := by decide +kernel
theorem block003_data_flat007_original : block003_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82191240 : Int) atom0235Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91916280 : Int) atom0236Coded) (CoefficientMerge.scale (98458200 : Int) atom0237Coded))) := by
  rw [block003_data_flat007_step, block003_data_flat003_original, block003_data_flat006_original]
def block003_data_flat008 : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 90512640)), (nat_lit 325, Int.ofNat (nat_lit 68604840)), (nat_lit 326, Int.ofNat (nat_lit 82191240)), (nat_lit 327, Int.ofNat (nat_lit 91916280)), (nat_lit 328, Int.ofNat (nat_lit 98458200))]
theorem block003_data_flat008_step : block003_data_flat008 = (CoefficientMerge.fastMerge block003_data_flat002 block003_data_flat007) := by decide +kernel
theorem block003_data_flat008_original : block003_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90512640 : Int) atom0233Coded) (CoefficientMerge.scale (68604840 : Int) atom0234Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82191240 : Int) atom0235Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91916280 : Int) atom0236Coded) (CoefficientMerge.scale (98458200 : Int) atom0237Coded)))) := by
  rw [block003_data_flat008_step, block003_data_flat002_original, block003_data_flat007_original]
def block003_data_flat009 : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 105000120))]
theorem block003_data_flat009_step : block003_data_flat009 = (CoefficientMerge.scale (105000120 : Int) atom0238Coded) := by decide +kernel
theorem block003_data_flat009_original : block003_data_flat009 = (CoefficientMerge.scale (105000120 : Int) atom0238Coded) := by
  rw [block003_data_flat009_step]
def block003_data_flat010 : CoefficientMerge.Poly := [(nat_lit 337, Int.ofNat (nat_lit 34030080))]
theorem block003_data_flat010_step : block003_data_flat010 = (CoefficientMerge.scale (34030080 : Int) atom0239Coded) := by decide +kernel
theorem block003_data_flat010_original : block003_data_flat010 = (CoefficientMerge.scale (34030080 : Int) atom0239Coded) := by
  rw [block003_data_flat010_step]
def block003_data_flat011 : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 105000120)), (nat_lit 337, Int.ofNat (nat_lit 34030080))]
theorem block003_data_flat011_step : block003_data_flat011 = (CoefficientMerge.fastMerge block003_data_flat009 block003_data_flat010) := by decide +kernel
theorem block003_data_flat011_original : block003_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (105000120 : Int) atom0238Coded) (CoefficientMerge.scale (34030080 : Int) atom0239Coded)) := by
  rw [block003_data_flat011_step, block003_data_flat009_original, block003_data_flat010_original]
def block003_data_flat012 : CoefficientMerge.Poly := [(nat_lit 338, Int.ofNat (nat_lit 61189760))]
theorem block003_data_flat012_step : block003_data_flat012 = (CoefficientMerge.scale (61189760 : Int) atom0240Coded) := by decide +kernel
theorem block003_data_flat012_original : block003_data_flat012 = (CoefficientMerge.scale (61189760 : Int) atom0240Coded) := by
  rw [block003_data_flat012_step]
def block003_data_flat013 : CoefficientMerge.Poly := [(nat_lit 339, Int.ofNat (nat_lit 95363520))]
theorem block003_data_flat013_step : block003_data_flat013 = (CoefficientMerge.scale (95363520 : Int) atom0241Coded) := by decide +kernel
theorem block003_data_flat013_original : block003_data_flat013 = (CoefficientMerge.scale (95363520 : Int) atom0241Coded) := by
  rw [block003_data_flat013_step]
def block003_data_flat014 : CoefficientMerge.Poly := [(nat_lit 340, Int.ofNat (nat_lit 75650880))]
theorem block003_data_flat014_step : block003_data_flat014 = (CoefficientMerge.scale (75650880 : Int) atom0242Coded) := by decide +kernel
theorem block003_data_flat014_original : block003_data_flat014 = (CoefficientMerge.scale (75650880 : Int) atom0242Coded) := by
  rw [block003_data_flat014_step]
def block003_data_flat015 : CoefficientMerge.Poly := [(nat_lit 339, Int.ofNat (nat_lit 95363520)), (nat_lit 340, Int.ofNat (nat_lit 75650880))]
theorem block003_data_flat015_step : block003_data_flat015 = (CoefficientMerge.fastMerge block003_data_flat013 block003_data_flat014) := by decide +kernel
theorem block003_data_flat015_original : block003_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (95363520 : Int) atom0241Coded) (CoefficientMerge.scale (75650880 : Int) atom0242Coded)) := by
  rw [block003_data_flat015_step, block003_data_flat013_original, block003_data_flat014_original]
def block003_data_flat016 : CoefficientMerge.Poly := [(nat_lit 338, Int.ofNat (nat_lit 61189760)), (nat_lit 339, Int.ofNat (nat_lit 95363520)), (nat_lit 340, Int.ofNat (nat_lit 75650880))]
theorem block003_data_flat016_step : block003_data_flat016 = (CoefficientMerge.fastMerge block003_data_flat012 block003_data_flat015) := by decide +kernel
theorem block003_data_flat016_original : block003_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61189760 : Int) atom0240Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (95363520 : Int) atom0241Coded) (CoefficientMerge.scale (75650880 : Int) atom0242Coded))) := by
  rw [block003_data_flat016_step, block003_data_flat012_original, block003_data_flat015_original]
def block003_data_flat017 : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 105000120)), (nat_lit 337, Int.ofNat (nat_lit 34030080)), (nat_lit 338, Int.ofNat (nat_lit 61189760)), (nat_lit 339, Int.ofNat (nat_lit 95363520)), (nat_lit 340, Int.ofNat (nat_lit 75650880))]
theorem block003_data_flat017_step : block003_data_flat017 = (CoefficientMerge.fastMerge block003_data_flat011 block003_data_flat016) := by decide +kernel
theorem block003_data_flat017_original : block003_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105000120 : Int) atom0238Coded) (CoefficientMerge.scale (34030080 : Int) atom0239Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61189760 : Int) atom0240Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (95363520 : Int) atom0241Coded) (CoefficientMerge.scale (75650880 : Int) atom0242Coded)))) := by
  rw [block003_data_flat017_step, block003_data_flat011_original, block003_data_flat016_original]
def block003_data_flat018 : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 90512640)), (nat_lit 325, Int.ofNat (nat_lit 68604840)), (nat_lit 326, Int.ofNat (nat_lit 82191240)), (nat_lit 327, Int.ofNat (nat_lit 91916280)), (nat_lit 328, Int.ofNat (nat_lit 98458200)), (nat_lit 329, Int.ofNat (nat_lit 105000120)), (nat_lit 337, Int.ofNat (nat_lit 34030080)), (nat_lit 338, Int.ofNat (nat_lit 61189760)), (nat_lit 339, Int.ofNat (nat_lit 95363520)), (nat_lit 340, Int.ofNat (nat_lit 75650880))]
theorem block003_data_flat018_step : block003_data_flat018 = (CoefficientMerge.fastMerge block003_data_flat008 block003_data_flat017) := by decide +kernel
theorem block003_data_flat018_original : block003_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90512640 : Int) atom0233Coded) (CoefficientMerge.scale (68604840 : Int) atom0234Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82191240 : Int) atom0235Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91916280 : Int) atom0236Coded) (CoefficientMerge.scale (98458200 : Int) atom0237Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105000120 : Int) atom0238Coded) (CoefficientMerge.scale (34030080 : Int) atom0239Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61189760 : Int) atom0240Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (95363520 : Int) atom0241Coded) (CoefficientMerge.scale (75650880 : Int) atom0242Coded))))) := by
  rw [block003_data_flat018_step, block003_data_flat008_original, block003_data_flat017_original]
def block003_data_flat019 : CoefficientMerge.Poly := [(nat_lit 341, Int.ofNat (nat_lit 90831240))]
theorem block003_data_flat019_step : block003_data_flat019 = (CoefficientMerge.scale (90831240 : Int) atom0243Coded) := by decide +kernel
theorem block003_data_flat019_original : block003_data_flat019 = (CoefficientMerge.scale (90831240 : Int) atom0243Coded) := by
  rw [block003_data_flat019_step]
def block003_data_flat020 : CoefficientMerge.Poly := [(nat_lit 342, Int.ofNat (nat_lit 98742720))]
theorem block003_data_flat020_step : block003_data_flat020 = (CoefficientMerge.scale (98742720 : Int) atom0244Coded) := by decide +kernel
theorem block003_data_flat020_original : block003_data_flat020 = (CoefficientMerge.scale (98742720 : Int) atom0244Coded) := by
  rw [block003_data_flat020_step]
def block003_data_flat021 : CoefficientMerge.Poly := [(nat_lit 341, Int.ofNat (nat_lit 90831240)), (nat_lit 342, Int.ofNat (nat_lit 98742720))]
theorem block003_data_flat021_step : block003_data_flat021 = (CoefficientMerge.fastMerge block003_data_flat019 block003_data_flat020) := by decide +kernel
theorem block003_data_flat021_original : block003_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (90831240 : Int) atom0243Coded) (CoefficientMerge.scale (98742720 : Int) atom0244Coded)) := by
  rw [block003_data_flat021_step, block003_data_flat019_original, block003_data_flat020_original]
def block003_data_flat022 : CoefficientMerge.Poly := [(nat_lit 343, Int.ofNat (nat_lit 105417600))]
theorem block003_data_flat022_step : block003_data_flat022 = (CoefficientMerge.scale (105417600 : Int) atom0245Coded) := by decide +kernel
theorem block003_data_flat022_original : block003_data_flat022 = (CoefficientMerge.scale (105417600 : Int) atom0245Coded) := by
  rw [block003_data_flat022_step]
def block003_data_flat023 : CoefficientMerge.Poly := [(nat_lit 344, Int.ofNat (nat_lit 112092480))]
theorem block003_data_flat023_step : block003_data_flat023 = (CoefficientMerge.scale (112092480 : Int) atom0246Coded) := by decide +kernel
theorem block003_data_flat023_original : block003_data_flat023 = (CoefficientMerge.scale (112092480 : Int) atom0246Coded) := by
  rw [block003_data_flat023_step]
def block003_data_flat024 : CoefficientMerge.Poly := [(nat_lit 353, Int.ofNat (nat_lit 42281280))]
theorem block003_data_flat024_step : block003_data_flat024 = (CoefficientMerge.scale (42281280 : Int) atom0247Coded) := by decide +kernel
theorem block003_data_flat024_original : block003_data_flat024 = (CoefficientMerge.scale (42281280 : Int) atom0247Coded) := by
  rw [block003_data_flat024_step]
def block003_data_flat025 : CoefficientMerge.Poly := [(nat_lit 344, Int.ofNat (nat_lit 112092480)), (nat_lit 353, Int.ofNat (nat_lit 42281280))]
theorem block003_data_flat025_step : block003_data_flat025 = (CoefficientMerge.fastMerge block003_data_flat023 block003_data_flat024) := by decide +kernel
theorem block003_data_flat025_original : block003_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (112092480 : Int) atom0246Coded) (CoefficientMerge.scale (42281280 : Int) atom0247Coded)) := by
  rw [block003_data_flat025_step, block003_data_flat023_original, block003_data_flat024_original]
def block003_data_flat026 : CoefficientMerge.Poly := [(nat_lit 343, Int.ofNat (nat_lit 105417600)), (nat_lit 344, Int.ofNat (nat_lit 112092480)), (nat_lit 353, Int.ofNat (nat_lit 42281280))]
theorem block003_data_flat026_step : block003_data_flat026 = (CoefficientMerge.fastMerge block003_data_flat022 block003_data_flat025) := by decide +kernel
theorem block003_data_flat026_original : block003_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (105417600 : Int) atom0245Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112092480 : Int) atom0246Coded) (CoefficientMerge.scale (42281280 : Int) atom0247Coded))) := by
  rw [block003_data_flat026_step, block003_data_flat022_original, block003_data_flat025_original]
def block003_data_flat027 : CoefficientMerge.Poly := [(nat_lit 341, Int.ofNat (nat_lit 90831240)), (nat_lit 342, Int.ofNat (nat_lit 98742720)), (nat_lit 343, Int.ofNat (nat_lit 105417600)), (nat_lit 344, Int.ofNat (nat_lit 112092480)), (nat_lit 353, Int.ofNat (nat_lit 42281280))]
theorem block003_data_flat027_step : block003_data_flat027 = (CoefficientMerge.fastMerge block003_data_flat021 block003_data_flat026) := by decide +kernel
theorem block003_data_flat027_original : block003_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90831240 : Int) atom0243Coded) (CoefficientMerge.scale (98742720 : Int) atom0244Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105417600 : Int) atom0245Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112092480 : Int) atom0246Coded) (CoefficientMerge.scale (42281280 : Int) atom0247Coded)))) := by
  rw [block003_data_flat027_step, block003_data_flat021_original, block003_data_flat026_original]
def block003_data_flat028 : CoefficientMerge.Poly := [(nat_lit 354, Int.ofNat (nat_lit 105534000))]
theorem block003_data_flat028_step : block003_data_flat028 = (CoefficientMerge.scale (105534000 : Int) atom0248Coded) := by decide +kernel
theorem block003_data_flat028_original : block003_data_flat028 = (CoefficientMerge.scale (105534000 : Int) atom0248Coded) := by
  rw [block003_data_flat028_step]
def block003_data_flat029 : CoefficientMerge.Poly := [(nat_lit 355, Int.ofNat (nat_lit 83431440))]
theorem block003_data_flat029_step : block003_data_flat029 = (CoefficientMerge.scale (83431440 : Int) atom0249Coded) := by decide +kernel
theorem block003_data_flat029_original : block003_data_flat029 = (CoefficientMerge.scale (83431440 : Int) atom0249Coded) := by
  rw [block003_data_flat029_step]
def block003_data_flat030 : CoefficientMerge.Poly := [(nat_lit 354, Int.ofNat (nat_lit 105534000)), (nat_lit 355, Int.ofNat (nat_lit 83431440))]
theorem block003_data_flat030_step : block003_data_flat030 = (CoefficientMerge.fastMerge block003_data_flat028 block003_data_flat029) := by decide +kernel
theorem block003_data_flat030_original : block003_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (105534000 : Int) atom0248Coded) (CoefficientMerge.scale (83431440 : Int) atom0249Coded)) := by
  rw [block003_data_flat030_step, block003_data_flat028_original, block003_data_flat029_original]
def block003_data_flat031 : CoefficientMerge.Poly := [(nat_lit 356, Int.ofNat (nat_lit 98601480))]
theorem block003_data_flat031_step : block003_data_flat031 = (CoefficientMerge.scale (98601480 : Int) atom0250Coded) := by decide +kernel
theorem block003_data_flat031_original : block003_data_flat031 = (CoefficientMerge.scale (98601480 : Int) atom0250Coded) := by
  rw [block003_data_flat031_step]
def block003_data_flat032 : CoefficientMerge.Poly := [(nat_lit 357, Int.ofNat (nat_lit 105713280))]
theorem block003_data_flat032_step : block003_data_flat032 = (CoefficientMerge.scale (105713280 : Int) atom0251Coded) := by decide +kernel
theorem block003_data_flat032_original : block003_data_flat032 = (CoefficientMerge.scale (105713280 : Int) atom0251Coded) := by
  rw [block003_data_flat032_step]
def block003_data_flat033 : CoefficientMerge.Poly := [(nat_lit 358, Int.ofNat (nat_lit 105421680))]
theorem block003_data_flat033_step : block003_data_flat033 = (CoefficientMerge.scale (105421680 : Int) atom0252Coded) := by decide +kernel
theorem block003_data_flat033_original : block003_data_flat033 = (CoefficientMerge.scale (105421680 : Int) atom0252Coded) := by
  rw [block003_data_flat033_step]
def block003_data_flat034 : CoefficientMerge.Poly := [(nat_lit 357, Int.ofNat (nat_lit 105713280)), (nat_lit 358, Int.ofNat (nat_lit 105421680))]
theorem block003_data_flat034_step : block003_data_flat034 = (CoefficientMerge.fastMerge block003_data_flat032 block003_data_flat033) := by decide +kernel
theorem block003_data_flat034_original : block003_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (105713280 : Int) atom0251Coded) (CoefficientMerge.scale (105421680 : Int) atom0252Coded)) := by
  rw [block003_data_flat034_step, block003_data_flat032_original, block003_data_flat033_original]
def block003_data_flat035 : CoefficientMerge.Poly := [(nat_lit 356, Int.ofNat (nat_lit 98601480)), (nat_lit 357, Int.ofNat (nat_lit 105713280)), (nat_lit 358, Int.ofNat (nat_lit 105421680))]
theorem block003_data_flat035_step : block003_data_flat035 = (CoefficientMerge.fastMerge block003_data_flat031 block003_data_flat034) := by decide +kernel
theorem block003_data_flat035_original : block003_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (98601480 : Int) atom0250Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105713280 : Int) atom0251Coded) (CoefficientMerge.scale (105421680 : Int) atom0252Coded))) := by
  rw [block003_data_flat035_step, block003_data_flat031_original, block003_data_flat034_original]
def block003_data_flat036 : CoefficientMerge.Poly := [(nat_lit 354, Int.ofNat (nat_lit 105534000)), (nat_lit 355, Int.ofNat (nat_lit 83431440)), (nat_lit 356, Int.ofNat (nat_lit 98601480)), (nat_lit 357, Int.ofNat (nat_lit 105713280)), (nat_lit 358, Int.ofNat (nat_lit 105421680))]
theorem block003_data_flat036_step : block003_data_flat036 = (CoefficientMerge.fastMerge block003_data_flat030 block003_data_flat035) := by decide +kernel
theorem block003_data_flat036_original : block003_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105534000 : Int) atom0248Coded) (CoefficientMerge.scale (83431440 : Int) atom0249Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98601480 : Int) atom0250Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105713280 : Int) atom0251Coded) (CoefficientMerge.scale (105421680 : Int) atom0252Coded)))) := by
  rw [block003_data_flat036_step, block003_data_flat030_original, block003_data_flat035_original]
def block003_data_flat037 : CoefficientMerge.Poly := [(nat_lit 341, Int.ofNat (nat_lit 90831240)), (nat_lit 342, Int.ofNat (nat_lit 98742720)), (nat_lit 343, Int.ofNat (nat_lit 105417600)), (nat_lit 344, Int.ofNat (nat_lit 112092480)), (nat_lit 353, Int.ofNat (nat_lit 42281280)), (nat_lit 354, Int.ofNat (nat_lit 105534000)), (nat_lit 355, Int.ofNat (nat_lit 83431440)), (nat_lit 356, Int.ofNat (nat_lit 98601480)), (nat_lit 357, Int.ofNat (nat_lit 105713280)), (nat_lit 358, Int.ofNat (nat_lit 105421680))]
theorem block003_data_flat037_step : block003_data_flat037 = (CoefficientMerge.fastMerge block003_data_flat027 block003_data_flat036) := by decide +kernel
theorem block003_data_flat037_original : block003_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90831240 : Int) atom0243Coded) (CoefficientMerge.scale (98742720 : Int) atom0244Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105417600 : Int) atom0245Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112092480 : Int) atom0246Coded) (CoefficientMerge.scale (42281280 : Int) atom0247Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105534000 : Int) atom0248Coded) (CoefficientMerge.scale (83431440 : Int) atom0249Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98601480 : Int) atom0250Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105713280 : Int) atom0251Coded) (CoefficientMerge.scale (105421680 : Int) atom0252Coded))))) := by
  rw [block003_data_flat037_step, block003_data_flat027_original, block003_data_flat036_original]
def block003_data_flat038 : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 90512640)), (nat_lit 325, Int.ofNat (nat_lit 68604840)), (nat_lit 326, Int.ofNat (nat_lit 82191240)), (nat_lit 327, Int.ofNat (nat_lit 91916280)), (nat_lit 328, Int.ofNat (nat_lit 98458200)), (nat_lit 329, Int.ofNat (nat_lit 105000120)), (nat_lit 337, Int.ofNat (nat_lit 34030080)), (nat_lit 338, Int.ofNat (nat_lit 61189760)), (nat_lit 339, Int.ofNat (nat_lit 95363520)), (nat_lit 340, Int.ofNat (nat_lit 75650880)), (nat_lit 341, Int.ofNat (nat_lit 90831240)), (nat_lit 342, Int.ofNat (nat_lit 98742720)), (nat_lit 343, Int.ofNat (nat_lit 105417600)), (nat_lit 344, Int.ofNat (nat_lit 112092480)), (nat_lit 353, Int.ofNat (nat_lit 42281280)), (nat_lit 354, Int.ofNat (nat_lit 105534000)), (nat_lit 355, Int.ofNat (nat_lit 83431440)), (nat_lit 356, Int.ofNat (nat_lit 98601480)), (nat_lit 357, Int.ofNat (nat_lit 105713280)), (nat_lit 358, Int.ofNat (nat_lit 105421680))]
theorem block003_data_flat038_step : block003_data_flat038 = (CoefficientMerge.fastMerge block003_data_flat018 block003_data_flat037) := by decide +kernel
theorem block003_data_flat038_original : block003_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90512640 : Int) atom0233Coded) (CoefficientMerge.scale (68604840 : Int) atom0234Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82191240 : Int) atom0235Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91916280 : Int) atom0236Coded) (CoefficientMerge.scale (98458200 : Int) atom0237Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105000120 : Int) atom0238Coded) (CoefficientMerge.scale (34030080 : Int) atom0239Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61189760 : Int) atom0240Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (95363520 : Int) atom0241Coded) (CoefficientMerge.scale (75650880 : Int) atom0242Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90831240 : Int) atom0243Coded) (CoefficientMerge.scale (98742720 : Int) atom0244Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105417600 : Int) atom0245Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112092480 : Int) atom0246Coded) (CoefficientMerge.scale (42281280 : Int) atom0247Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105534000 : Int) atom0248Coded) (CoefficientMerge.scale (83431440 : Int) atom0249Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98601480 : Int) atom0250Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105713280 : Int) atom0251Coded) (CoefficientMerge.scale (105421680 : Int) atom0252Coded)))))) := by
  rw [block003_data_flat038_step, block003_data_flat018_original, block003_data_flat037_original]
def block003_data_flat039 : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 123972480))]
theorem block003_data_flat039_step : block003_data_flat039 = (CoefficientMerge.scale (123972480 : Int) atom0253Coded) := by decide +kernel
theorem block003_data_flat039_original : block003_data_flat039 = (CoefficientMerge.scale (123972480 : Int) atom0253Coded) := by
  rw [block003_data_flat039_step]
def block003_data_flat040 : CoefficientMerge.Poly := [(nat_lit 369, Int.ofNat (nat_lit 78278400))]
theorem block003_data_flat040_step : block003_data_flat040 = (CoefficientMerge.scale (78278400 : Int) atom0254Coded) := by decide +kernel
theorem block003_data_flat040_original : block003_data_flat040 = (CoefficientMerge.scale (78278400 : Int) atom0254Coded) := by
  rw [block003_data_flat040_step]
def block003_data_flat041 : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 123972480)), (nat_lit 369, Int.ofNat (nat_lit 78278400))]
theorem block003_data_flat041_step : block003_data_flat041 = (CoefficientMerge.fastMerge block003_data_flat039 block003_data_flat040) := by decide +kernel
theorem block003_data_flat041_original : block003_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (123972480 : Int) atom0253Coded) (CoefficientMerge.scale (78278400 : Int) atom0254Coded)) := by
  rw [block003_data_flat041_step, block003_data_flat039_original, block003_data_flat040_original]
def block003_data_flat042 : CoefficientMerge.Poly := [(nat_lit 370, Int.ofNat (nat_lit 124610400))]
theorem block003_data_flat042_step : block003_data_flat042 = (CoefficientMerge.scale (124610400 : Int) atom0255Coded) := by decide +kernel
theorem block003_data_flat042_original : block003_data_flat042 = (CoefficientMerge.scale (124610400 : Int) atom0255Coded) := by
  rw [block003_data_flat042_step]
def block003_data_flat043 : CoefficientMerge.Poly := [(nat_lit 371, Int.ofNat (nat_lit 162543240))]
theorem block003_data_flat043_step : block003_data_flat043 = (CoefficientMerge.scale (162543240 : Int) atom0256Coded) := by decide +kernel
theorem block003_data_flat043_original : block003_data_flat043 = (CoefficientMerge.scale (162543240 : Int) atom0256Coded) := by
  rw [block003_data_flat043_step]
def block003_data_flat044 : CoefficientMerge.Poly := [(nat_lit 372, Int.ofNat (nat_lit 171695520))]
theorem block003_data_flat044_step : block003_data_flat044 = (CoefficientMerge.scale (171695520 : Int) atom0257Coded) := by decide +kernel
theorem block003_data_flat044_original : block003_data_flat044 = (CoefficientMerge.scale (171695520 : Int) atom0257Coded) := by
  rw [block003_data_flat044_step]
def block003_data_flat045 : CoefficientMerge.Poly := [(nat_lit 371, Int.ofNat (nat_lit 162543240)), (nat_lit 372, Int.ofNat (nat_lit 171695520))]
theorem block003_data_flat045_step : block003_data_flat045 = (CoefficientMerge.fastMerge block003_data_flat043 block003_data_flat044) := by decide +kernel
theorem block003_data_flat045_original : block003_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (162543240 : Int) atom0256Coded) (CoefficientMerge.scale (171695520 : Int) atom0257Coded)) := by
  rw [block003_data_flat045_step, block003_data_flat043_original, block003_data_flat044_original]
def block003_data_flat046 : CoefficientMerge.Poly := [(nat_lit 370, Int.ofNat (nat_lit 124610400)), (nat_lit 371, Int.ofNat (nat_lit 162543240)), (nat_lit 372, Int.ofNat (nat_lit 171695520))]
theorem block003_data_flat046_step : block003_data_flat046 = (CoefficientMerge.fastMerge block003_data_flat042 block003_data_flat045) := by decide +kernel
theorem block003_data_flat046_original : block003_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (124610400 : Int) atom0255Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162543240 : Int) atom0256Coded) (CoefficientMerge.scale (171695520 : Int) atom0257Coded))) := by
  rw [block003_data_flat046_step, block003_data_flat042_original, block003_data_flat045_original]
def block003_data_flat047 : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 123972480)), (nat_lit 369, Int.ofNat (nat_lit 78278400)), (nat_lit 370, Int.ofNat (nat_lit 124610400)), (nat_lit 371, Int.ofNat (nat_lit 162543240)), (nat_lit 372, Int.ofNat (nat_lit 171695520))]
theorem block003_data_flat047_step : block003_data_flat047 = (CoefficientMerge.fastMerge block003_data_flat041 block003_data_flat046) := by decide +kernel
theorem block003_data_flat047_original : block003_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123972480 : Int) atom0253Coded) (CoefficientMerge.scale (78278400 : Int) atom0254Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124610400 : Int) atom0255Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162543240 : Int) atom0256Coded) (CoefficientMerge.scale (171695520 : Int) atom0257Coded)))) := by
  rw [block003_data_flat047_step, block003_data_flat041_original, block003_data_flat046_original]
def block003_data_flat048 : CoefficientMerge.Poly := [(nat_lit 373, Int.ofNat (nat_lit 110190240))]
theorem block003_data_flat048_step : block003_data_flat048 = (CoefficientMerge.scale (110190240 : Int) atom0258Coded) := by decide +kernel
theorem block003_data_flat048_original : block003_data_flat048 = (CoefficientMerge.scale (110190240 : Int) atom0258Coded) := by
  rw [block003_data_flat048_step]
def block003_data_flat049 : CoefficientMerge.Poly := [(nat_lit 374, Int.ofNat (nat_lit 132083640))]
theorem block003_data_flat049_step : block003_data_flat049 = (CoefficientMerge.scale (132083640 : Int) atom0259Coded) := by decide +kernel
theorem block003_data_flat049_original : block003_data_flat049 = (CoefficientMerge.scale (132083640 : Int) atom0259Coded) := by
  rw [block003_data_flat049_step]
def block003_data_flat050 : CoefficientMerge.Poly := [(nat_lit 373, Int.ofNat (nat_lit 110190240)), (nat_lit 374, Int.ofNat (nat_lit 132083640))]
theorem block003_data_flat050_step : block003_data_flat050 = (CoefficientMerge.fastMerge block003_data_flat048 block003_data_flat049) := by decide +kernel
theorem block003_data_flat050_original : block003_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (110190240 : Int) atom0258Coded) (CoefficientMerge.scale (132083640 : Int) atom0259Coded)) := by
  rw [block003_data_flat050_step, block003_data_flat048_original, block003_data_flat049_original]
def block003_data_flat051 : CoefficientMerge.Poly := [(nat_lit 385, Int.ofNat (nat_lit 50720688))]
theorem block003_data_flat051_step : block003_data_flat051 = (CoefficientMerge.scale (50720688 : Int) atom0260Coded) := by decide +kernel
theorem block003_data_flat051_original : block003_data_flat051 = (CoefficientMerge.scale (50720688 : Int) atom0260Coded) := by
  rw [block003_data_flat051_step]
def block003_data_flat052 : CoefficientMerge.Poly := [(nat_lit 386, Int.ofNat (nat_lit 119681280))]
theorem block003_data_flat052_step : block003_data_flat052 = (CoefficientMerge.scale (119681280 : Int) atom0261Coded) := by decide +kernel
theorem block003_data_flat052_original : block003_data_flat052 = (CoefficientMerge.scale (119681280 : Int) atom0261Coded) := by
  rw [block003_data_flat052_step]
def block003_data_flat053 : CoefficientMerge.Poly := [(nat_lit 387, Int.ofNat (nat_lit 148644360))]
theorem block003_data_flat053_step : block003_data_flat053 = (CoefficientMerge.scale (148644360 : Int) atom0262Coded) := by decide +kernel
theorem block003_data_flat053_original : block003_data_flat053 = (CoefficientMerge.scale (148644360 : Int) atom0262Coded) := by
  rw [block003_data_flat053_step]
def block003_data_flat054 : CoefficientMerge.Poly := [(nat_lit 386, Int.ofNat (nat_lit 119681280)), (nat_lit 387, Int.ofNat (nat_lit 148644360))]
theorem block003_data_flat054_step : block003_data_flat054 = (CoefficientMerge.fastMerge block003_data_flat052 block003_data_flat053) := by decide +kernel
theorem block003_data_flat054_original : block003_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (119681280 : Int) atom0261Coded) (CoefficientMerge.scale (148644360 : Int) atom0262Coded)) := by
  rw [block003_data_flat054_step, block003_data_flat052_original, block003_data_flat053_original]
def block003_data_flat055 : CoefficientMerge.Poly := [(nat_lit 385, Int.ofNat (nat_lit 50720688)), (nat_lit 386, Int.ofNat (nat_lit 119681280)), (nat_lit 387, Int.ofNat (nat_lit 148644360))]
theorem block003_data_flat055_step : block003_data_flat055 = (CoefficientMerge.fastMerge block003_data_flat051 block003_data_flat054) := by decide +kernel
theorem block003_data_flat055_original : block003_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50720688 : Int) atom0260Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119681280 : Int) atom0261Coded) (CoefficientMerge.scale (148644360 : Int) atom0262Coded))) := by
  rw [block003_data_flat055_step, block003_data_flat051_original, block003_data_flat054_original]
def block003_data_flat056 : CoefficientMerge.Poly := [(nat_lit 373, Int.ofNat (nat_lit 110190240)), (nat_lit 374, Int.ofNat (nat_lit 132083640)), (nat_lit 385, Int.ofNat (nat_lit 50720688)), (nat_lit 386, Int.ofNat (nat_lit 119681280)), (nat_lit 387, Int.ofNat (nat_lit 148644360))]
theorem block003_data_flat056_step : block003_data_flat056 = (CoefficientMerge.fastMerge block003_data_flat050 block003_data_flat055) := by decide +kernel
theorem block003_data_flat056_original : block003_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110190240 : Int) atom0258Coded) (CoefficientMerge.scale (132083640 : Int) atom0259Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50720688 : Int) atom0260Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119681280 : Int) atom0261Coded) (CoefficientMerge.scale (148644360 : Int) atom0262Coded)))) := by
  rw [block003_data_flat056_step, block003_data_flat050_original, block003_data_flat055_original]
def block003_data_flat057 : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 123972480)), (nat_lit 369, Int.ofNat (nat_lit 78278400)), (nat_lit 370, Int.ofNat (nat_lit 124610400)), (nat_lit 371, Int.ofNat (nat_lit 162543240)), (nat_lit 372, Int.ofNat (nat_lit 171695520)), (nat_lit 373, Int.ofNat (nat_lit 110190240)), (nat_lit 374, Int.ofNat (nat_lit 132083640)), (nat_lit 385, Int.ofNat (nat_lit 50720688)), (nat_lit 386, Int.ofNat (nat_lit 119681280)), (nat_lit 387, Int.ofNat (nat_lit 148644360))]
theorem block003_data_flat057_step : block003_data_flat057 = (CoefficientMerge.fastMerge block003_data_flat047 block003_data_flat056) := by decide +kernel
theorem block003_data_flat057_original : block003_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123972480 : Int) atom0253Coded) (CoefficientMerge.scale (78278400 : Int) atom0254Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124610400 : Int) atom0255Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162543240 : Int) atom0256Coded) (CoefficientMerge.scale (171695520 : Int) atom0257Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110190240 : Int) atom0258Coded) (CoefficientMerge.scale (132083640 : Int) atom0259Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50720688 : Int) atom0260Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119681280 : Int) atom0261Coded) (CoefficientMerge.scale (148644360 : Int) atom0262Coded))))) := by
  rw [block003_data_flat057_step, block003_data_flat047_original, block003_data_flat056_original]
def block003_data_flat058 : CoefficientMerge.Poly := [(nat_lit 388, Int.ofNat (nat_lit 109284120))]
theorem block003_data_flat058_step : block003_data_flat058 = (CoefficientMerge.scale (109284120 : Int) atom0263Coded) := by decide +kernel
theorem block003_data_flat058_original : block003_data_flat058 = (CoefficientMerge.scale (109284120 : Int) atom0263Coded) := by
  rw [block003_data_flat058_step]
def block003_data_flat059 : CoefficientMerge.Poly := [(nat_lit 389, Int.ofNat (nat_lit 121793040))]
theorem block003_data_flat059_step : block003_data_flat059 = (CoefficientMerge.scale (121793040 : Int) atom0264Coded) := by decide +kernel
theorem block003_data_flat059_original : block003_data_flat059 = (CoefficientMerge.scale (121793040 : Int) atom0264Coded) := by
  rw [block003_data_flat059_step]
def block003_data_flat060 : CoefficientMerge.Poly := [(nat_lit 388, Int.ofNat (nat_lit 109284120)), (nat_lit 389, Int.ofNat (nat_lit 121793040))]
theorem block003_data_flat060_step : block003_data_flat060 = (CoefficientMerge.fastMerge block003_data_flat058 block003_data_flat059) := by decide +kernel
theorem block003_data_flat060_original : block003_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (109284120 : Int) atom0263Coded) (CoefficientMerge.scale (121793040 : Int) atom0264Coded)) := by
  rw [block003_data_flat060_step, block003_data_flat058_original, block003_data_flat059_original]
def block003_data_flat061 : CoefficientMerge.Poly := [(nat_lit 401, Int.ofNat (nat_lit 86289840))]
theorem block003_data_flat061_step : block003_data_flat061 = (CoefficientMerge.scale (86289840 : Int) atom0265Coded) := by decide +kernel
theorem block003_data_flat061_original : block003_data_flat061 = (CoefficientMerge.scale (86289840 : Int) atom0265Coded) := by
  rw [block003_data_flat061_step]
def block003_data_flat062 : CoefficientMerge.Poly := [(nat_lit 402, Int.ofNat (nat_lit 150873120))]
theorem block003_data_flat062_step : block003_data_flat062 = (CoefficientMerge.scale (150873120 : Int) atom0266Coded) := by decide +kernel
theorem block003_data_flat062_original : block003_data_flat062 = (CoefficientMerge.scale (150873120 : Int) atom0266Coded) := by
  rw [block003_data_flat062_step]
def block003_data_flat063 : CoefficientMerge.Poly := [(nat_lit 403, Int.ofNat (nat_lit 111926880))]
theorem block003_data_flat063_step : block003_data_flat063 = (CoefficientMerge.scale (111926880 : Int) atom0267Coded) := by decide +kernel
theorem block003_data_flat063_original : block003_data_flat063 = (CoefficientMerge.scale (111926880 : Int) atom0267Coded) := by
  rw [block003_data_flat063_step]
def block003_data_flat064 : CoefficientMerge.Poly := [(nat_lit 402, Int.ofNat (nat_lit 150873120)), (nat_lit 403, Int.ofNat (nat_lit 111926880))]
theorem block003_data_flat064_step : block003_data_flat064 = (CoefficientMerge.fastMerge block003_data_flat062 block003_data_flat063) := by decide +kernel
theorem block003_data_flat064_original : block003_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (150873120 : Int) atom0266Coded) (CoefficientMerge.scale (111926880 : Int) atom0267Coded)) := by
  rw [block003_data_flat064_step, block003_data_flat062_original, block003_data_flat063_original]
def block003_data_flat065 : CoefficientMerge.Poly := [(nat_lit 401, Int.ofNat (nat_lit 86289840)), (nat_lit 402, Int.ofNat (nat_lit 150873120)), (nat_lit 403, Int.ofNat (nat_lit 111926880))]
theorem block003_data_flat065_step : block003_data_flat065 = (CoefficientMerge.fastMerge block003_data_flat061 block003_data_flat064) := by decide +kernel
theorem block003_data_flat065_original : block003_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (86289840 : Int) atom0265Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150873120 : Int) atom0266Coded) (CoefficientMerge.scale (111926880 : Int) atom0267Coded))) := by
  rw [block003_data_flat065_step, block003_data_flat061_original, block003_data_flat064_original]
def block003_data_flat066 : CoefficientMerge.Poly := [(nat_lit 388, Int.ofNat (nat_lit 109284120)), (nat_lit 389, Int.ofNat (nat_lit 121793040)), (nat_lit 401, Int.ofNat (nat_lit 86289840)), (nat_lit 402, Int.ofNat (nat_lit 150873120)), (nat_lit 403, Int.ofNat (nat_lit 111926880))]
theorem block003_data_flat066_step : block003_data_flat066 = (CoefficientMerge.fastMerge block003_data_flat060 block003_data_flat065) := by decide +kernel
theorem block003_data_flat066_original : block003_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109284120 : Int) atom0263Coded) (CoefficientMerge.scale (121793040 : Int) atom0264Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86289840 : Int) atom0265Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150873120 : Int) atom0266Coded) (CoefficientMerge.scale (111926880 : Int) atom0267Coded)))) := by
  rw [block003_data_flat066_step, block003_data_flat060_original, block003_data_flat065_original]
def block003_data_flat067 : CoefficientMerge.Poly := [(nat_lit 404, Int.ofNat (nat_lit 129163320))]
theorem block003_data_flat067_step : block003_data_flat067 = (CoefficientMerge.scale (129163320 : Int) atom0268Coded) := by decide +kernel
theorem block003_data_flat067_original : block003_data_flat067 = (CoefficientMerge.scale (129163320 : Int) atom0268Coded) := by
  rw [block003_data_flat067_step]
def block003_data_flat068 : CoefficientMerge.Poly := [(nat_lit 417, Int.ofNat (nat_lit 60586920))]
theorem block003_data_flat068_step : block003_data_flat068 = (CoefficientMerge.scale (60586920 : Int) atom0269Coded) := by decide +kernel
theorem block003_data_flat068_original : block003_data_flat068 = (CoefficientMerge.scale (60586920 : Int) atom0269Coded) := by
  rw [block003_data_flat068_step]
def block003_data_flat069 : CoefficientMerge.Poly := [(nat_lit 404, Int.ofNat (nat_lit 129163320)), (nat_lit 417, Int.ofNat (nat_lit 60586920))]
theorem block003_data_flat069_step : block003_data_flat069 = (CoefficientMerge.fastMerge block003_data_flat067 block003_data_flat068) := by decide +kernel
theorem block003_data_flat069_original : block003_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (129163320 : Int) atom0268Coded) (CoefficientMerge.scale (60586920 : Int) atom0269Coded)) := by
  rw [block003_data_flat069_step, block003_data_flat067_original, block003_data_flat068_original]
def block003_data_flat070 : CoefficientMerge.Poly := [(nat_lit 418, Int.ofNat (nat_lit 82651680))]
theorem block003_data_flat070_step : block003_data_flat070 = (CoefficientMerge.scale (82651680 : Int) atom0270Coded) := by decide +kernel
theorem block003_data_flat070_original : block003_data_flat070 = (CoefficientMerge.scale (82651680 : Int) atom0270Coded) := by
  rw [block003_data_flat070_step]
def block003_data_flat071 : CoefficientMerge.Poly := [(nat_lit 419, Int.ofNat (nat_lit 99339120))]
theorem block003_data_flat071_step : block003_data_flat071 = (CoefficientMerge.scale (99339120 : Int) atom0271Coded) := by decide +kernel
theorem block003_data_flat071_original : block003_data_flat071 = (CoefficientMerge.scale (99339120 : Int) atom0271Coded) := by
  rw [block003_data_flat071_step]
def block003_data_flat072 : CoefficientMerge.Poly := [(nat_lit 433, Int.ofNat (nat_lit 15121080))]
theorem block003_data_flat072_step : block003_data_flat072 = (CoefficientMerge.scale (15121080 : Int) atom0272Coded) := by decide +kernel
theorem block003_data_flat072_original : block003_data_flat072 = (CoefficientMerge.scale (15121080 : Int) atom0272Coded) := by
  rw [block003_data_flat072_step]
def block003_data_flat073 : CoefficientMerge.Poly := [(nat_lit 419, Int.ofNat (nat_lit 99339120)), (nat_lit 433, Int.ofNat (nat_lit 15121080))]
theorem block003_data_flat073_step : block003_data_flat073 = (CoefficientMerge.fastMerge block003_data_flat071 block003_data_flat072) := by decide +kernel
theorem block003_data_flat073_original : block003_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (99339120 : Int) atom0271Coded) (CoefficientMerge.scale (15121080 : Int) atom0272Coded)) := by
  rw [block003_data_flat073_step, block003_data_flat071_original, block003_data_flat072_original]
def block003_data_flat074 : CoefficientMerge.Poly := [(nat_lit 418, Int.ofNat (nat_lit 82651680)), (nat_lit 419, Int.ofNat (nat_lit 99339120)), (nat_lit 433, Int.ofNat (nat_lit 15121080))]
theorem block003_data_flat074_step : block003_data_flat074 = (CoefficientMerge.fastMerge block003_data_flat070 block003_data_flat073) := by decide +kernel
theorem block003_data_flat074_original : block003_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82651680 : Int) atom0270Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99339120 : Int) atom0271Coded) (CoefficientMerge.scale (15121080 : Int) atom0272Coded))) := by
  rw [block003_data_flat074_step, block003_data_flat070_original, block003_data_flat073_original]
def block003_data_flat075 : CoefficientMerge.Poly := [(nat_lit 404, Int.ofNat (nat_lit 129163320)), (nat_lit 417, Int.ofNat (nat_lit 60586920)), (nat_lit 418, Int.ofNat (nat_lit 82651680)), (nat_lit 419, Int.ofNat (nat_lit 99339120)), (nat_lit 433, Int.ofNat (nat_lit 15121080))]
theorem block003_data_flat075_step : block003_data_flat075 = (CoefficientMerge.fastMerge block003_data_flat069 block003_data_flat074) := by decide +kernel
theorem block003_data_flat075_original : block003_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129163320 : Int) atom0268Coded) (CoefficientMerge.scale (60586920 : Int) atom0269Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82651680 : Int) atom0270Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99339120 : Int) atom0271Coded) (CoefficientMerge.scale (15121080 : Int) atom0272Coded)))) := by
  rw [block003_data_flat075_step, block003_data_flat069_original, block003_data_flat074_original]
def block003_data_flat076 : CoefficientMerge.Poly := [(nat_lit 388, Int.ofNat (nat_lit 109284120)), (nat_lit 389, Int.ofNat (nat_lit 121793040)), (nat_lit 401, Int.ofNat (nat_lit 86289840)), (nat_lit 402, Int.ofNat (nat_lit 150873120)), (nat_lit 403, Int.ofNat (nat_lit 111926880)), (nat_lit 404, Int.ofNat (nat_lit 129163320)), (nat_lit 417, Int.ofNat (nat_lit 60586920)), (nat_lit 418, Int.ofNat (nat_lit 82651680)), (nat_lit 419, Int.ofNat (nat_lit 99339120)), (nat_lit 433, Int.ofNat (nat_lit 15121080))]
theorem block003_data_flat076_step : block003_data_flat076 = (CoefficientMerge.fastMerge block003_data_flat066 block003_data_flat075) := by decide +kernel
theorem block003_data_flat076_original : block003_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109284120 : Int) atom0263Coded) (CoefficientMerge.scale (121793040 : Int) atom0264Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86289840 : Int) atom0265Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150873120 : Int) atom0266Coded) (CoefficientMerge.scale (111926880 : Int) atom0267Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129163320 : Int) atom0268Coded) (CoefficientMerge.scale (60586920 : Int) atom0269Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82651680 : Int) atom0270Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99339120 : Int) atom0271Coded) (CoefficientMerge.scale (15121080 : Int) atom0272Coded))))) := by
  rw [block003_data_flat076_step, block003_data_flat066_original, block003_data_flat075_original]
def block003_data_flat077 : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 123972480)), (nat_lit 369, Int.ofNat (nat_lit 78278400)), (nat_lit 370, Int.ofNat (nat_lit 124610400)), (nat_lit 371, Int.ofNat (nat_lit 162543240)), (nat_lit 372, Int.ofNat (nat_lit 171695520)), (nat_lit 373, Int.ofNat (nat_lit 110190240)), (nat_lit 374, Int.ofNat (nat_lit 132083640)), (nat_lit 385, Int.ofNat (nat_lit 50720688)), (nat_lit 386, Int.ofNat (nat_lit 119681280)), (nat_lit 387, Int.ofNat (nat_lit 148644360)), (nat_lit 388, Int.ofNat (nat_lit 109284120)), (nat_lit 389, Int.ofNat (nat_lit 121793040)), (nat_lit 401, Int.ofNat (nat_lit 86289840)), (nat_lit 402, Int.ofNat (nat_lit 150873120)), (nat_lit 403, Int.ofNat (nat_lit 111926880)), (nat_lit 404, Int.ofNat (nat_lit 129163320)), (nat_lit 417, Int.ofNat (nat_lit 60586920)), (nat_lit 418, Int.ofNat (nat_lit 82651680)), (nat_lit 419, Int.ofNat (nat_lit 99339120)), (nat_lit 433, Int.ofNat (nat_lit 15121080))]
theorem block003_data_flat077_step : block003_data_flat077 = (CoefficientMerge.fastMerge block003_data_flat057 block003_data_flat076) := by decide +kernel
theorem block003_data_flat077_original : block003_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123972480 : Int) atom0253Coded) (CoefficientMerge.scale (78278400 : Int) atom0254Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124610400 : Int) atom0255Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162543240 : Int) atom0256Coded) (CoefficientMerge.scale (171695520 : Int) atom0257Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110190240 : Int) atom0258Coded) (CoefficientMerge.scale (132083640 : Int) atom0259Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50720688 : Int) atom0260Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119681280 : Int) atom0261Coded) (CoefficientMerge.scale (148644360 : Int) atom0262Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109284120 : Int) atom0263Coded) (CoefficientMerge.scale (121793040 : Int) atom0264Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86289840 : Int) atom0265Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150873120 : Int) atom0266Coded) (CoefficientMerge.scale (111926880 : Int) atom0267Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129163320 : Int) atom0268Coded) (CoefficientMerge.scale (60586920 : Int) atom0269Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82651680 : Int) atom0270Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99339120 : Int) atom0271Coded) (CoefficientMerge.scale (15121080 : Int) atom0272Coded)))))) := by
  rw [block003_data_flat077_step, block003_data_flat057_original, block003_data_flat076_original]
def block003_data_flat078 : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 90512640)), (nat_lit 325, Int.ofNat (nat_lit 68604840)), (nat_lit 326, Int.ofNat (nat_lit 82191240)), (nat_lit 327, Int.ofNat (nat_lit 91916280)), (nat_lit 328, Int.ofNat (nat_lit 98458200)), (nat_lit 329, Int.ofNat (nat_lit 105000120)), (nat_lit 337, Int.ofNat (nat_lit 34030080)), (nat_lit 338, Int.ofNat (nat_lit 61189760)), (nat_lit 339, Int.ofNat (nat_lit 95363520)), (nat_lit 340, Int.ofNat (nat_lit 75650880)), (nat_lit 341, Int.ofNat (nat_lit 90831240)), (nat_lit 342, Int.ofNat (nat_lit 98742720)), (nat_lit 343, Int.ofNat (nat_lit 105417600)), (nat_lit 344, Int.ofNat (nat_lit 112092480)), (nat_lit 353, Int.ofNat (nat_lit 42281280)), (nat_lit 354, Int.ofNat (nat_lit 105534000)), (nat_lit 355, Int.ofNat (nat_lit 83431440)), (nat_lit 356, Int.ofNat (nat_lit 98601480)), (nat_lit 357, Int.ofNat (nat_lit 105713280)), (nat_lit 358, Int.ofNat (nat_lit 105421680)), (nat_lit 359, Int.ofNat (nat_lit 123972480)), (nat_lit 369, Int.ofNat (nat_lit 78278400)), (nat_lit 370, Int.ofNat (nat_lit 124610400)), (nat_lit 371, Int.ofNat (nat_lit 162543240)), (nat_lit 372, Int.ofNat (nat_lit 171695520)), (nat_lit 373, Int.ofNat (nat_lit 110190240)), (nat_lit 374, Int.ofNat (nat_lit 132083640)), (nat_lit 385, Int.ofNat (nat_lit 50720688)), (nat_lit 386, Int.ofNat (nat_lit 119681280)), (nat_lit 387, Int.ofNat (nat_lit 148644360)), (nat_lit 388, Int.ofNat (nat_lit 109284120)), (nat_lit 389, Int.ofNat (nat_lit 121793040)), (nat_lit 401, Int.ofNat (nat_lit 86289840)), (nat_lit 402, Int.ofNat (nat_lit 150873120)), (nat_lit 403, Int.ofNat (nat_lit 111926880)), (nat_lit 404, Int.ofNat (nat_lit 129163320)), (nat_lit 417, Int.ofNat (nat_lit 60586920)), (nat_lit 418, Int.ofNat (nat_lit 82651680)), (nat_lit 419, Int.ofNat (nat_lit 99339120)), (nat_lit 433, Int.ofNat (nat_lit 15121080))]
theorem block003_data_flat078_step : block003_data_flat078 = (CoefficientMerge.fastMerge block003_data_flat038 block003_data_flat077) := by decide +kernel
theorem block003_data_flat078_original : block003_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90512640 : Int) atom0233Coded) (CoefficientMerge.scale (68604840 : Int) atom0234Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82191240 : Int) atom0235Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91916280 : Int) atom0236Coded) (CoefficientMerge.scale (98458200 : Int) atom0237Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105000120 : Int) atom0238Coded) (CoefficientMerge.scale (34030080 : Int) atom0239Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61189760 : Int) atom0240Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (95363520 : Int) atom0241Coded) (CoefficientMerge.scale (75650880 : Int) atom0242Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90831240 : Int) atom0243Coded) (CoefficientMerge.scale (98742720 : Int) atom0244Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105417600 : Int) atom0245Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112092480 : Int) atom0246Coded) (CoefficientMerge.scale (42281280 : Int) atom0247Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105534000 : Int) atom0248Coded) (CoefficientMerge.scale (83431440 : Int) atom0249Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98601480 : Int) atom0250Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105713280 : Int) atom0251Coded) (CoefficientMerge.scale (105421680 : Int) atom0252Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123972480 : Int) atom0253Coded) (CoefficientMerge.scale (78278400 : Int) atom0254Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124610400 : Int) atom0255Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162543240 : Int) atom0256Coded) (CoefficientMerge.scale (171695520 : Int) atom0257Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110190240 : Int) atom0258Coded) (CoefficientMerge.scale (132083640 : Int) atom0259Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50720688 : Int) atom0260Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119681280 : Int) atom0261Coded) (CoefficientMerge.scale (148644360 : Int) atom0262Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109284120 : Int) atom0263Coded) (CoefficientMerge.scale (121793040 : Int) atom0264Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86289840 : Int) atom0265Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150873120 : Int) atom0266Coded) (CoefficientMerge.scale (111926880 : Int) atom0267Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129163320 : Int) atom0268Coded) (CoefficientMerge.scale (60586920 : Int) atom0269Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82651680 : Int) atom0270Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99339120 : Int) atom0271Coded) (CoefficientMerge.scale (15121080 : Int) atom0272Coded))))))) := by
  rw [block003_data_flat078_step, block003_data_flat038_original, block003_data_flat077_original]
def block003_data_flat079 : CoefficientMerge.Poly := [(nat_lit 434, Int.ofNat (nat_lit 38720880))]
theorem block003_data_flat079_step : block003_data_flat079 = (CoefficientMerge.scale (38720880 : Int) atom0273Coded) := by decide +kernel
theorem block003_data_flat079_original : block003_data_flat079 = (CoefficientMerge.scale (38720880 : Int) atom0273Coded) := by
  rw [block003_data_flat079_step]
def block003_data_flat080 : CoefficientMerge.Poly := [(nat_lit 449, Int.ofNat (nat_lit 13514040))]
theorem block003_data_flat080_step : block003_data_flat080 = (CoefficientMerge.scale (13514040 : Int) atom0274Coded) := by decide +kernel
theorem block003_data_flat080_original : block003_data_flat080 = (CoefficientMerge.scale (13514040 : Int) atom0274Coded) := by
  rw [block003_data_flat080_step]
def block003_data_flat081 : CoefficientMerge.Poly := [(nat_lit 434, Int.ofNat (nat_lit 38720880)), (nat_lit 449, Int.ofNat (nat_lit 13514040))]
theorem block003_data_flat081_step : block003_data_flat081 = (CoefficientMerge.fastMerge block003_data_flat079 block003_data_flat080) := by decide +kernel
theorem block003_data_flat081_original : block003_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38720880 : Int) atom0273Coded) (CoefficientMerge.scale (13514040 : Int) atom0274Coded)) := by
  rw [block003_data_flat081_step, block003_data_flat079_original, block003_data_flat080_original]
def block003_data_flat082 : CoefficientMerge.Poly := [(nat_lit 482, Int.ofNat (nat_lit 10108800))]
theorem block003_data_flat082_step : block003_data_flat082 = (CoefficientMerge.scale (10108800 : Int) atom0275Coded) := by decide +kernel
theorem block003_data_flat082_original : block003_data_flat082 = (CoefficientMerge.scale (10108800 : Int) atom0275Coded) := by
  rw [block003_data_flat082_step]
def block003_data_flat083 : CoefficientMerge.Poly := [(nat_lit 483, Int.ofNat (nat_lit 28200960))]
theorem block003_data_flat083_step : block003_data_flat083 = (CoefficientMerge.scale (28200960 : Int) atom0276Coded) := by decide +kernel
theorem block003_data_flat083_original : block003_data_flat083 = (CoefficientMerge.scale (28200960 : Int) atom0276Coded) := by
  rw [block003_data_flat083_step]
def block003_data_flat084 : CoefficientMerge.Poly := [(nat_lit 484, Int.ofNat (nat_lit 26075520))]
theorem block003_data_flat084_step : block003_data_flat084 = (CoefficientMerge.scale (26075520 : Int) atom0277Coded) := by decide +kernel
theorem block003_data_flat084_original : block003_data_flat084 = (CoefficientMerge.scale (26075520 : Int) atom0277Coded) := by
  rw [block003_data_flat084_step]
def block003_data_flat085 : CoefficientMerge.Poly := [(nat_lit 483, Int.ofNat (nat_lit 28200960)), (nat_lit 484, Int.ofNat (nat_lit 26075520))]
theorem block003_data_flat085_step : block003_data_flat085 = (CoefficientMerge.fastMerge block003_data_flat083 block003_data_flat084) := by decide +kernel
theorem block003_data_flat085_original : block003_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28200960 : Int) atom0276Coded) (CoefficientMerge.scale (26075520 : Int) atom0277Coded)) := by
  rw [block003_data_flat085_step, block003_data_flat083_original, block003_data_flat084_original]
def block003_data_flat086 : CoefficientMerge.Poly := [(nat_lit 482, Int.ofNat (nat_lit 10108800)), (nat_lit 483, Int.ofNat (nat_lit 28200960)), (nat_lit 484, Int.ofNat (nat_lit 26075520))]
theorem block003_data_flat086_step : block003_data_flat086 = (CoefficientMerge.fastMerge block003_data_flat082 block003_data_flat085) := by decide +kernel
theorem block003_data_flat086_original : block003_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10108800 : Int) atom0275Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28200960 : Int) atom0276Coded) (CoefficientMerge.scale (26075520 : Int) atom0277Coded))) := by
  rw [block003_data_flat086_step, block003_data_flat082_original, block003_data_flat085_original]
def block003_data_flat087 : CoefficientMerge.Poly := [(nat_lit 434, Int.ofNat (nat_lit 38720880)), (nat_lit 449, Int.ofNat (nat_lit 13514040)), (nat_lit 482, Int.ofNat (nat_lit 10108800)), (nat_lit 483, Int.ofNat (nat_lit 28200960)), (nat_lit 484, Int.ofNat (nat_lit 26075520))]
theorem block003_data_flat087_step : block003_data_flat087 = (CoefficientMerge.fastMerge block003_data_flat081 block003_data_flat086) := by decide +kernel
theorem block003_data_flat087_original : block003_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38720880 : Int) atom0273Coded) (CoefficientMerge.scale (13514040 : Int) atom0274Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10108800 : Int) atom0275Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28200960 : Int) atom0276Coded) (CoefficientMerge.scale (26075520 : Int) atom0277Coded)))) := by
  rw [block003_data_flat087_step, block003_data_flat081_original, block003_data_flat086_original]
def block003_data_flat088 : CoefficientMerge.Poly := [(nat_lit 485, Int.ofNat (nat_lit 23950080))]
theorem block003_data_flat088_step : block003_data_flat088 = (CoefficientMerge.scale (23950080 : Int) atom0278Coded) := by decide +kernel
theorem block003_data_flat088_original : block003_data_flat088 = (CoefficientMerge.scale (23950080 : Int) atom0278Coded) := by
  rw [block003_data_flat088_step]
def block003_data_flat089 : CoefficientMerge.Poly := [(nat_lit 486, Int.ofNat (nat_lit 21824640))]
theorem block003_data_flat089_step : block003_data_flat089 = (CoefficientMerge.scale (21824640 : Int) atom0279Coded) := by decide +kernel
theorem block003_data_flat089_original : block003_data_flat089 = (CoefficientMerge.scale (21824640 : Int) atom0279Coded) := by
  rw [block003_data_flat089_step]
def block003_data_flat090 : CoefficientMerge.Poly := [(nat_lit 485, Int.ofNat (nat_lit 23950080)), (nat_lit 486, Int.ofNat (nat_lit 21824640))]
theorem block003_data_flat090_step : block003_data_flat090 = (CoefficientMerge.fastMerge block003_data_flat088 block003_data_flat089) := by decide +kernel
theorem block003_data_flat090_original : block003_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23950080 : Int) atom0278Coded) (CoefficientMerge.scale (21824640 : Int) atom0279Coded)) := by
  rw [block003_data_flat090_step, block003_data_flat088_original, block003_data_flat089_original]
def block003_data_flat091 : CoefficientMerge.Poly := [(nat_lit 487, Int.ofNat (nat_lit 19699200))]
theorem block003_data_flat091_step : block003_data_flat091 = (CoefficientMerge.scale (19699200 : Int) atom0280Coded) := by decide +kernel
theorem block003_data_flat091_original : block003_data_flat091 = (CoefficientMerge.scale (19699200 : Int) atom0280Coded) := by
  rw [block003_data_flat091_step]
def block003_data_flat092 : CoefficientMerge.Poly := [(nat_lit 488, Int.ofNat (nat_lit 17573760))]
theorem block003_data_flat092_step : block003_data_flat092 = (CoefficientMerge.scale (17573760 : Int) atom0281Coded) := by decide +kernel
theorem block003_data_flat092_original : block003_data_flat092 = (CoefficientMerge.scale (17573760 : Int) atom0281Coded) := by
  rw [block003_data_flat092_step]
def block003_data_flat093 : CoefficientMerge.Poly := [(nat_lit 489, Int.ofNat (nat_lit 42664320))]
theorem block003_data_flat093_step : block003_data_flat093 = (CoefficientMerge.scale (42664320 : Int) atom0282Coded) := by decide +kernel
theorem block003_data_flat093_original : block003_data_flat093 = (CoefficientMerge.scale (42664320 : Int) atom0282Coded) := by
  rw [block003_data_flat093_step]
def block003_data_flat094 : CoefficientMerge.Poly := [(nat_lit 488, Int.ofNat (nat_lit 17573760)), (nat_lit 489, Int.ofNat (nat_lit 42664320))]
theorem block003_data_flat094_step : block003_data_flat094 = (CoefficientMerge.fastMerge block003_data_flat092 block003_data_flat093) := by decide +kernel
theorem block003_data_flat094_original : block003_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17573760 : Int) atom0281Coded) (CoefficientMerge.scale (42664320 : Int) atom0282Coded)) := by
  rw [block003_data_flat094_step, block003_data_flat092_original, block003_data_flat093_original]
def block003_data_flat095 : CoefficientMerge.Poly := [(nat_lit 487, Int.ofNat (nat_lit 19699200)), (nat_lit 488, Int.ofNat (nat_lit 17573760)), (nat_lit 489, Int.ofNat (nat_lit 42664320))]
theorem block003_data_flat095_step : block003_data_flat095 = (CoefficientMerge.fastMerge block003_data_flat091 block003_data_flat094) := by decide +kernel
theorem block003_data_flat095_original : block003_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19699200 : Int) atom0280Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17573760 : Int) atom0281Coded) (CoefficientMerge.scale (42664320 : Int) atom0282Coded))) := by
  rw [block003_data_flat095_step, block003_data_flat091_original, block003_data_flat094_original]
def block003_data_flat096 : CoefficientMerge.Poly := [(nat_lit 485, Int.ofNat (nat_lit 23950080)), (nat_lit 486, Int.ofNat (nat_lit 21824640)), (nat_lit 487, Int.ofNat (nat_lit 19699200)), (nat_lit 488, Int.ofNat (nat_lit 17573760)), (nat_lit 489, Int.ofNat (nat_lit 42664320))]
theorem block003_data_flat096_step : block003_data_flat096 = (CoefficientMerge.fastMerge block003_data_flat090 block003_data_flat095) := by decide +kernel
theorem block003_data_flat096_original : block003_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23950080 : Int) atom0278Coded) (CoefficientMerge.scale (21824640 : Int) atom0279Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19699200 : Int) atom0280Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17573760 : Int) atom0281Coded) (CoefficientMerge.scale (42664320 : Int) atom0282Coded)))) := by
  rw [block003_data_flat096_step, block003_data_flat090_original, block003_data_flat095_original]
def block003_data_flat097 : CoefficientMerge.Poly := [(nat_lit 434, Int.ofNat (nat_lit 38720880)), (nat_lit 449, Int.ofNat (nat_lit 13514040)), (nat_lit 482, Int.ofNat (nat_lit 10108800)), (nat_lit 483, Int.ofNat (nat_lit 28200960)), (nat_lit 484, Int.ofNat (nat_lit 26075520)), (nat_lit 485, Int.ofNat (nat_lit 23950080)), (nat_lit 486, Int.ofNat (nat_lit 21824640)), (nat_lit 487, Int.ofNat (nat_lit 19699200)), (nat_lit 488, Int.ofNat (nat_lit 17573760)), (nat_lit 489, Int.ofNat (nat_lit 42664320))]
theorem block003_data_flat097_step : block003_data_flat097 = (CoefficientMerge.fastMerge block003_data_flat087 block003_data_flat096) := by decide +kernel
theorem block003_data_flat097_original : block003_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38720880 : Int) atom0273Coded) (CoefficientMerge.scale (13514040 : Int) atom0274Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10108800 : Int) atom0275Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28200960 : Int) atom0276Coded) (CoefficientMerge.scale (26075520 : Int) atom0277Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23950080 : Int) atom0278Coded) (CoefficientMerge.scale (21824640 : Int) atom0279Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19699200 : Int) atom0280Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17573760 : Int) atom0281Coded) (CoefficientMerge.scale (42664320 : Int) atom0282Coded))))) := by
  rw [block003_data_flat097_step, block003_data_flat087_original, block003_data_flat096_original]
def block003_data_flat098 : CoefficientMerge.Poly := [(nat_lit 490, Int.ofNat (nat_lit 13322880))]
theorem block003_data_flat098_step : block003_data_flat098 = (CoefficientMerge.scale (13322880 : Int) atom0283Coded) := by decide +kernel
theorem block003_data_flat098_original : block003_data_flat098 = (CoefficientMerge.scale (13322880 : Int) atom0283Coded) := by
  rw [block003_data_flat098_step]
def block003_data_flat099 : CoefficientMerge.Poly := [(nat_lit 491, Int.ofNat (nat_lit 23926320))]
theorem block003_data_flat099_step : block003_data_flat099 = (CoefficientMerge.scale (23926320 : Int) atom0284Coded) := by decide +kernel
theorem block003_data_flat099_original : block003_data_flat099 = (CoefficientMerge.scale (23926320 : Int) atom0284Coded) := by
  rw [block003_data_flat099_step]
def block003_data_flat100 : CoefficientMerge.Poly := [(nat_lit 490, Int.ofNat (nat_lit 13322880)), (nat_lit 491, Int.ofNat (nat_lit 23926320))]
theorem block003_data_flat100_step : block003_data_flat100 = (CoefficientMerge.fastMerge block003_data_flat098 block003_data_flat099) := by decide +kernel
theorem block003_data_flat100_original : block003_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13322880 : Int) atom0283Coded) (CoefficientMerge.scale (23926320 : Int) atom0284Coded)) := by
  rw [block003_data_flat100_step, block003_data_flat098_original, block003_data_flat099_original]
def block003_data_flat101 : CoefficientMerge.Poly := [(nat_lit 492, Int.ofNat (nat_lit 9072000))]
theorem block003_data_flat101_step : block003_data_flat101 = (CoefficientMerge.scale (9072000 : Int) atom0285Coded) := by decide +kernel
theorem block003_data_flat101_original : block003_data_flat101 = (CoefficientMerge.scale (9072000 : Int) atom0285Coded) := by
  rw [block003_data_flat101_step]
def block003_data_flat102 : CoefficientMerge.Poly := [(nat_lit 494, Int.ofNat (nat_lit 13262400))]
theorem block003_data_flat102_step : block003_data_flat102 = (CoefficientMerge.scale (13262400 : Int) atom0286Coded) := by decide +kernel
theorem block003_data_flat102_original : block003_data_flat102 = (CoefficientMerge.scale (13262400 : Int) atom0286Coded) := by
  rw [block003_data_flat102_step]
def block003_data_flat103 : CoefficientMerge.Poly := [(nat_lit 498, Int.ofNat (nat_lit 21772800))]
theorem block003_data_flat103_step : block003_data_flat103 = (CoefficientMerge.scale (21772800 : Int) atom0287Coded) := by decide +kernel
theorem block003_data_flat103_original : block003_data_flat103 = (CoefficientMerge.scale (21772800 : Int) atom0287Coded) := by
  rw [block003_data_flat103_step]
def block003_data_flat104 : CoefficientMerge.Poly := [(nat_lit 494, Int.ofNat (nat_lit 13262400)), (nat_lit 498, Int.ofNat (nat_lit 21772800))]
theorem block003_data_flat104_step : block003_data_flat104 = (CoefficientMerge.fastMerge block003_data_flat102 block003_data_flat103) := by decide +kernel
theorem block003_data_flat104_original : block003_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13262400 : Int) atom0286Coded) (CoefficientMerge.scale (21772800 : Int) atom0287Coded)) := by
  rw [block003_data_flat104_step, block003_data_flat102_original, block003_data_flat103_original]
def block003_data_flat105 : CoefficientMerge.Poly := [(nat_lit 492, Int.ofNat (nat_lit 9072000)), (nat_lit 494, Int.ofNat (nat_lit 13262400)), (nat_lit 498, Int.ofNat (nat_lit 21772800))]
theorem block003_data_flat105_step : block003_data_flat105 = (CoefficientMerge.fastMerge block003_data_flat101 block003_data_flat104) := by decide +kernel
theorem block003_data_flat105_original : block003_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9072000 : Int) atom0285Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13262400 : Int) atom0286Coded) (CoefficientMerge.scale (21772800 : Int) atom0287Coded))) := by
  rw [block003_data_flat105_step, block003_data_flat101_original, block003_data_flat104_original]
def block003_data_flat106 : CoefficientMerge.Poly := [(nat_lit 490, Int.ofNat (nat_lit 13322880)), (nat_lit 491, Int.ofNat (nat_lit 23926320)), (nat_lit 492, Int.ofNat (nat_lit 9072000)), (nat_lit 494, Int.ofNat (nat_lit 13262400)), (nat_lit 498, Int.ofNat (nat_lit 21772800))]
theorem block003_data_flat106_step : block003_data_flat106 = (CoefficientMerge.fastMerge block003_data_flat100 block003_data_flat105) := by decide +kernel
theorem block003_data_flat106_original : block003_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13322880 : Int) atom0283Coded) (CoefficientMerge.scale (23926320 : Int) atom0284Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9072000 : Int) atom0285Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13262400 : Int) atom0286Coded) (CoefficientMerge.scale (21772800 : Int) atom0287Coded)))) := by
  rw [block003_data_flat106_step, block003_data_flat100_original, block003_data_flat105_original]
def block003_data_flat107 : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 40072320))]
theorem block003_data_flat107_step : block003_data_flat107 = (CoefficientMerge.scale (40072320 : Int) atom0288Coded) := by decide +kernel
theorem block003_data_flat107_original : block003_data_flat107 = (CoefficientMerge.scale (40072320 : Int) atom0288Coded) := by
  rw [block003_data_flat107_step]
def block003_data_flat108 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 39398400))]
theorem block003_data_flat108_step : block003_data_flat108 = (CoefficientMerge.scale (39398400 : Int) atom0289Coded) := by decide +kernel
theorem block003_data_flat108_original : block003_data_flat108 = (CoefficientMerge.scale (39398400 : Int) atom0289Coded) := by
  rw [block003_data_flat108_step]
def block003_data_flat109 : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 40072320)), (nat_lit 500, Int.ofNat (nat_lit 39398400))]
theorem block003_data_flat109_step : block003_data_flat109 = (CoefficientMerge.fastMerge block003_data_flat107 block003_data_flat108) := by decide +kernel
theorem block003_data_flat109_original : block003_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40072320 : Int) atom0288Coded) (CoefficientMerge.scale (39398400 : Int) atom0289Coded)) := by
  rw [block003_data_flat109_step, block003_data_flat107_original, block003_data_flat108_original]
def block003_data_flat110 : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 38724480))]
theorem block003_data_flat110_step : block003_data_flat110 = (CoefficientMerge.scale (38724480 : Int) atom0290Coded) := by decide +kernel
theorem block003_data_flat110_original : block003_data_flat110 = (CoefficientMerge.scale (38724480 : Int) atom0290Coded) := by
  rw [block003_data_flat110_step]
def block003_data_flat111 : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 38499840))]
theorem block003_data_flat111_step : block003_data_flat111 = (CoefficientMerge.scale (38499840 : Int) atom0291Coded) := by decide +kernel
theorem block003_data_flat111_original : block003_data_flat111 = (CoefficientMerge.scale (38499840 : Int) atom0291Coded) := by
  rw [block003_data_flat111_step]
def block003_data_flat112 : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 38275200))]
theorem block003_data_flat112_step : block003_data_flat112 = (CoefficientMerge.scale (38275200 : Int) atom0292Coded) := by decide +kernel
theorem block003_data_flat112_original : block003_data_flat112 = (CoefficientMerge.scale (38275200 : Int) atom0292Coded) := by
  rw [block003_data_flat112_step]
def block003_data_flat113 : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 38499840)), (nat_lit 503, Int.ofNat (nat_lit 38275200))]
theorem block003_data_flat113_step : block003_data_flat113 = (CoefficientMerge.fastMerge block003_data_flat111 block003_data_flat112) := by decide +kernel
theorem block003_data_flat113_original : block003_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38499840 : Int) atom0291Coded) (CoefficientMerge.scale (38275200 : Int) atom0292Coded)) := by
  rw [block003_data_flat113_step, block003_data_flat111_original, block003_data_flat112_original]
def block003_data_flat114 : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 38724480)), (nat_lit 502, Int.ofNat (nat_lit 38499840)), (nat_lit 503, Int.ofNat (nat_lit 38275200))]
theorem block003_data_flat114_step : block003_data_flat114 = (CoefficientMerge.fastMerge block003_data_flat110 block003_data_flat113) := by decide +kernel
theorem block003_data_flat114_original : block003_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38724480 : Int) atom0290Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38499840 : Int) atom0291Coded) (CoefficientMerge.scale (38275200 : Int) atom0292Coded))) := by
  rw [block003_data_flat114_step, block003_data_flat110_original, block003_data_flat113_original]
def block003_data_flat115 : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 40072320)), (nat_lit 500, Int.ofNat (nat_lit 39398400)), (nat_lit 501, Int.ofNat (nat_lit 38724480)), (nat_lit 502, Int.ofNat (nat_lit 38499840)), (nat_lit 503, Int.ofNat (nat_lit 38275200))]
theorem block003_data_flat115_step : block003_data_flat115 = (CoefficientMerge.fastMerge block003_data_flat109 block003_data_flat114) := by decide +kernel
theorem block003_data_flat115_original : block003_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40072320 : Int) atom0288Coded) (CoefficientMerge.scale (39398400 : Int) atom0289Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38724480 : Int) atom0290Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38499840 : Int) atom0291Coded) (CoefficientMerge.scale (38275200 : Int) atom0292Coded)))) := by
  rw [block003_data_flat115_step, block003_data_flat109_original, block003_data_flat114_original]
def block003_data_flat116 : CoefficientMerge.Poly := [(nat_lit 490, Int.ofNat (nat_lit 13322880)), (nat_lit 491, Int.ofNat (nat_lit 23926320)), (nat_lit 492, Int.ofNat (nat_lit 9072000)), (nat_lit 494, Int.ofNat (nat_lit 13262400)), (nat_lit 498, Int.ofNat (nat_lit 21772800)), (nat_lit 499, Int.ofNat (nat_lit 40072320)), (nat_lit 500, Int.ofNat (nat_lit 39398400)), (nat_lit 501, Int.ofNat (nat_lit 38724480)), (nat_lit 502, Int.ofNat (nat_lit 38499840)), (nat_lit 503, Int.ofNat (nat_lit 38275200))]
theorem block003_data_flat116_step : block003_data_flat116 = (CoefficientMerge.fastMerge block003_data_flat106 block003_data_flat115) := by decide +kernel
theorem block003_data_flat116_original : block003_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13322880 : Int) atom0283Coded) (CoefficientMerge.scale (23926320 : Int) atom0284Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9072000 : Int) atom0285Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13262400 : Int) atom0286Coded) (CoefficientMerge.scale (21772800 : Int) atom0287Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40072320 : Int) atom0288Coded) (CoefficientMerge.scale (39398400 : Int) atom0289Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38724480 : Int) atom0290Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38499840 : Int) atom0291Coded) (CoefficientMerge.scale (38275200 : Int) atom0292Coded))))) := by
  rw [block003_data_flat116_step, block003_data_flat106_original, block003_data_flat115_original]
def block003_data_flat117 : CoefficientMerge.Poly := [(nat_lit 434, Int.ofNat (nat_lit 38720880)), (nat_lit 449, Int.ofNat (nat_lit 13514040)), (nat_lit 482, Int.ofNat (nat_lit 10108800)), (nat_lit 483, Int.ofNat (nat_lit 28200960)), (nat_lit 484, Int.ofNat (nat_lit 26075520)), (nat_lit 485, Int.ofNat (nat_lit 23950080)), (nat_lit 486, Int.ofNat (nat_lit 21824640)), (nat_lit 487, Int.ofNat (nat_lit 19699200)), (nat_lit 488, Int.ofNat (nat_lit 17573760)), (nat_lit 489, Int.ofNat (nat_lit 42664320)), (nat_lit 490, Int.ofNat (nat_lit 13322880)), (nat_lit 491, Int.ofNat (nat_lit 23926320)), (nat_lit 492, Int.ofNat (nat_lit 9072000)), (nat_lit 494, Int.ofNat (nat_lit 13262400)), (nat_lit 498, Int.ofNat (nat_lit 21772800)), (nat_lit 499, Int.ofNat (nat_lit 40072320)), (nat_lit 500, Int.ofNat (nat_lit 39398400)), (nat_lit 501, Int.ofNat (nat_lit 38724480)), (nat_lit 502, Int.ofNat (nat_lit 38499840)), (nat_lit 503, Int.ofNat (nat_lit 38275200))]
theorem block003_data_flat117_step : block003_data_flat117 = (CoefficientMerge.fastMerge block003_data_flat097 block003_data_flat116) := by decide +kernel
theorem block003_data_flat117_original : block003_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38720880 : Int) atom0273Coded) (CoefficientMerge.scale (13514040 : Int) atom0274Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10108800 : Int) atom0275Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28200960 : Int) atom0276Coded) (CoefficientMerge.scale (26075520 : Int) atom0277Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23950080 : Int) atom0278Coded) (CoefficientMerge.scale (21824640 : Int) atom0279Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19699200 : Int) atom0280Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17573760 : Int) atom0281Coded) (CoefficientMerge.scale (42664320 : Int) atom0282Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13322880 : Int) atom0283Coded) (CoefficientMerge.scale (23926320 : Int) atom0284Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9072000 : Int) atom0285Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13262400 : Int) atom0286Coded) (CoefficientMerge.scale (21772800 : Int) atom0287Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40072320 : Int) atom0288Coded) (CoefficientMerge.scale (39398400 : Int) atom0289Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38724480 : Int) atom0290Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38499840 : Int) atom0291Coded) (CoefficientMerge.scale (38275200 : Int) atom0292Coded)))))) := by
  rw [block003_data_flat117_step, block003_data_flat097_original, block003_data_flat116_original]
def block003_data_flat118 : CoefficientMerge.Poly := [(nat_lit 504, Int.ofNat (nat_lit 91134720))]
theorem block003_data_flat118_step : block003_data_flat118 = (CoefficientMerge.scale (91134720 : Int) atom0293Coded) := by decide +kernel
theorem block003_data_flat118_original : block003_data_flat118 = (CoefficientMerge.scale (91134720 : Int) atom0293Coded) := by
  rw [block003_data_flat118_step]
def block003_data_flat119 : CoefficientMerge.Poly := [(nat_lit 505, Int.ofNat (nat_lit 38350800))]
theorem block003_data_flat119_step : block003_data_flat119 = (CoefficientMerge.scale (38350800 : Int) atom0294Coded) := by decide +kernel
theorem block003_data_flat119_original : block003_data_flat119 = (CoefficientMerge.scale (38350800 : Int) atom0294Coded) := by
  rw [block003_data_flat119_step]
def block003_data_flat120 : CoefficientMerge.Poly := [(nat_lit 504, Int.ofNat (nat_lit 91134720)), (nat_lit 505, Int.ofNat (nat_lit 38350800))]
theorem block003_data_flat120_step : block003_data_flat120 = (CoefficientMerge.fastMerge block003_data_flat118 block003_data_flat119) := by decide +kernel
theorem block003_data_flat120_original : block003_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (91134720 : Int) atom0293Coded) (CoefficientMerge.scale (38350800 : Int) atom0294Coded)) := by
  rw [block003_data_flat120_step, block003_data_flat118_original, block003_data_flat119_original]
def block003_data_flat121 : CoefficientMerge.Poly := [(nat_lit 506, Int.ofNat (nat_lit 60812640))]
theorem block003_data_flat121_step : block003_data_flat121 = (CoefficientMerge.scale (60812640 : Int) atom0295Coded) := by decide +kernel
theorem block003_data_flat121_original : block003_data_flat121 = (CoefficientMerge.scale (60812640 : Int) atom0295Coded) := by
  rw [block003_data_flat121_step]
def block003_data_flat122 : CoefficientMerge.Poly := [(nat_lit 507, Int.ofNat (nat_lit 38951280))]
theorem block003_data_flat122_step : block003_data_flat122 = (CoefficientMerge.scale (38951280 : Int) atom0296Coded) := by decide +kernel
theorem block003_data_flat122_original : block003_data_flat122 = (CoefficientMerge.scale (38951280 : Int) atom0296Coded) := by
  rw [block003_data_flat122_step]
def block003_data_flat123 : CoefficientMerge.Poly := [(nat_lit 508, Int.ofNat (nat_lit 32479920))]
theorem block003_data_flat123_step : block003_data_flat123 = (CoefficientMerge.scale (32479920 : Int) atom0297Coded) := by decide +kernel
theorem block003_data_flat123_original : block003_data_flat123 = (CoefficientMerge.scale (32479920 : Int) atom0297Coded) := by
  rw [block003_data_flat123_step]
def block003_data_flat124 : CoefficientMerge.Poly := [(nat_lit 507, Int.ofNat (nat_lit 38951280)), (nat_lit 508, Int.ofNat (nat_lit 32479920))]
theorem block003_data_flat124_step : block003_data_flat124 = (CoefficientMerge.fastMerge block003_data_flat122 block003_data_flat123) := by decide +kernel
theorem block003_data_flat124_original : block003_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38951280 : Int) atom0296Coded) (CoefficientMerge.scale (32479920 : Int) atom0297Coded)) := by
  rw [block003_data_flat124_step, block003_data_flat122_original, block003_data_flat123_original]
def block003_data_flat125 : CoefficientMerge.Poly := [(nat_lit 506, Int.ofNat (nat_lit 60812640)), (nat_lit 507, Int.ofNat (nat_lit 38951280)), (nat_lit 508, Int.ofNat (nat_lit 32479920))]
theorem block003_data_flat125_step : block003_data_flat125 = (CoefficientMerge.fastMerge block003_data_flat121 block003_data_flat124) := by decide +kernel
theorem block003_data_flat125_original : block003_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (60812640 : Int) atom0295Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38951280 : Int) atom0296Coded) (CoefficientMerge.scale (32479920 : Int) atom0297Coded))) := by
  rw [block003_data_flat125_step, block003_data_flat121_original, block003_data_flat124_original]
def block003_data_flat126 : CoefficientMerge.Poly := [(nat_lit 504, Int.ofNat (nat_lit 91134720)), (nat_lit 505, Int.ofNat (nat_lit 38350800)), (nat_lit 506, Int.ofNat (nat_lit 60812640)), (nat_lit 507, Int.ofNat (nat_lit 38951280)), (nat_lit 508, Int.ofNat (nat_lit 32479920))]
theorem block003_data_flat126_step : block003_data_flat126 = (CoefficientMerge.fastMerge block003_data_flat120 block003_data_flat125) := by decide +kernel
theorem block003_data_flat126_original : block003_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91134720 : Int) atom0293Coded) (CoefficientMerge.scale (38350800 : Int) atom0294Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60812640 : Int) atom0295Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38951280 : Int) atom0296Coded) (CoefficientMerge.scale (32479920 : Int) atom0297Coded)))) := by
  rw [block003_data_flat126_step, block003_data_flat120_original, block003_data_flat125_original]
def block003_data_flat127 : CoefficientMerge.Poly := [(nat_lit 509, Int.ofNat (nat_lit 48342960))]
theorem block003_data_flat127_step : block003_data_flat127 = (CoefficientMerge.scale (48342960 : Int) atom0298Coded) := by decide +kernel
theorem block003_data_flat127_original : block003_data_flat127 = (CoefficientMerge.scale (48342960 : Int) atom0298Coded) := by
  rw [block003_data_flat127_step]
def block003_data_flat128 : CoefficientMerge.Poly := [(nat_lit 514, Int.ofNat (nat_lit 27296640))]
theorem block003_data_flat128_step : block003_data_flat128 = (CoefficientMerge.scale (27296640 : Int) atom0299Coded) := by decide +kernel
theorem block003_data_flat128_original : block003_data_flat128 = (CoefficientMerge.scale (27296640 : Int) atom0299Coded) := by
  rw [block003_data_flat128_step]
def block003_data_flat129 : CoefficientMerge.Poly := [(nat_lit 509, Int.ofNat (nat_lit 48342960)), (nat_lit 514, Int.ofNat (nat_lit 27296640))]
theorem block003_data_flat129_step : block003_data_flat129 = (CoefficientMerge.fastMerge block003_data_flat127 block003_data_flat128) := by decide +kernel
theorem block003_data_flat129_original : block003_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48342960 : Int) atom0298Coded) (CoefficientMerge.scale (27296640 : Int) atom0299Coded)) := by
  rw [block003_data_flat129_step, block003_data_flat127_original, block003_data_flat128_original]
def block003_data_flat130 : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 46281600))]
theorem block003_data_flat130_step : block003_data_flat130 = (CoefficientMerge.scale (46281600 : Int) atom0300Coded) := by decide +kernel
theorem block003_data_flat130_original : block003_data_flat130 = (CoefficientMerge.scale (46281600 : Int) atom0300Coded) := by
  rw [block003_data_flat130_step]
def block003_data_flat131 : CoefficientMerge.Poly := [(nat_lit 516, Int.ofNat (nat_lit 46765440))]
theorem block003_data_flat131_step : block003_data_flat131 = (CoefficientMerge.scale (46765440 : Int) atom0301Coded) := by decide +kernel
theorem block003_data_flat131_original : block003_data_flat131 = (CoefficientMerge.scale (46765440 : Int) atom0301Coded) := by
  rw [block003_data_flat131_step]
def block003_data_flat132 : CoefficientMerge.Poly := [(nat_lit 517, Int.ofNat (nat_lit 47249280))]
theorem block003_data_flat132_step : block003_data_flat132 = (CoefficientMerge.scale (47249280 : Int) atom0302Coded) := by decide +kernel
theorem block003_data_flat132_original : block003_data_flat132 = (CoefficientMerge.scale (47249280 : Int) atom0302Coded) := by
  rw [block003_data_flat132_step]
def block003_data_flat133 : CoefficientMerge.Poly := [(nat_lit 516, Int.ofNat (nat_lit 46765440)), (nat_lit 517, Int.ofNat (nat_lit 47249280))]
theorem block003_data_flat133_step : block003_data_flat133 = (CoefficientMerge.fastMerge block003_data_flat131 block003_data_flat132) := by decide +kernel
theorem block003_data_flat133_original : block003_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46765440 : Int) atom0301Coded) (CoefficientMerge.scale (47249280 : Int) atom0302Coded)) := by
  rw [block003_data_flat133_step, block003_data_flat131_original, block003_data_flat132_original]
def block003_data_flat134 : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 46281600)), (nat_lit 516, Int.ofNat (nat_lit 46765440)), (nat_lit 517, Int.ofNat (nat_lit 47249280))]
theorem block003_data_flat134_step : block003_data_flat134 = (CoefficientMerge.fastMerge block003_data_flat130 block003_data_flat133) := by decide +kernel
theorem block003_data_flat134_original : block003_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46281600 : Int) atom0300Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46765440 : Int) atom0301Coded) (CoefficientMerge.scale (47249280 : Int) atom0302Coded))) := by
  rw [block003_data_flat134_step, block003_data_flat130_original, block003_data_flat133_original]
def block003_data_flat135 : CoefficientMerge.Poly := [(nat_lit 509, Int.ofNat (nat_lit 48342960)), (nat_lit 514, Int.ofNat (nat_lit 27296640)), (nat_lit 515, Int.ofNat (nat_lit 46281600)), (nat_lit 516, Int.ofNat (nat_lit 46765440)), (nat_lit 517, Int.ofNat (nat_lit 47249280))]
theorem block003_data_flat135_step : block003_data_flat135 = (CoefficientMerge.fastMerge block003_data_flat129 block003_data_flat134) := by decide +kernel
theorem block003_data_flat135_original : block003_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48342960 : Int) atom0298Coded) (CoefficientMerge.scale (27296640 : Int) atom0299Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46281600 : Int) atom0300Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46765440 : Int) atom0301Coded) (CoefficientMerge.scale (47249280 : Int) atom0302Coded)))) := by
  rw [block003_data_flat135_step, block003_data_flat129_original, block003_data_flat134_original]
def block003_data_flat136 : CoefficientMerge.Poly := [(nat_lit 504, Int.ofNat (nat_lit 91134720)), (nat_lit 505, Int.ofNat (nat_lit 38350800)), (nat_lit 506, Int.ofNat (nat_lit 60812640)), (nat_lit 507, Int.ofNat (nat_lit 38951280)), (nat_lit 508, Int.ofNat (nat_lit 32479920)), (nat_lit 509, Int.ofNat (nat_lit 48342960)), (nat_lit 514, Int.ofNat (nat_lit 27296640)), (nat_lit 515, Int.ofNat (nat_lit 46281600)), (nat_lit 516, Int.ofNat (nat_lit 46765440)), (nat_lit 517, Int.ofNat (nat_lit 47249280))]
theorem block003_data_flat136_step : block003_data_flat136 = (CoefficientMerge.fastMerge block003_data_flat126 block003_data_flat135) := by decide +kernel
theorem block003_data_flat136_original : block003_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91134720 : Int) atom0293Coded) (CoefficientMerge.scale (38350800 : Int) atom0294Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60812640 : Int) atom0295Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38951280 : Int) atom0296Coded) (CoefficientMerge.scale (32479920 : Int) atom0297Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48342960 : Int) atom0298Coded) (CoefficientMerge.scale (27296640 : Int) atom0299Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46281600 : Int) atom0300Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46765440 : Int) atom0301Coded) (CoefficientMerge.scale (47249280 : Int) atom0302Coded))))) := by
  rw [block003_data_flat136_step, block003_data_flat126_original, block003_data_flat135_original]
def block003_data_flat137 : CoefficientMerge.Poly := [(nat_lit 518, Int.ofNat (nat_lit 47733120))]
theorem block003_data_flat137_step : block003_data_flat137 = (CoefficientMerge.scale (47733120 : Int) atom0303Coded) := by decide +kernel
theorem block003_data_flat137_original : block003_data_flat137 = (CoefficientMerge.scale (47733120 : Int) atom0303Coded) := by
  rw [block003_data_flat137_step]
def block003_data_flat138 : CoefficientMerge.Poly := [(nat_lit 519, Int.ofNat (nat_lit 96940800))]
theorem block003_data_flat138_step : block003_data_flat138 = (CoefficientMerge.scale (96940800 : Int) atom0304Coded) := by decide +kernel
theorem block003_data_flat138_original : block003_data_flat138 = (CoefficientMerge.scale (96940800 : Int) atom0304Coded) := by
  rw [block003_data_flat138_step]
def block003_data_flat139 : CoefficientMerge.Poly := [(nat_lit 518, Int.ofNat (nat_lit 47733120)), (nat_lit 519, Int.ofNat (nat_lit 96940800))]
theorem block003_data_flat139_step : block003_data_flat139 = (CoefficientMerge.fastMerge block003_data_flat137 block003_data_flat138) := by decide +kernel
theorem block003_data_flat139_original : block003_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47733120 : Int) atom0303Coded) (CoefficientMerge.scale (96940800 : Int) atom0304Coded)) := by
  rw [block003_data_flat139_step, block003_data_flat137_original, block003_data_flat138_original]
def block003_data_flat140 : CoefficientMerge.Poly := [(nat_lit 520, Int.ofNat (nat_lit 53688240))]
theorem block003_data_flat140_step : block003_data_flat140 = (CoefficientMerge.scale (53688240 : Int) atom0305Coded) := by decide +kernel
theorem block003_data_flat140_original : block003_data_flat140 = (CoefficientMerge.scale (53688240 : Int) atom0305Coded) := by
  rw [block003_data_flat140_step]
def block003_data_flat141 : CoefficientMerge.Poly := [(nat_lit 521, Int.ofNat (nat_lit 73772640))]
theorem block003_data_flat141_step : block003_data_flat141 = (CoefficientMerge.scale (73772640 : Int) atom0306Coded) := by decide +kernel
theorem block003_data_flat141_original : block003_data_flat141 = (CoefficientMerge.scale (73772640 : Int) atom0306Coded) := by
  rw [block003_data_flat141_step]
def block003_data_flat142 : CoefficientMerge.Poly := [(nat_lit 522, Int.ofNat (nat_lit 64630800))]
theorem block003_data_flat142_step : block003_data_flat142 = (CoefficientMerge.scale (64630800 : Int) atom0307Coded) := by decide +kernel
theorem block003_data_flat142_original : block003_data_flat142 = (CoefficientMerge.scale (64630800 : Int) atom0307Coded) := by
  rw [block003_data_flat142_step]
def block003_data_flat143 : CoefficientMerge.Poly := [(nat_lit 521, Int.ofNat (nat_lit 73772640)), (nat_lit 522, Int.ofNat (nat_lit 64630800))]
theorem block003_data_flat143_step : block003_data_flat143 = (CoefficientMerge.fastMerge block003_data_flat141 block003_data_flat142) := by decide +kernel
theorem block003_data_flat143_original : block003_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (73772640 : Int) atom0306Coded) (CoefficientMerge.scale (64630800 : Int) atom0307Coded)) := by
  rw [block003_data_flat143_step, block003_data_flat141_original, block003_data_flat142_original]
def block003_data_flat144 : CoefficientMerge.Poly := [(nat_lit 520, Int.ofNat (nat_lit 53688240)), (nat_lit 521, Int.ofNat (nat_lit 73772640)), (nat_lit 522, Int.ofNat (nat_lit 64630800))]
theorem block003_data_flat144_step : block003_data_flat144 = (CoefficientMerge.fastMerge block003_data_flat140 block003_data_flat143) := by decide +kernel
theorem block003_data_flat144_original : block003_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53688240 : Int) atom0305Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73772640 : Int) atom0306Coded) (CoefficientMerge.scale (64630800 : Int) atom0307Coded))) := by
  rw [block003_data_flat144_step, block003_data_flat140_original, block003_data_flat143_original]
def block003_data_flat145 : CoefficientMerge.Poly := [(nat_lit 518, Int.ofNat (nat_lit 47733120)), (nat_lit 519, Int.ofNat (nat_lit 96940800)), (nat_lit 520, Int.ofNat (nat_lit 53688240)), (nat_lit 521, Int.ofNat (nat_lit 73772640)), (nat_lit 522, Int.ofNat (nat_lit 64630800))]
theorem block003_data_flat145_step : block003_data_flat145 = (CoefficientMerge.fastMerge block003_data_flat139 block003_data_flat144) := by decide +kernel
theorem block003_data_flat145_original : block003_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47733120 : Int) atom0303Coded) (CoefficientMerge.scale (96940800 : Int) atom0304Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53688240 : Int) atom0305Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73772640 : Int) atom0306Coded) (CoefficientMerge.scale (64630800 : Int) atom0307Coded)))) := by
  rw [block003_data_flat145_step, block003_data_flat139_original, block003_data_flat144_original]
def block003_data_flat146 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 64818000))]
theorem block003_data_flat146_step : block003_data_flat146 = (CoefficientMerge.scale (64818000 : Int) atom0308Coded) := by decide +kernel
theorem block003_data_flat146_original : block003_data_flat146 = (CoefficientMerge.scale (64818000 : Int) atom0308Coded) := by
  rw [block003_data_flat146_step]
def block003_data_flat147 : CoefficientMerge.Poly := [(nat_lit 524, Int.ofNat (nat_lit 87339600))]
theorem block003_data_flat147_step : block003_data_flat147 = (CoefficientMerge.scale (87339600 : Int) atom0309Coded) := by decide +kernel
theorem block003_data_flat147_original : block003_data_flat147 = (CoefficientMerge.scale (87339600 : Int) atom0309Coded) := by
  rw [block003_data_flat147_step]
def block003_data_flat148 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 64818000)), (nat_lit 524, Int.ofNat (nat_lit 87339600))]
theorem block003_data_flat148_step : block003_data_flat148 = (CoefficientMerge.fastMerge block003_data_flat146 block003_data_flat147) := by decide +kernel
theorem block003_data_flat148_original : block003_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64818000 : Int) atom0308Coded) (CoefficientMerge.scale (87339600 : Int) atom0309Coded)) := by
  rw [block003_data_flat148_step, block003_data_flat146_original, block003_data_flat147_original]
def block003_data_flat149 : CoefficientMerge.Poly := [(nat_lit 530, Int.ofNat (nat_lit 31582080))]
theorem block003_data_flat149_step : block003_data_flat149 = (CoefficientMerge.scale (31582080 : Int) atom0310Coded) := by decide +kernel
theorem block003_data_flat149_original : block003_data_flat149 = (CoefficientMerge.scale (31582080 : Int) atom0310Coded) := by
  rw [block003_data_flat149_step]
def block003_data_flat150 : CoefficientMerge.Poly := [(nat_lit 531, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat150_step : block003_data_flat150 = (CoefficientMerge.scale (61263360 : Int) atom0311Coded) := by decide +kernel
theorem block003_data_flat150_original : block003_data_flat150 = (CoefficientMerge.scale (61263360 : Int) atom0311Coded) := by
  rw [block003_data_flat150_step]
def block003_data_flat151 : CoefficientMerge.Poly := [(nat_lit 532, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat151_step : block003_data_flat151 = (CoefficientMerge.scale (61263360 : Int) atom0312Coded) := by decide +kernel
theorem block003_data_flat151_original : block003_data_flat151 = (CoefficientMerge.scale (61263360 : Int) atom0312Coded) := by
  rw [block003_data_flat151_step]
def block003_data_flat152 : CoefficientMerge.Poly := [(nat_lit 531, Int.ofNat (nat_lit 61263360)), (nat_lit 532, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat152_step : block003_data_flat152 = (CoefficientMerge.fastMerge block003_data_flat150 block003_data_flat151) := by decide +kernel
theorem block003_data_flat152_original : block003_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0311Coded) (CoefficientMerge.scale (61263360 : Int) atom0312Coded)) := by
  rw [block003_data_flat152_step, block003_data_flat150_original, block003_data_flat151_original]
def block003_data_flat153 : CoefficientMerge.Poly := [(nat_lit 530, Int.ofNat (nat_lit 31582080)), (nat_lit 531, Int.ofNat (nat_lit 61263360)), (nat_lit 532, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat153_step : block003_data_flat153 = (CoefficientMerge.fastMerge block003_data_flat149 block003_data_flat152) := by decide +kernel
theorem block003_data_flat153_original : block003_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31582080 : Int) atom0310Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0311Coded) (CoefficientMerge.scale (61263360 : Int) atom0312Coded))) := by
  rw [block003_data_flat153_step, block003_data_flat149_original, block003_data_flat152_original]
def block003_data_flat154 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 64818000)), (nat_lit 524, Int.ofNat (nat_lit 87339600)), (nat_lit 530, Int.ofNat (nat_lit 31582080)), (nat_lit 531, Int.ofNat (nat_lit 61263360)), (nat_lit 532, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat154_step : block003_data_flat154 = (CoefficientMerge.fastMerge block003_data_flat148 block003_data_flat153) := by decide +kernel
theorem block003_data_flat154_original : block003_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64818000 : Int) atom0308Coded) (CoefficientMerge.scale (87339600 : Int) atom0309Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31582080 : Int) atom0310Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0311Coded) (CoefficientMerge.scale (61263360 : Int) atom0312Coded)))) := by
  rw [block003_data_flat154_step, block003_data_flat148_original, block003_data_flat153_original]
def block003_data_flat155 : CoefficientMerge.Poly := [(nat_lit 518, Int.ofNat (nat_lit 47733120)), (nat_lit 519, Int.ofNat (nat_lit 96940800)), (nat_lit 520, Int.ofNat (nat_lit 53688240)), (nat_lit 521, Int.ofNat (nat_lit 73772640)), (nat_lit 522, Int.ofNat (nat_lit 64630800)), (nat_lit 523, Int.ofNat (nat_lit 64818000)), (nat_lit 524, Int.ofNat (nat_lit 87339600)), (nat_lit 530, Int.ofNat (nat_lit 31582080)), (nat_lit 531, Int.ofNat (nat_lit 61263360)), (nat_lit 532, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat155_step : block003_data_flat155 = (CoefficientMerge.fastMerge block003_data_flat145 block003_data_flat154) := by decide +kernel
theorem block003_data_flat155_original : block003_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47733120 : Int) atom0303Coded) (CoefficientMerge.scale (96940800 : Int) atom0304Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53688240 : Int) atom0305Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73772640 : Int) atom0306Coded) (CoefficientMerge.scale (64630800 : Int) atom0307Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64818000 : Int) atom0308Coded) (CoefficientMerge.scale (87339600 : Int) atom0309Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31582080 : Int) atom0310Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0311Coded) (CoefficientMerge.scale (61263360 : Int) atom0312Coded))))) := by
  rw [block003_data_flat155_step, block003_data_flat145_original, block003_data_flat154_original]
def block003_data_flat156 : CoefficientMerge.Poly := [(nat_lit 504, Int.ofNat (nat_lit 91134720)), (nat_lit 505, Int.ofNat (nat_lit 38350800)), (nat_lit 506, Int.ofNat (nat_lit 60812640)), (nat_lit 507, Int.ofNat (nat_lit 38951280)), (nat_lit 508, Int.ofNat (nat_lit 32479920)), (nat_lit 509, Int.ofNat (nat_lit 48342960)), (nat_lit 514, Int.ofNat (nat_lit 27296640)), (nat_lit 515, Int.ofNat (nat_lit 46281600)), (nat_lit 516, Int.ofNat (nat_lit 46765440)), (nat_lit 517, Int.ofNat (nat_lit 47249280)), (nat_lit 518, Int.ofNat (nat_lit 47733120)), (nat_lit 519, Int.ofNat (nat_lit 96940800)), (nat_lit 520, Int.ofNat (nat_lit 53688240)), (nat_lit 521, Int.ofNat (nat_lit 73772640)), (nat_lit 522, Int.ofNat (nat_lit 64630800)), (nat_lit 523, Int.ofNat (nat_lit 64818000)), (nat_lit 524, Int.ofNat (nat_lit 87339600)), (nat_lit 530, Int.ofNat (nat_lit 31582080)), (nat_lit 531, Int.ofNat (nat_lit 61263360)), (nat_lit 532, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat156_step : block003_data_flat156 = (CoefficientMerge.fastMerge block003_data_flat136 block003_data_flat155) := by decide +kernel
theorem block003_data_flat156_original : block003_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91134720 : Int) atom0293Coded) (CoefficientMerge.scale (38350800 : Int) atom0294Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60812640 : Int) atom0295Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38951280 : Int) atom0296Coded) (CoefficientMerge.scale (32479920 : Int) atom0297Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48342960 : Int) atom0298Coded) (CoefficientMerge.scale (27296640 : Int) atom0299Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46281600 : Int) atom0300Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46765440 : Int) atom0301Coded) (CoefficientMerge.scale (47249280 : Int) atom0302Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47733120 : Int) atom0303Coded) (CoefficientMerge.scale (96940800 : Int) atom0304Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53688240 : Int) atom0305Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73772640 : Int) atom0306Coded) (CoefficientMerge.scale (64630800 : Int) atom0307Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64818000 : Int) atom0308Coded) (CoefficientMerge.scale (87339600 : Int) atom0309Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31582080 : Int) atom0310Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0311Coded) (CoefficientMerge.scale (61263360 : Int) atom0312Coded)))))) := by
  rw [block003_data_flat156_step, block003_data_flat136_original, block003_data_flat155_original]
def block003_data_flat157 : CoefficientMerge.Poly := [(nat_lit 434, Int.ofNat (nat_lit 38720880)), (nat_lit 449, Int.ofNat (nat_lit 13514040)), (nat_lit 482, Int.ofNat (nat_lit 10108800)), (nat_lit 483, Int.ofNat (nat_lit 28200960)), (nat_lit 484, Int.ofNat (nat_lit 26075520)), (nat_lit 485, Int.ofNat (nat_lit 23950080)), (nat_lit 486, Int.ofNat (nat_lit 21824640)), (nat_lit 487, Int.ofNat (nat_lit 19699200)), (nat_lit 488, Int.ofNat (nat_lit 17573760)), (nat_lit 489, Int.ofNat (nat_lit 42664320)), (nat_lit 490, Int.ofNat (nat_lit 13322880)), (nat_lit 491, Int.ofNat (nat_lit 23926320)), (nat_lit 492, Int.ofNat (nat_lit 9072000)), (nat_lit 494, Int.ofNat (nat_lit 13262400)), (nat_lit 498, Int.ofNat (nat_lit 21772800)), (nat_lit 499, Int.ofNat (nat_lit 40072320)), (nat_lit 500, Int.ofNat (nat_lit 39398400)), (nat_lit 501, Int.ofNat (nat_lit 38724480)), (nat_lit 502, Int.ofNat (nat_lit 38499840)), (nat_lit 503, Int.ofNat (nat_lit 38275200)), (nat_lit 504, Int.ofNat (nat_lit 91134720)), (nat_lit 505, Int.ofNat (nat_lit 38350800)), (nat_lit 506, Int.ofNat (nat_lit 60812640)), (nat_lit 507, Int.ofNat (nat_lit 38951280)), (nat_lit 508, Int.ofNat (nat_lit 32479920)), (nat_lit 509, Int.ofNat (nat_lit 48342960)), (nat_lit 514, Int.ofNat (nat_lit 27296640)), (nat_lit 515, Int.ofNat (nat_lit 46281600)), (nat_lit 516, Int.ofNat (nat_lit 46765440)), (nat_lit 517, Int.ofNat (nat_lit 47249280)), (nat_lit 518, Int.ofNat (nat_lit 47733120)), (nat_lit 519, Int.ofNat (nat_lit 96940800)), (nat_lit 520, Int.ofNat (nat_lit 53688240)), (nat_lit 521, Int.ofNat (nat_lit 73772640)), (nat_lit 522, Int.ofNat (nat_lit 64630800)), (nat_lit 523, Int.ofNat (nat_lit 64818000)), (nat_lit 524, Int.ofNat (nat_lit 87339600)), (nat_lit 530, Int.ofNat (nat_lit 31582080)), (nat_lit 531, Int.ofNat (nat_lit 61263360)), (nat_lit 532, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat157_step : block003_data_flat157 = (CoefficientMerge.fastMerge block003_data_flat117 block003_data_flat156) := by decide +kernel
theorem block003_data_flat157_original : block003_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38720880 : Int) atom0273Coded) (CoefficientMerge.scale (13514040 : Int) atom0274Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10108800 : Int) atom0275Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28200960 : Int) atom0276Coded) (CoefficientMerge.scale (26075520 : Int) atom0277Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23950080 : Int) atom0278Coded) (CoefficientMerge.scale (21824640 : Int) atom0279Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19699200 : Int) atom0280Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17573760 : Int) atom0281Coded) (CoefficientMerge.scale (42664320 : Int) atom0282Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13322880 : Int) atom0283Coded) (CoefficientMerge.scale (23926320 : Int) atom0284Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9072000 : Int) atom0285Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13262400 : Int) atom0286Coded) (CoefficientMerge.scale (21772800 : Int) atom0287Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40072320 : Int) atom0288Coded) (CoefficientMerge.scale (39398400 : Int) atom0289Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38724480 : Int) atom0290Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38499840 : Int) atom0291Coded) (CoefficientMerge.scale (38275200 : Int) atom0292Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91134720 : Int) atom0293Coded) (CoefficientMerge.scale (38350800 : Int) atom0294Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60812640 : Int) atom0295Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38951280 : Int) atom0296Coded) (CoefficientMerge.scale (32479920 : Int) atom0297Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48342960 : Int) atom0298Coded) (CoefficientMerge.scale (27296640 : Int) atom0299Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46281600 : Int) atom0300Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46765440 : Int) atom0301Coded) (CoefficientMerge.scale (47249280 : Int) atom0302Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47733120 : Int) atom0303Coded) (CoefficientMerge.scale (96940800 : Int) atom0304Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53688240 : Int) atom0305Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73772640 : Int) atom0306Coded) (CoefficientMerge.scale (64630800 : Int) atom0307Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64818000 : Int) atom0308Coded) (CoefficientMerge.scale (87339600 : Int) atom0309Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31582080 : Int) atom0310Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0311Coded) (CoefficientMerge.scale (61263360 : Int) atom0312Coded))))))) := by
  rw [block003_data_flat157_step, block003_data_flat117_original, block003_data_flat156_original]
def block003_data_flat158 : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 90512640)), (nat_lit 325, Int.ofNat (nat_lit 68604840)), (nat_lit 326, Int.ofNat (nat_lit 82191240)), (nat_lit 327, Int.ofNat (nat_lit 91916280)), (nat_lit 328, Int.ofNat (nat_lit 98458200)), (nat_lit 329, Int.ofNat (nat_lit 105000120)), (nat_lit 337, Int.ofNat (nat_lit 34030080)), (nat_lit 338, Int.ofNat (nat_lit 61189760)), (nat_lit 339, Int.ofNat (nat_lit 95363520)), (nat_lit 340, Int.ofNat (nat_lit 75650880)), (nat_lit 341, Int.ofNat (nat_lit 90831240)), (nat_lit 342, Int.ofNat (nat_lit 98742720)), (nat_lit 343, Int.ofNat (nat_lit 105417600)), (nat_lit 344, Int.ofNat (nat_lit 112092480)), (nat_lit 353, Int.ofNat (nat_lit 42281280)), (nat_lit 354, Int.ofNat (nat_lit 105534000)), (nat_lit 355, Int.ofNat (nat_lit 83431440)), (nat_lit 356, Int.ofNat (nat_lit 98601480)), (nat_lit 357, Int.ofNat (nat_lit 105713280)), (nat_lit 358, Int.ofNat (nat_lit 105421680)), (nat_lit 359, Int.ofNat (nat_lit 123972480)), (nat_lit 369, Int.ofNat (nat_lit 78278400)), (nat_lit 370, Int.ofNat (nat_lit 124610400)), (nat_lit 371, Int.ofNat (nat_lit 162543240)), (nat_lit 372, Int.ofNat (nat_lit 171695520)), (nat_lit 373, Int.ofNat (nat_lit 110190240)), (nat_lit 374, Int.ofNat (nat_lit 132083640)), (nat_lit 385, Int.ofNat (nat_lit 50720688)), (nat_lit 386, Int.ofNat (nat_lit 119681280)), (nat_lit 387, Int.ofNat (nat_lit 148644360)), (nat_lit 388, Int.ofNat (nat_lit 109284120)), (nat_lit 389, Int.ofNat (nat_lit 121793040)), (nat_lit 401, Int.ofNat (nat_lit 86289840)), (nat_lit 402, Int.ofNat (nat_lit 150873120)), (nat_lit 403, Int.ofNat (nat_lit 111926880)), (nat_lit 404, Int.ofNat (nat_lit 129163320)), (nat_lit 417, Int.ofNat (nat_lit 60586920)), (nat_lit 418, Int.ofNat (nat_lit 82651680)), (nat_lit 419, Int.ofNat (nat_lit 99339120)), (nat_lit 433, Int.ofNat (nat_lit 15121080)), (nat_lit 434, Int.ofNat (nat_lit 38720880)), (nat_lit 449, Int.ofNat (nat_lit 13514040)), (nat_lit 482, Int.ofNat (nat_lit 10108800)), (nat_lit 483, Int.ofNat (nat_lit 28200960)), (nat_lit 484, Int.ofNat (nat_lit 26075520)), (nat_lit 485, Int.ofNat (nat_lit 23950080)), (nat_lit 486, Int.ofNat (nat_lit 21824640)), (nat_lit 487, Int.ofNat (nat_lit 19699200)), (nat_lit 488, Int.ofNat (nat_lit 17573760)), (nat_lit 489, Int.ofNat (nat_lit 42664320)), (nat_lit 490, Int.ofNat (nat_lit 13322880)), (nat_lit 491, Int.ofNat (nat_lit 23926320)), (nat_lit 492, Int.ofNat (nat_lit 9072000)), (nat_lit 494, Int.ofNat (nat_lit 13262400)), (nat_lit 498, Int.ofNat (nat_lit 21772800)), (nat_lit 499, Int.ofNat (nat_lit 40072320)), (nat_lit 500, Int.ofNat (nat_lit 39398400)), (nat_lit 501, Int.ofNat (nat_lit 38724480)), (nat_lit 502, Int.ofNat (nat_lit 38499840)), (nat_lit 503, Int.ofNat (nat_lit 38275200)), (nat_lit 504, Int.ofNat (nat_lit 91134720)), (nat_lit 505, Int.ofNat (nat_lit 38350800)), (nat_lit 506, Int.ofNat (nat_lit 60812640)), (nat_lit 507, Int.ofNat (nat_lit 38951280)), (nat_lit 508, Int.ofNat (nat_lit 32479920)), (nat_lit 509, Int.ofNat (nat_lit 48342960)), (nat_lit 514, Int.ofNat (nat_lit 27296640)), (nat_lit 515, Int.ofNat (nat_lit 46281600)), (nat_lit 516, Int.ofNat (nat_lit 46765440)), (nat_lit 517, Int.ofNat (nat_lit 47249280)), (nat_lit 518, Int.ofNat (nat_lit 47733120)), (nat_lit 519, Int.ofNat (nat_lit 96940800)), (nat_lit 520, Int.ofNat (nat_lit 53688240)), (nat_lit 521, Int.ofNat (nat_lit 73772640)), (nat_lit 522, Int.ofNat (nat_lit 64630800)), (nat_lit 523, Int.ofNat (nat_lit 64818000)), (nat_lit 524, Int.ofNat (nat_lit 87339600)), (nat_lit 530, Int.ofNat (nat_lit 31582080)), (nat_lit 531, Int.ofNat (nat_lit 61263360)), (nat_lit 532, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat158_step : block003_data_flat158 = (CoefficientMerge.fastMerge block003_data_flat078 block003_data_flat157) := by decide +kernel
theorem block003_data_flat158_original : block003_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90512640 : Int) atom0233Coded) (CoefficientMerge.scale (68604840 : Int) atom0234Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82191240 : Int) atom0235Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91916280 : Int) atom0236Coded) (CoefficientMerge.scale (98458200 : Int) atom0237Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105000120 : Int) atom0238Coded) (CoefficientMerge.scale (34030080 : Int) atom0239Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61189760 : Int) atom0240Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (95363520 : Int) atom0241Coded) (CoefficientMerge.scale (75650880 : Int) atom0242Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90831240 : Int) atom0243Coded) (CoefficientMerge.scale (98742720 : Int) atom0244Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105417600 : Int) atom0245Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112092480 : Int) atom0246Coded) (CoefficientMerge.scale (42281280 : Int) atom0247Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105534000 : Int) atom0248Coded) (CoefficientMerge.scale (83431440 : Int) atom0249Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98601480 : Int) atom0250Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105713280 : Int) atom0251Coded) (CoefficientMerge.scale (105421680 : Int) atom0252Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123972480 : Int) atom0253Coded) (CoefficientMerge.scale (78278400 : Int) atom0254Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124610400 : Int) atom0255Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162543240 : Int) atom0256Coded) (CoefficientMerge.scale (171695520 : Int) atom0257Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110190240 : Int) atom0258Coded) (CoefficientMerge.scale (132083640 : Int) atom0259Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50720688 : Int) atom0260Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119681280 : Int) atom0261Coded) (CoefficientMerge.scale (148644360 : Int) atom0262Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109284120 : Int) atom0263Coded) (CoefficientMerge.scale (121793040 : Int) atom0264Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86289840 : Int) atom0265Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150873120 : Int) atom0266Coded) (CoefficientMerge.scale (111926880 : Int) atom0267Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129163320 : Int) atom0268Coded) (CoefficientMerge.scale (60586920 : Int) atom0269Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82651680 : Int) atom0270Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99339120 : Int) atom0271Coded) (CoefficientMerge.scale (15121080 : Int) atom0272Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38720880 : Int) atom0273Coded) (CoefficientMerge.scale (13514040 : Int) atom0274Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10108800 : Int) atom0275Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28200960 : Int) atom0276Coded) (CoefficientMerge.scale (26075520 : Int) atom0277Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23950080 : Int) atom0278Coded) (CoefficientMerge.scale (21824640 : Int) atom0279Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19699200 : Int) atom0280Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17573760 : Int) atom0281Coded) (CoefficientMerge.scale (42664320 : Int) atom0282Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13322880 : Int) atom0283Coded) (CoefficientMerge.scale (23926320 : Int) atom0284Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9072000 : Int) atom0285Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13262400 : Int) atom0286Coded) (CoefficientMerge.scale (21772800 : Int) atom0287Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40072320 : Int) atom0288Coded) (CoefficientMerge.scale (39398400 : Int) atom0289Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38724480 : Int) atom0290Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38499840 : Int) atom0291Coded) (CoefficientMerge.scale (38275200 : Int) atom0292Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91134720 : Int) atom0293Coded) (CoefficientMerge.scale (38350800 : Int) atom0294Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60812640 : Int) atom0295Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38951280 : Int) atom0296Coded) (CoefficientMerge.scale (32479920 : Int) atom0297Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48342960 : Int) atom0298Coded) (CoefficientMerge.scale (27296640 : Int) atom0299Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46281600 : Int) atom0300Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46765440 : Int) atom0301Coded) (CoefficientMerge.scale (47249280 : Int) atom0302Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47733120 : Int) atom0303Coded) (CoefficientMerge.scale (96940800 : Int) atom0304Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53688240 : Int) atom0305Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73772640 : Int) atom0306Coded) (CoefficientMerge.scale (64630800 : Int) atom0307Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64818000 : Int) atom0308Coded) (CoefficientMerge.scale (87339600 : Int) atom0309Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31582080 : Int) atom0310Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0311Coded) (CoefficientMerge.scale (61263360 : Int) atom0312Coded)))))))) := by
  rw [block003_data_flat158_step, block003_data_flat078_original, block003_data_flat157_original]
def block003_data_flat159 : CoefficientMerge.Poly := [(nat_lit 324, Int.ofNat (nat_lit 90512640)), (nat_lit 325, Int.ofNat (nat_lit 68604840)), (nat_lit 326, Int.ofNat (nat_lit 82191240)), (nat_lit 327, Int.ofNat (nat_lit 91916280)), (nat_lit 328, Int.ofNat (nat_lit 98458200)), (nat_lit 329, Int.ofNat (nat_lit 105000120)), (nat_lit 337, Int.ofNat (nat_lit 34030080)), (nat_lit 338, Int.ofNat (nat_lit 61189760)), (nat_lit 339, Int.ofNat (nat_lit 95363520)), (nat_lit 340, Int.ofNat (nat_lit 75650880)), (nat_lit 341, Int.ofNat (nat_lit 90831240)), (nat_lit 342, Int.ofNat (nat_lit 98742720)), (nat_lit 343, Int.ofNat (nat_lit 105417600)), (nat_lit 344, Int.ofNat (nat_lit 112092480)), (nat_lit 353, Int.ofNat (nat_lit 42281280)), (nat_lit 354, Int.ofNat (nat_lit 105534000)), (nat_lit 355, Int.ofNat (nat_lit 83431440)), (nat_lit 356, Int.ofNat (nat_lit 98601480)), (nat_lit 357, Int.ofNat (nat_lit 105713280)), (nat_lit 358, Int.ofNat (nat_lit 105421680)), (nat_lit 359, Int.ofNat (nat_lit 123972480)), (nat_lit 369, Int.ofNat (nat_lit 78278400)), (nat_lit 370, Int.ofNat (nat_lit 124610400)), (nat_lit 371, Int.ofNat (nat_lit 162543240)), (nat_lit 372, Int.ofNat (nat_lit 171695520)), (nat_lit 373, Int.ofNat (nat_lit 110190240)), (nat_lit 374, Int.ofNat (nat_lit 132083640)), (nat_lit 385, Int.ofNat (nat_lit 50720688)), (nat_lit 386, Int.ofNat (nat_lit 119681280)), (nat_lit 387, Int.ofNat (nat_lit 148644360)), (nat_lit 388, Int.ofNat (nat_lit 109284120)), (nat_lit 389, Int.ofNat (nat_lit 121793040)), (nat_lit 401, Int.ofNat (nat_lit 86289840)), (nat_lit 402, Int.ofNat (nat_lit 150873120)), (nat_lit 403, Int.ofNat (nat_lit 111926880)), (nat_lit 404, Int.ofNat (nat_lit 129163320)), (nat_lit 417, Int.ofNat (nat_lit 60586920)), (nat_lit 418, Int.ofNat (nat_lit 82651680)), (nat_lit 419, Int.ofNat (nat_lit 99339120)), (nat_lit 433, Int.ofNat (nat_lit 15121080)), (nat_lit 434, Int.ofNat (nat_lit 38720880)), (nat_lit 449, Int.ofNat (nat_lit 13514040)), (nat_lit 482, Int.ofNat (nat_lit 10108800)), (nat_lit 483, Int.ofNat (nat_lit 28200960)), (nat_lit 484, Int.ofNat (nat_lit 26075520)), (nat_lit 485, Int.ofNat (nat_lit 23950080)), (nat_lit 486, Int.ofNat (nat_lit 21824640)), (nat_lit 487, Int.ofNat (nat_lit 19699200)), (nat_lit 488, Int.ofNat (nat_lit 17573760)), (nat_lit 489, Int.ofNat (nat_lit 42664320)), (nat_lit 490, Int.ofNat (nat_lit 13322880)), (nat_lit 491, Int.ofNat (nat_lit 23926320)), (nat_lit 492, Int.ofNat (nat_lit 9072000)), (nat_lit 494, Int.ofNat (nat_lit 13262400)), (nat_lit 498, Int.ofNat (nat_lit 21772800)), (nat_lit 499, Int.ofNat (nat_lit 40072320)), (nat_lit 500, Int.ofNat (nat_lit 39398400)), (nat_lit 501, Int.ofNat (nat_lit 38724480)), (nat_lit 502, Int.ofNat (nat_lit 38499840)), (nat_lit 503, Int.ofNat (nat_lit 38275200)), (nat_lit 504, Int.ofNat (nat_lit 91134720)), (nat_lit 505, Int.ofNat (nat_lit 38350800)), (nat_lit 506, Int.ofNat (nat_lit 60812640)), (nat_lit 507, Int.ofNat (nat_lit 38951280)), (nat_lit 508, Int.ofNat (nat_lit 32479920)), (nat_lit 509, Int.ofNat (nat_lit 48342960)), (nat_lit 514, Int.ofNat (nat_lit 27296640)), (nat_lit 515, Int.ofNat (nat_lit 46281600)), (nat_lit 516, Int.ofNat (nat_lit 46765440)), (nat_lit 517, Int.ofNat (nat_lit 47249280)), (nat_lit 518, Int.ofNat (nat_lit 47733120)), (nat_lit 519, Int.ofNat (nat_lit 96940800)), (nat_lit 520, Int.ofNat (nat_lit 53688240)), (nat_lit 521, Int.ofNat (nat_lit 73772640)), (nat_lit 522, Int.ofNat (nat_lit 64630800)), (nat_lit 523, Int.ofNat (nat_lit 64818000)), (nat_lit 524, Int.ofNat (nat_lit 87339600)), (nat_lit 530, Int.ofNat (nat_lit 31582080)), (nat_lit 531, Int.ofNat (nat_lit 61263360)), (nat_lit 532, Int.ofNat (nat_lit 61263360))]
theorem block003_data_flat159_step : block003_data_flat159 = (CoefficientMerge.trim block003_data_flat158) := by decide +kernel
theorem block003_data_flat159_original : block003_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90512640 : Int) atom0233Coded) (CoefficientMerge.scale (68604840 : Int) atom0234Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82191240 : Int) atom0235Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91916280 : Int) atom0236Coded) (CoefficientMerge.scale (98458200 : Int) atom0237Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105000120 : Int) atom0238Coded) (CoefficientMerge.scale (34030080 : Int) atom0239Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61189760 : Int) atom0240Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (95363520 : Int) atom0241Coded) (CoefficientMerge.scale (75650880 : Int) atom0242Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90831240 : Int) atom0243Coded) (CoefficientMerge.scale (98742720 : Int) atom0244Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105417600 : Int) atom0245Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112092480 : Int) atom0246Coded) (CoefficientMerge.scale (42281280 : Int) atom0247Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105534000 : Int) atom0248Coded) (CoefficientMerge.scale (83431440 : Int) atom0249Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98601480 : Int) atom0250Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105713280 : Int) atom0251Coded) (CoefficientMerge.scale (105421680 : Int) atom0252Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123972480 : Int) atom0253Coded) (CoefficientMerge.scale (78278400 : Int) atom0254Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124610400 : Int) atom0255Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162543240 : Int) atom0256Coded) (CoefficientMerge.scale (171695520 : Int) atom0257Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110190240 : Int) atom0258Coded) (CoefficientMerge.scale (132083640 : Int) atom0259Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50720688 : Int) atom0260Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119681280 : Int) atom0261Coded) (CoefficientMerge.scale (148644360 : Int) atom0262Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109284120 : Int) atom0263Coded) (CoefficientMerge.scale (121793040 : Int) atom0264Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86289840 : Int) atom0265Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150873120 : Int) atom0266Coded) (CoefficientMerge.scale (111926880 : Int) atom0267Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129163320 : Int) atom0268Coded) (CoefficientMerge.scale (60586920 : Int) atom0269Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82651680 : Int) atom0270Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99339120 : Int) atom0271Coded) (CoefficientMerge.scale (15121080 : Int) atom0272Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38720880 : Int) atom0273Coded) (CoefficientMerge.scale (13514040 : Int) atom0274Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10108800 : Int) atom0275Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28200960 : Int) atom0276Coded) (CoefficientMerge.scale (26075520 : Int) atom0277Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23950080 : Int) atom0278Coded) (CoefficientMerge.scale (21824640 : Int) atom0279Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19699200 : Int) atom0280Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17573760 : Int) atom0281Coded) (CoefficientMerge.scale (42664320 : Int) atom0282Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13322880 : Int) atom0283Coded) (CoefficientMerge.scale (23926320 : Int) atom0284Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9072000 : Int) atom0285Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13262400 : Int) atom0286Coded) (CoefficientMerge.scale (21772800 : Int) atom0287Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40072320 : Int) atom0288Coded) (CoefficientMerge.scale (39398400 : Int) atom0289Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38724480 : Int) atom0290Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38499840 : Int) atom0291Coded) (CoefficientMerge.scale (38275200 : Int) atom0292Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91134720 : Int) atom0293Coded) (CoefficientMerge.scale (38350800 : Int) atom0294Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60812640 : Int) atom0295Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38951280 : Int) atom0296Coded) (CoefficientMerge.scale (32479920 : Int) atom0297Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48342960 : Int) atom0298Coded) (CoefficientMerge.scale (27296640 : Int) atom0299Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46281600 : Int) atom0300Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46765440 : Int) atom0301Coded) (CoefficientMerge.scale (47249280 : Int) atom0302Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47733120 : Int) atom0303Coded) (CoefficientMerge.scale (96940800 : Int) atom0304Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53688240 : Int) atom0305Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73772640 : Int) atom0306Coded) (CoefficientMerge.scale (64630800 : Int) atom0307Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64818000 : Int) atom0308Coded) (CoefficientMerge.scale (87339600 : Int) atom0309Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31582080 : Int) atom0310Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0311Coded) (CoefficientMerge.scale (61263360 : Int) atom0312Coded))))))))) := by
  rw [block003_data_flat159_step, block003_data_flat158_original]
theorem block003_data : block003 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90512640 : Int) atom0233Coded) (CoefficientMerge.scale (68604840 : Int) atom0234Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82191240 : Int) atom0235Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (91916280 : Int) atom0236Coded) (CoefficientMerge.scale (98458200 : Int) atom0237Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105000120 : Int) atom0238Coded) (CoefficientMerge.scale (34030080 : Int) atom0239Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61189760 : Int) atom0240Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (95363520 : Int) atom0241Coded) (CoefficientMerge.scale (75650880 : Int) atom0242Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90831240 : Int) atom0243Coded) (CoefficientMerge.scale (98742720 : Int) atom0244Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105417600 : Int) atom0245Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112092480 : Int) atom0246Coded) (CoefficientMerge.scale (42281280 : Int) atom0247Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (105534000 : Int) atom0248Coded) (CoefficientMerge.scale (83431440 : Int) atom0249Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98601480 : Int) atom0250Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105713280 : Int) atom0251Coded) (CoefficientMerge.scale (105421680 : Int) atom0252Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123972480 : Int) atom0253Coded) (CoefficientMerge.scale (78278400 : Int) atom0254Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124610400 : Int) atom0255Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162543240 : Int) atom0256Coded) (CoefficientMerge.scale (171695520 : Int) atom0257Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (110190240 : Int) atom0258Coded) (CoefficientMerge.scale (132083640 : Int) atom0259Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50720688 : Int) atom0260Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119681280 : Int) atom0261Coded) (CoefficientMerge.scale (148644360 : Int) atom0262Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109284120 : Int) atom0263Coded) (CoefficientMerge.scale (121793040 : Int) atom0264Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86289840 : Int) atom0265Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150873120 : Int) atom0266Coded) (CoefficientMerge.scale (111926880 : Int) atom0267Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129163320 : Int) atom0268Coded) (CoefficientMerge.scale (60586920 : Int) atom0269Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82651680 : Int) atom0270Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (99339120 : Int) atom0271Coded) (CoefficientMerge.scale (15121080 : Int) atom0272Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38720880 : Int) atom0273Coded) (CoefficientMerge.scale (13514040 : Int) atom0274Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10108800 : Int) atom0275Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28200960 : Int) atom0276Coded) (CoefficientMerge.scale (26075520 : Int) atom0277Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23950080 : Int) atom0278Coded) (CoefficientMerge.scale (21824640 : Int) atom0279Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19699200 : Int) atom0280Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17573760 : Int) atom0281Coded) (CoefficientMerge.scale (42664320 : Int) atom0282Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13322880 : Int) atom0283Coded) (CoefficientMerge.scale (23926320 : Int) atom0284Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9072000 : Int) atom0285Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13262400 : Int) atom0286Coded) (CoefficientMerge.scale (21772800 : Int) atom0287Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40072320 : Int) atom0288Coded) (CoefficientMerge.scale (39398400 : Int) atom0289Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38724480 : Int) atom0290Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38499840 : Int) atom0291Coded) (CoefficientMerge.scale (38275200 : Int) atom0292Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91134720 : Int) atom0293Coded) (CoefficientMerge.scale (38350800 : Int) atom0294Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60812640 : Int) atom0295Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38951280 : Int) atom0296Coded) (CoefficientMerge.scale (32479920 : Int) atom0297Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48342960 : Int) atom0298Coded) (CoefficientMerge.scale (27296640 : Int) atom0299Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46281600 : Int) atom0300Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46765440 : Int) atom0301Coded) (CoefficientMerge.scale (47249280 : Int) atom0302Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47733120 : Int) atom0303Coded) (CoefficientMerge.scale (96940800 : Int) atom0304Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53688240 : Int) atom0305Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73772640 : Int) atom0306Coded) (CoefficientMerge.scale (64630800 : Int) atom0307Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64818000 : Int) atom0308Coded) (CoefficientMerge.scale (87339600 : Int) atom0309Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31582080 : Int) atom0310Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61263360 : Int) atom0311Coded) (CoefficientMerge.scale (61263360 : Int) atom0312Coded)))))))) := by
  have h : block003 = block003_data_flat159 := by decide +kernel
  exact h.trans block003_data_flat159_original
theorem block003_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) block003 := by
  rw [block003_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0233Coded_nonneg g hg hA hB) (atom0234Coded_nonneg g hg hA hB)) (add_nonneg (atom0235Coded_nonneg g hg hA hB) (add_nonneg (atom0236Coded_nonneg g hg hA hB) (atom0237Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0238Coded_nonneg g hg hA hB) (atom0239Coded_nonneg g hg hA hB)) (add_nonneg (atom0240Coded_nonneg g hg hA hB) (add_nonneg (atom0241Coded_nonneg g hg hA hB) (atom0242Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0243Coded_nonneg g hg hA hB) (atom0244Coded_nonneg g hg hA hB)) (add_nonneg (atom0245Coded_nonneg g hg hA hB) (add_nonneg (atom0246Coded_nonneg g hg hA hB) (atom0247Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0248Coded_nonneg g hg hA hB) (atom0249Coded_nonneg g hg hA hB)) (add_nonneg (atom0250Coded_nonneg g hg hA hB) (add_nonneg (atom0251Coded_nonneg g hg hA hB) (atom0252Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0253Coded_nonneg g hg hA hB) (atom0254Coded_nonneg g hg hA hB)) (add_nonneg (atom0255Coded_nonneg g hg hA hB) (add_nonneg (atom0256Coded_nonneg g hg hA hB) (atom0257Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0258Coded_nonneg g hg hA hB) (atom0259Coded_nonneg g hg hA hB)) (add_nonneg (atom0260Coded_nonneg g hg hA hB) (add_nonneg (atom0261Coded_nonneg g hg hA hB) (atom0262Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0263Coded_nonneg g hg hA hB) (atom0264Coded_nonneg g hg hA hB)) (add_nonneg (atom0265Coded_nonneg g hg hA hB) (add_nonneg (atom0266Coded_nonneg g hg hA hB) (atom0267Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0268Coded_nonneg g hg hA hB) (atom0269Coded_nonneg g hg hA hB)) (add_nonneg (atom0270Coded_nonneg g hg hA hB) (add_nonneg (atom0271Coded_nonneg g hg hA hB) (atom0272Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0273Coded_nonneg g hg hA hB) (atom0274Coded_nonneg g hg hA hB)) (add_nonneg (atom0275Coded_nonneg g hg hA hB) (add_nonneg (atom0276Coded_nonneg g hg hA hB) (atom0277Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0278Coded_nonneg g hg hA hB) (atom0279Coded_nonneg g hg hA hB)) (add_nonneg (atom0280Coded_nonneg g hg hA hB) (add_nonneg (atom0281Coded_nonneg g hg hA hB) (atom0282Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0283Coded_nonneg g hg hA hB) (atom0284Coded_nonneg g hg hA hB)) (add_nonneg (atom0285Coded_nonneg g hg hA hB) (add_nonneg (atom0286Coded_nonneg g hg hA hB) (atom0287Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0288Coded_nonneg g hg hA hB) (atom0289Coded_nonneg g hg hA hB)) (add_nonneg (atom0290Coded_nonneg g hg hA hB) (add_nonneg (atom0291Coded_nonneg g hg hA hB) (atom0292Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0293Coded_nonneg g hg hA hB) (atom0294Coded_nonneg g hg hA hB)) (add_nonneg (atom0295Coded_nonneg g hg hA hB) (add_nonneg (atom0296Coded_nonneg g hg hA hB) (atom0297Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0298Coded_nonneg g hg hA hB) (atom0299Coded_nonneg g hg hA hB)) (add_nonneg (atom0300Coded_nonneg g hg hA hB) (add_nonneg (atom0301Coded_nonneg g hg hA hB) (atom0302Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0303Coded_nonneg g hg hA hB) (atom0304Coded_nonneg g hg hA hB)) (add_nonneg (atom0305Coded_nonneg g hg hA hB) (add_nonneg (atom0306Coded_nonneg g hg hA hB) (atom0307Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0308Coded_nonneg g hg hA hB) (atom0309Coded_nonneg g hg hA hB)) (add_nonneg (atom0310Coded_nonneg g hg hA hB) (add_nonneg (atom0311Coded_nonneg g hg hA hB) (atom0312Coded_nonneg g hg hA hB))))))))

end APPT.Finite15
