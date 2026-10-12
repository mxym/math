-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0256 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0256 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0256 = ((g 0) * (g 6) * (g 13)) := by
  norm_num [atom0256, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0256_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24337174377600 : Int) atom0256) := by
  rw [SparsePolynomial.eval_scale, eval_atom0256]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0256Coded : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 1))]
theorem atom0256Coded_decode : atom0256 = SparsePolynomial.decodeCubic 21 atom0256Coded := by decide +kernel
theorem atom0256Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) := by
  have h := atom0256_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0256Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0257 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0257 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0257 = ((g 0) * (g 6) * (g 14)) := by
  norm_num [atom0257, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0257_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25039315123200 : Int) atom0257) := by
  rw [SparsePolynomial.eval_scale, eval_atom0257]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0257Coded : CoefficientMerge.Poly := [(nat_lit 140, Int.ofNat (nat_lit 1))]
theorem atom0257Coded_decode : atom0257 = SparsePolynomial.decodeCubic 21 atom0257Coded := by decide +kernel
theorem atom0257Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded) := by
  have h := atom0257_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0257Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0258 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0258 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0258 = ((g 0) * (g 6) * (g 15)) := by
  norm_num [atom0258, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0258_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29039577235200 : Int) atom0258) := by
  rw [SparsePolynomial.eval_scale, eval_atom0258]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0258Coded : CoefficientMerge.Poly := [(nat_lit 141, Int.ofNat (nat_lit 1))]
theorem atom0258Coded_decode : atom0258 = SparsePolynomial.decodeCubic 21 atom0258Coded := by decide +kernel
theorem atom0258Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) := by
  have h := atom0258_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0258Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0259 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0259 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0259 = ((g 0) * (g 6) * (g 16)) := by
  norm_num [atom0259, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0259_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21558664512000 : Int) atom0259) := by
  rw [SparsePolynomial.eval_scale, eval_atom0259]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0259Coded : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 1))]
theorem atom0259Coded_decode : atom0259 = SparsePolynomial.decodeCubic 21 atom0259Coded := by decide +kernel
theorem atom0259Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) := by
  have h := atom0259_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0259Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0260 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0260 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0260 = ((g 0) * (g 6) * (g 17)) := by
  norm_num [atom0260, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0260_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18654996729600 : Int) atom0260) := by
  rw [SparsePolynomial.eval_scale, eval_atom0260]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0260Coded : CoefficientMerge.Poly := [(nat_lit 143, Int.ofNat (nat_lit 1))]
theorem atom0260Coded_decode : atom0260 = SparsePolynomial.decodeCubic 21 atom0260Coded := by decide +kernel
theorem atom0260Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded) := by
  have h := atom0260_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0260Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0261 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0261 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0261 = ((g 0) * (g 6) * (g 18)) := by
  norm_num [atom0261, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0261_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13125428870400 : Int) atom0261) := by
  rw [SparsePolynomial.eval_scale, eval_atom0261]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0261Coded : CoefficientMerge.Poly := [(nat_lit 144, Int.ofNat (nat_lit 1))]
theorem atom0261Coded_decode : atom0261 = SparsePolynomial.decodeCubic 21 atom0261Coded := by decide +kernel
theorem atom0261Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) := by
  have h := atom0261_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0261Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0262 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0262 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0262 = ((g 0) * (g 6) * (g 19)) := by
  norm_num [atom0262, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0262_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13510927180800 : Int) atom0262) := by
  rw [SparsePolynomial.eval_scale, eval_atom0262]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0262Coded : CoefficientMerge.Poly := [(nat_lit 145, Int.ofNat (nat_lit 1))]
theorem atom0262Coded_decode : atom0262 = SparsePolynomial.decodeCubic 21 atom0262Coded := by decide +kernel
theorem atom0262Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded) := by
  have h := atom0262_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0262Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0263 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0263 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0263 = ((g 0) * (g 6) * (g 20)) := by
  norm_num [atom0263, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0263_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10819430496000 : Int) atom0263) := by
  rw [SparsePolynomial.eval_scale, eval_atom0263]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0263Coded : CoefficientMerge.Poly := [(nat_lit 146, Int.ofNat (nat_lit 1))]
theorem atom0263Coded_decode : atom0263 = SparsePolynomial.decodeCubic 21 atom0263Coded := by decide +kernel
theorem atom0263Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) := by
  have h := atom0263_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0263Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0264 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0264 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0264 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0264, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0264_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13421582466048 : Int) atom0264) := by
  rw [SparsePolynomial.eval_scale, eval_atom0264]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0264Coded : CoefficientMerge.Poly := [(nat_lit 154, Int.ofNat (nat_lit 1))]
theorem atom0264Coded_decode : atom0264 = SparsePolynomial.decodeCubic 21 atom0264Coded := by decide +kernel
theorem atom0264Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) := by
  have h := atom0264_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0264Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0265 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0265 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0265 = ((g 0) * (g 7) * (g 8)) := by
  norm_num [atom0265, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0265_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23660965873728 : Int) atom0265) := by
  rw [SparsePolynomial.eval_scale, eval_atom0265]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0265Coded : CoefficientMerge.Poly := [(nat_lit 155, Int.ofNat (nat_lit 1))]
theorem atom0265Coded_decode : atom0265 = SparsePolynomial.decodeCubic 21 atom0265Coded := by decide +kernel
theorem atom0265Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded) := by
  have h := atom0265_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0265Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0266 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0266 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0266 = ((g 0) * (g 7) * (g 9)) := by
  norm_num [atom0266, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0266_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22372041369024 : Int) atom0266) := by
  rw [SparsePolynomial.eval_scale, eval_atom0266]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0266Coded : CoefficientMerge.Poly := [(nat_lit 156, Int.ofNat (nat_lit 1))]
theorem atom0266Coded_decode : atom0266 = SparsePolynomial.decodeCubic 21 atom0266Coded := by decide +kernel
theorem atom0266Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) := by
  have h := atom0266_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0266Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0267 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0267 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0267 = ((g 0) * (g 7) * (g 10)) := by
  norm_num [atom0267, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0267_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23033831975424 : Int) atom0267) := by
  rw [SparsePolynomial.eval_scale, eval_atom0267]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0267Coded : CoefficientMerge.Poly := [(nat_lit 157, Int.ofNat (nat_lit 1))]
theorem atom0267Coded_decode : atom0267 = SparsePolynomial.decodeCubic 21 atom0267Coded := by decide +kernel
theorem atom0267Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded) := by
  have h := atom0267_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0267Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0268 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0268 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0268 = ((g 0) * (g 7) * (g 11)) := by
  norm_num [atom0268, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0268_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23838356994624 : Int) atom0268) := by
  rw [SparsePolynomial.eval_scale, eval_atom0268]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0268Coded : CoefficientMerge.Poly := [(nat_lit 158, Int.ofNat (nat_lit 1))]
theorem atom0268Coded_decode : atom0268 = SparsePolynomial.decodeCubic 21 atom0268Coded := by decide +kernel
theorem atom0268Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) := by
  have h := atom0268_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0268Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0269 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0269 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0269 = ((g 0) * (g 7) * (g 12)) := by
  norm_num [atom0269, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0269_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25176291029824 : Int) atom0269) := by
  rw [SparsePolynomial.eval_scale, eval_atom0269]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0269Coded : CoefficientMerge.Poly := [(nat_lit 159, Int.ofNat (nat_lit 1))]
theorem atom0269Coded_decode : atom0269 = SparsePolynomial.decodeCubic 21 atom0269Coded := by decide +kernel
theorem atom0269Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) := by
  have h := atom0269_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0269Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0270 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0270 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0270 = ((g 0) * (g 7) * (g 13)) := by
  norm_num [atom0270, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0270_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26078455353024 : Int) atom0270) := by
  rw [SparsePolynomial.eval_scale, eval_atom0270]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0270Coded : CoefficientMerge.Poly := [(nat_lit 160, Int.ofNat (nat_lit 1))]
theorem atom0270Coded_decode : atom0270 = SparsePolynomial.decodeCubic 21 atom0270Coded := by decide +kernel
theorem atom0270Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded) := by
  have h := atom0270_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0270Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0271 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0271 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0271 = ((g 0) * (g 7) * (g 14)) := by
  norm_num [atom0271, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0271_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26761266690624 : Int) atom0271) := by
  rw [SparsePolynomial.eval_scale, eval_atom0271]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0271Coded : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 1))]
theorem atom0271Coded_decode : atom0271 = SparsePolynomial.decodeCubic 21 atom0271Coded := by decide +kernel
theorem atom0271Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) := by
  have h := atom0271_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0271Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0272 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0272 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0272 = ((g 0) * (g 7) * (g 15)) := by
  norm_num [atom0272, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0272_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30796193398176 : Int) atom0272) := by
  rw [SparsePolynomial.eval_scale, eval_atom0272]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0272Coded : CoefficientMerge.Poly := [(nat_lit 162, Int.ofNat (nat_lit 1))]
theorem atom0272Coded_decode : atom0272 = SparsePolynomial.decodeCubic 21 atom0272Coded := by decide +kernel
theorem atom0272Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded) := by
  have h := atom0272_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0272Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0273 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0273 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0273 = ((g 0) * (g 7) * (g 16)) := by
  norm_num [atom0273, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0273_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23976290418336 : Int) atom0273) := by
  rw [SparsePolynomial.eval_scale, eval_atom0273]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0273Coded : CoefficientMerge.Poly := [(nat_lit 163, Int.ofNat (nat_lit 1))]
theorem atom0273Coded_decode : atom0273 = SparsePolynomial.decodeCubic 21 atom0273Coded := by decide +kernel
theorem atom0273Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) := by
  have h := atom0273_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0273Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0274 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0274 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0274 = ((g 0) * (g 7) * (g 17)) := by
  norm_num [atom0274, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0274_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22287869204832 : Int) atom0274) := by
  rw [SparsePolynomial.eval_scale, eval_atom0274]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0274Coded : CoefficientMerge.Poly := [(nat_lit 164, Int.ofNat (nat_lit 1))]
theorem atom0274Coded_decode : atom0274 = SparsePolynomial.decodeCubic 21 atom0274Coded := by decide +kernel
theorem atom0274Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) := by
  have h := atom0274_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0274Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0275 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0275 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0275 = ((g 0) * (g 7) * (g 18)) := by
  norm_num [atom0275, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0275_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16973062270560 : Int) atom0275) := by
  rw [SparsePolynomial.eval_scale, eval_atom0275]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0275Coded : CoefficientMerge.Poly := [(nat_lit 165, Int.ofNat (nat_lit 1))]
theorem atom0275Coded_decode : atom0275 = SparsePolynomial.decodeCubic 21 atom0275Coded := by decide +kernel
theorem atom0275Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded) := by
  have h := atom0275_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0275Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0276 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0276 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0276 = ((g 0) * (g 7) * (g 19)) := by
  norm_num [atom0276, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0276_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16137647557920 : Int) atom0276) := by
  rw [SparsePolynomial.eval_scale, eval_atom0276]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0276Coded : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 1))]
theorem atom0276Coded_decode : atom0276 = SparsePolynomial.decodeCubic 21 atom0276Coded := by decide +kernel
theorem atom0276Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) := by
  have h := atom0276_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0276Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0277 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0277 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0277 = ((g 0) * (g 7) * (g 20)) := by
  norm_num [atom0277, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0277_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14405932338336 : Int) atom0277) := by
  rw [SparsePolynomial.eval_scale, eval_atom0277]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0277Coded : CoefficientMerge.Poly := [(nat_lit 167, Int.ofNat (nat_lit 1))]
theorem atom0277Coded_decode : atom0277 = SparsePolynomial.decodeCubic 21 atom0277Coded := by decide +kernel
theorem atom0277Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded) := by
  have h := atom0277_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0277Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0278 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0278 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0278 = ((g 0) * (g 8) * (g 8)) := by
  norm_num [atom0278, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0278_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14770003348800 : Int) atom0278) := by
  rw [SparsePolynomial.eval_scale, eval_atom0278]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0278Coded : CoefficientMerge.Poly := [(nat_lit 176, Int.ofNat (nat_lit 1))]
theorem atom0278Coded_decode : atom0278 = SparsePolynomial.decodeCubic 21 atom0278Coded := by decide +kernel
theorem atom0278Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) := by
  have h := atom0278_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0278Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0279 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0279 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0279 = ((g 0) * (g 8) * (g 9)) := by
  norm_num [atom0279, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0279_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26552598367680 : Int) atom0279) := by
  rw [SparsePolynomial.eval_scale, eval_atom0279]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0279Coded : CoefficientMerge.Poly := [(nat_lit 177, Int.ofNat (nat_lit 1))]
theorem atom0279Coded_decode : atom0279 = SparsePolynomial.decodeCubic 21 atom0279Coded := by decide +kernel
theorem atom0279Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) := by
  have h := atom0279_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0279Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0280 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0280 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0280 = ((g 0) * (g 8) * (g 10)) := by
  norm_num [atom0280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0280_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25135035962400 : Int) atom0280) := by
  rw [SparsePolynomial.eval_scale, eval_atom0280]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0280Coded : CoefficientMerge.Poly := [(nat_lit 178, Int.ofNat (nat_lit 1))]
theorem atom0280Coded_decode : atom0280 = SparsePolynomial.decodeCubic 21 atom0280Coded := by decide +kernel
theorem atom0280Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded) := by
  have h := atom0280_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0280Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0281 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0281 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0281 = ((g 0) * (g 8) * (g 11)) := by
  norm_num [atom0281, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0281_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25813436594400 : Int) atom0281) := by
  rw [SparsePolynomial.eval_scale, eval_atom0281]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0281Coded : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 1))]
theorem atom0281Coded_decode : atom0281 = SparsePolynomial.decodeCubic 21 atom0281Coded := by decide +kernel
theorem atom0281Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) := by
  have h := atom0281_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0281Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0282 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0282 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0282 = ((g 0) * (g 8) * (g 12)) := by
  norm_num [atom0282, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0282_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26983204780000 : Int) atom0282) := by
  rw [SparsePolynomial.eval_scale, eval_atom0282]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0282Coded : CoefficientMerge.Poly := [(nat_lit 180, Int.ofNat (nat_lit 1))]
theorem atom0282Coded_decode : atom0282 = SparsePolynomial.decodeCubic 21 atom0282Coded := by decide +kernel
theorem atom0282Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded) := by
  have h := atom0282_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0282Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0283 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0283 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0283 = ((g 0) * (g 8) * (g 13)) := by
  norm_num [atom0283, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0283_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27823998232800 : Int) atom0283) := by
  rw [SparsePolynomial.eval_scale, eval_atom0283]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0283Coded : CoefficientMerge.Poly := [(nat_lit 181, Int.ofNat (nat_lit 1))]
theorem atom0283Coded_decode : atom0283 = SparsePolynomial.decodeCubic 21 atom0283Coded := by decide +kernel
theorem atom0283Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) := by
  have h := atom0283_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0283Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0284 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0284 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0284 = ((g 0) * (g 8) * (g 14)) := by
  norm_num [atom0284, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0284_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28445438700000 : Int) atom0284) := by
  rw [SparsePolynomial.eval_scale, eval_atom0284]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0284Coded : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 1))]
theorem atom0284Coded_decode : atom0284 = SparsePolynomial.decodeCubic 21 atom0284Coded := by decide +kernel
theorem atom0284Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) := by
  have h := atom0284_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0284Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0285 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0285 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0285 = ((g 0) * (g 8) * (g 15)) := by
  norm_num [atom0285, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0285_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32314904294400 : Int) atom0285) := by
  rw [SparsePolynomial.eval_scale, eval_atom0285]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0285Coded : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 1))]
theorem atom0285Coded_decode : atom0285 = SparsePolynomial.decodeCubic 21 atom0285Coded := by decide +kernel
theorem atom0285Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded) := by
  have h := atom0285_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0285Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0286 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0286 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0286 = ((g 0) * (g 8) * (g 16)) := by
  norm_num [atom0286, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0286_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25706174665500 : Int) atom0286) := by
  rw [SparsePolynomial.eval_scale, eval_atom0286]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0286Coded : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 1))]
theorem atom0286Coded_decode : atom0286 = SparsePolynomial.decodeCubic 21 atom0286Coded := by decide +kernel
theorem atom0286Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) := by
  have h := atom0286_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0286Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0287 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0287 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0287 = ((g 0) * (g 8) * (g 17)) := by
  norm_num [atom0287, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0287_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24255404812800 : Int) atom0287) := by
  rw [SparsePolynomial.eval_scale, eval_atom0287]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0287Coded : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 1))]
theorem atom0287Coded_decode : atom0287 = SparsePolynomial.decodeCubic 21 atom0287Coded := by decide +kernel
theorem atom0287Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded) := by
  have h := atom0287_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0287Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0288 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0288 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0288 = ((g 0) * (g 8) * (g 18)) := by
  norm_num [atom0288, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0288_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18917112734100 : Int) atom0288) := by
  rw [SparsePolynomial.eval_scale, eval_atom0288]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0288Coded : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 1))]
theorem atom0288Coded_decode : atom0288 = SparsePolynomial.decodeCubic 21 atom0288Coded := by decide +kernel
theorem atom0288Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) := by
  have h := atom0288_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0288Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0289 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0289 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0289 = ((g 0) * (g 8) * (g 19)) := by
  norm_num [atom0289, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0289_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17491669568100 : Int) atom0289) := by
  rw [SparsePolynomial.eval_scale, eval_atom0289]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0289Coded : CoefficientMerge.Poly := [(nat_lit 187, Int.ofNat (nat_lit 1))]
theorem atom0289Coded_decode : atom0289 = SparsePolynomial.decodeCubic 21 atom0289Coded := by decide +kernel
theorem atom0289Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) := by
  have h := atom0289_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0289Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0290 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0290 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0290 = ((g 0) * (g 8) * (g 20)) := by
  norm_num [atom0290, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0290_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15923188782900 : Int) atom0290) := by
  rw [SparsePolynomial.eval_scale, eval_atom0290]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0290Coded : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 1))]
theorem atom0290Coded_decode : atom0290 = SparsePolynomial.decodeCubic 21 atom0290Coded := by decide +kernel
theorem atom0290Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded) := by
  have h := atom0290_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0290Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0291 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0291 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0291 = ((g 0) * (g 9) * (g 9)) := by
  norm_num [atom0291, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0291_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16313214960000 : Int) atom0291) := by
  rw [SparsePolynomial.eval_scale, eval_atom0291]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0291Coded : CoefficientMerge.Poly := [(nat_lit 198, Int.ofNat (nat_lit 1))]
theorem atom0291Coded_decode : atom0291 = SparsePolynomial.decodeCubic 21 atom0291Coded := by decide +kernel
theorem atom0291Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) := by
  have h := atom0291_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0291Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0292 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0292 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0292 = ((g 0) * (g 9) * (g 10)) := by
  norm_num [atom0292, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0292_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29540683226880 : Int) atom0292) := by
  rw [SparsePolynomial.eval_scale, eval_atom0292]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0292Coded : CoefficientMerge.Poly := [(nat_lit 199, Int.ofNat (nat_lit 1))]
theorem atom0292Coded_decode : atom0292 = SparsePolynomial.decodeCubic 21 atom0292Coded := by decide +kernel
theorem atom0292Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded) := by
  have h := atom0292_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0292Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0293 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0293 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0293 = ((g 0) * (g 9) * (g 11)) := by
  norm_num [atom0293, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0293_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27605876760000 : Int) atom0293) := by
  rw [SparsePolynomial.eval_scale, eval_atom0293]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0293Coded : CoefficientMerge.Poly := [(nat_lit 200, Int.ofNat (nat_lit 1))]
theorem atom0293Coded_decode : atom0293 = SparsePolynomial.decodeCubic 21 atom0293Coded := by decide +kernel
theorem atom0293Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) := by
  have h := atom0293_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0293Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0294 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0294 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0294 = ((g 0) * (g 9) * (g 12)) := by
  norm_num [atom0294, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0294_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28779027592000 : Int) atom0294) := by
  rw [SparsePolynomial.eval_scale, eval_atom0294]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0294Coded : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 1))]
theorem atom0294Coded_decode : atom0294 = SparsePolynomial.decodeCubic 21 atom0294Coded := by decide +kernel
theorem atom0294Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) := by
  have h := atom0294_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0294Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0295 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0295 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0295 = ((g 0) * (g 9) * (g 13)) := by
  norm_num [atom0295, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0295_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29516408712000 : Int) atom0295) := by
  rw [SparsePolynomial.eval_scale, eval_atom0295]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0295Coded : CoefficientMerge.Poly := [(nat_lit 202, Int.ofNat (nat_lit 1))]
theorem atom0295Coded_decode : atom0295 = SparsePolynomial.decodeCubic 21 atom0295Coded := by decide +kernel
theorem atom0295Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded) := by
  have h := atom0295_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0295Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0296 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0296 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0296 = ((g 0) * (g 9) * (g 14)) := by
  norm_num [atom0296, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0296_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30034436846400 : Int) atom0296) := by
  rw [SparsePolynomial.eval_scale, eval_atom0296]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0296Coded : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 1))]
theorem atom0296Coded_decode : atom0296 = SparsePolynomial.decodeCubic 21 atom0296Coded := by decide +kernel
theorem atom0296Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) := by
  have h := atom0296_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0296Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0297 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0297 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0297 = ((g 0) * (g 9) * (g 15)) := by
  norm_num [atom0297, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0297_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33814866355200 : Int) atom0297) := by
  rw [SparsePolynomial.eval_scale, eval_atom0297]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0297Coded : CoefficientMerge.Poly := [(nat_lit 204, Int.ofNat (nat_lit 1))]
theorem atom0297Coded_decode : atom0297 = SparsePolynomial.decodeCubic 21 atom0297Coded := by decide +kernel
theorem atom0297Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded) := by
  have h := atom0297_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0297Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0298 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0298 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0298 = ((g 0) * (g 9) * (g 16)) := by
  norm_num [atom0298, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0298_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27205547783400 : Int) atom0298) := by
  rw [SparsePolynomial.eval_scale, eval_atom0298]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0298Coded : CoefficientMerge.Poly := [(nat_lit 205, Int.ofNat (nat_lit 1))]
theorem atom0298Coded_decode : atom0298 = SparsePolynomial.decodeCubic 21 atom0298Coded := by decide +kernel
theorem atom0298Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) := by
  have h := atom0298_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0298Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0299 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0299 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0299 = ((g 0) * (g 9) * (g 17)) := by
  norm_num [atom0299, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0299_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26091698572800 : Int) atom0299) := by
  rw [SparsePolynomial.eval_scale, eval_atom0299]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0299Coded : CoefficientMerge.Poly := [(nat_lit 206, Int.ofNat (nat_lit 1))]
theorem atom0299Coded_decode : atom0299 = SparsePolynomial.decodeCubic 21 atom0299Coded := by decide +kernel
theorem atom0299Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) := by
  have h := atom0299_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0299Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0300 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0300 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0300 = ((g 0) * (g 9) * (g 18)) := by
  norm_num [atom0300, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0300_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20444060460600 : Int) atom0300) := by
  rw [SparsePolynomial.eval_scale, eval_atom0300]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0300Coded : CoefficientMerge.Poly := [(nat_lit 207, Int.ofNat (nat_lit 1))]
theorem atom0300Coded_decode : atom0300 = SparsePolynomial.decodeCubic 21 atom0300Coded := by decide +kernel
theorem atom0300Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded) := by
  have h := atom0300_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0300Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0301 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0301 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0301 = ((g 0) * (g 9) * (g 19)) := by
  norm_num [atom0301, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0301_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18430701269400 : Int) atom0301) := by
  rw [SparsePolynomial.eval_scale, eval_atom0301]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0301Coded : CoefficientMerge.Poly := [(nat_lit 208, Int.ofNat (nat_lit 1))]
theorem atom0301Coded_decode : atom0301 = SparsePolynomial.decodeCubic 21 atom0301Coded := by decide +kernel
theorem atom0301Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) := by
  have h := atom0301_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0301Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0302 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0302 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0302 = ((g 0) * (g 9) * (g 20)) := by
  norm_num [atom0302, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0302_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16915074334200 : Int) atom0302) := by
  rw [SparsePolynomial.eval_scale, eval_atom0302]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0302Coded : CoefficientMerge.Poly := [(nat_lit 209, Int.ofNat (nat_lit 1))]
theorem atom0302Coded_decode : atom0302 = SparsePolynomial.decodeCubic 21 atom0302Coded := by decide +kernel
theorem atom0302Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded) := by
  have h := atom0302_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0302Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0303 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0303 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0303 = ((g 0) * (g 10) * (g 10)) := by
  norm_num [atom0303, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0303_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17758088208000 : Int) atom0303) := by
  rw [SparsePolynomial.eval_scale, eval_atom0303]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0303Coded : CoefficientMerge.Poly := [(nat_lit 220, Int.ofNat (nat_lit 1))]
theorem atom0303Coded_decode : atom0303 = SparsePolynomial.decodeCubic 21 atom0303Coded := by decide +kernel
theorem atom0303Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) := by
  have h := atom0303_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0303Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0304 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0304 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0304 = ((g 0) * (g 10) * (g 11)) := by
  norm_num [atom0304, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0304_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32512456529280 : Int) atom0304) := by
  rw [SparsePolynomial.eval_scale, eval_atom0304]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0304Coded : CoefficientMerge.Poly := [(nat_lit 221, Int.ofNat (nat_lit 1))]
theorem atom0304Coded_decode : atom0304 = SparsePolynomial.decodeCubic 21 atom0304Coded := by decide +kernel
theorem atom0304Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) := by
  have h := atom0304_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0304Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0305 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0305 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0305 = ((g 0) * (g 10) * (g 12)) := by
  norm_num [atom0305, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0305_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30716949294080 : Int) atom0305) := by
  rw [SparsePolynomial.eval_scale, eval_atom0305]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0305Coded : CoefficientMerge.Poly := [(nat_lit 222, Int.ofNat (nat_lit 1))]
theorem atom0305Coded_decode : atom0305 = SparsePolynomial.decodeCubic 21 atom0305Coded := by decide +kernel
theorem atom0305Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded) := by
  have h := atom0305_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0305Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0306 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0306 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0306 = ((g 0) * (g 10) * (g 13)) := by
  norm_num [atom0306, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0306_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31264753665600 : Int) atom0306) := by
  rw [SparsePolynomial.eval_scale, eval_atom0306]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0306Coded : CoefficientMerge.Poly := [(nat_lit 223, Int.ofNat (nat_lit 1))]
theorem atom0306Coded_decode : atom0306 = SparsePolynomial.decodeCubic 21 atom0306Coded := by decide +kernel
theorem atom0306Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) := by
  have h := atom0306_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0306Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0307 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0307 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0307 = ((g 0) * (g 10) * (g 14)) := by
  norm_num [atom0307, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0307_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31637328004800 : Int) atom0307) := by
  rw [SparsePolynomial.eval_scale, eval_atom0307]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0307Coded : CoefficientMerge.Poly := [(nat_lit 224, Int.ofNat (nat_lit 1))]
theorem atom0307Coded_decode : atom0307 = SparsePolynomial.decodeCubic 21 atom0307Coded := by decide +kernel
theorem atom0307Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded) := by
  have h := atom0307_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0307Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0308 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0308 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0308 = ((g 0) * (g 10) * (g 15)) := by
  norm_num [atom0308, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0308_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35314828416000 : Int) atom0308) := by
  rw [SparsePolynomial.eval_scale, eval_atom0308]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0308Coded : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 1))]
theorem atom0308Coded_decode : atom0308 = SparsePolynomial.decodeCubic 21 atom0308Coded := by decide +kernel
theorem atom0308Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) := by
  have h := atom0308_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0308Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0309 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0309 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0309 = ((g 0) * (g 10) * (g 16)) := by
  norm_num [atom0309, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0309_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28584761448600 : Int) atom0309) := by
  rw [SparsePolynomial.eval_scale, eval_atom0309]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0309Coded : CoefficientMerge.Poly := [(nat_lit 226, Int.ofNat (nat_lit 1))]
theorem atom0309Coded_decode : atom0309 = SparsePolynomial.decodeCubic 21 atom0309Coded := by decide +kernel
theorem atom0309Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) := by
  have h := atom0309_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0309Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0310 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0310 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0310 = ((g 0) * (g 10) * (g 17)) := by
  norm_num [atom0310, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0310_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27927992332800 : Int) atom0310) := by
  rw [SparsePolynomial.eval_scale, eval_atom0310]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0310Coded : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 1))]
theorem atom0310Coded_decode : atom0310 = SparsePolynomial.decodeCubic 21 atom0310Coded := by decide +kernel
theorem atom0310Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded) := by
  have h := atom0310_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0310Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0311 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0311 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0311 = ((g 0) * (g 10) * (g 18)) := by
  norm_num [atom0311, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0311_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21666826729800 : Int) atom0311) := by
  rw [SparsePolynomial.eval_scale, eval_atom0311]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0311Coded : CoefficientMerge.Poly := [(nat_lit 228, Int.ofNat (nat_lit 1))]
theorem atom0311Coded_decode : atom0311 = SparsePolynomial.decodeCubic 21 atom0311Coded := by decide +kernel
theorem atom0311Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) := by
  have h := atom0311_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0311Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0312 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0312 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0312 = ((g 0) * (g 10) * (g 19)) := by
  norm_num [atom0312, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0312_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18956883997800 : Int) atom0312) := by
  rw [SparsePolynomial.eval_scale, eval_atom0312]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0312Coded : CoefficientMerge.Poly := [(nat_lit 229, Int.ofNat (nat_lit 1))]
theorem atom0312Coded_decode : atom0312 = SparsePolynomial.decodeCubic 21 atom0312Coded := by decide +kernel
theorem atom0312Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded) := by
  have h := atom0312_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0312Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0313 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0313 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0313 = ((g 0) * (g 10) * (g 20)) := by
  norm_num [atom0313, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0313_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17385443397000 : Int) atom0313) := by
  rw [SparsePolynomial.eval_scale, eval_atom0313]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0313Coded : CoefficientMerge.Poly := [(nat_lit 230, Int.ofNat (nat_lit 1))]
theorem atom0313Coded_decode : atom0313 = SparsePolynomial.decodeCubic 21 atom0313Coded := by decide +kernel
theorem atom0313Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) := by
  have h := atom0313_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0313Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0314 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0314 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0314 = ((g 0) * (g 11) * (g 11)) := by
  norm_num [atom0314, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0314_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19284988262400 : Int) atom0314) := by
  rw [SparsePolynomial.eval_scale, eval_atom0314]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0314Coded : CoefficientMerge.Poly := [(nat_lit 242, Int.ofNat (nat_lit 1))]
theorem atom0314Coded_decode : atom0314 = SparsePolynomial.decodeCubic 21 atom0314Coded := by decide +kernel
theorem atom0314Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) := by
  have h := atom0314_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0314Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0315 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0315 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0315 = ((g 0) * (g 11) * (g 12)) := by
  norm_num [atom0315, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0315_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35899040401280 : Int) atom0315) := by
  rw [SparsePolynomial.eval_scale, eval_atom0315]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0315Coded : CoefficientMerge.Poly := [(nat_lit 243, Int.ofNat (nat_lit 1))]
theorem atom0315Coded_decode : atom0315 = SparsePolynomial.decodeCubic 21 atom0315Coded := by decide +kernel
theorem atom0315Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded) := by
  have h := atom0315_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0315Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0316 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0316 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0316 = ((g 0) * (g 11) * (g 13)) := by
  norm_num [atom0316, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0316_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33134812300800 : Int) atom0316) := by
  rw [SparsePolynomial.eval_scale, eval_atom0316]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0316Coded : CoefficientMerge.Poly := [(nat_lit 244, Int.ofNat (nat_lit 1))]
theorem atom0316Coded_decode : atom0316 = SparsePolynomial.decodeCubic 21 atom0316Coded := by decide +kernel
theorem atom0316Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) := by
  have h := atom0316_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0316Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0317 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0317 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0317 = ((g 0) * (g 11) * (g 14)) := by
  norm_num [atom0317, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0317_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33319891382400 : Int) atom0317) := by
  rw [SparsePolynomial.eval_scale, eval_atom0317]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0317Coded : CoefficientMerge.Poly := [(nat_lit 245, Int.ofNat (nat_lit 1))]
theorem atom0317Coded_decode : atom0317 = SparsePolynomial.decodeCubic 21 atom0317Coded := by decide +kernel
theorem atom0317Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded) := by
  have h := atom0317_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0317Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0318 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0318 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0318 = ((g 0) * (g 11) * (g 15)) := by
  norm_num [atom0318, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0318_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36736809580800 : Int) atom0318) := by
  rw [SparsePolynomial.eval_scale, eval_atom0318]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0318Coded : CoefficientMerge.Poly := [(nat_lit 246, Int.ofNat (nat_lit 1))]
theorem atom0318Coded_decode : atom0318 = SparsePolynomial.decodeCubic 21 atom0318Coded := by decide +kernel
theorem atom0318Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) := by
  have h := atom0318_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0318Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0319 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0319 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0319 = ((g 0) * (g 11) * (g 16)) := by
  norm_num [atom0319, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0319_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29709470649600 : Int) atom0319) := by
  rw [SparsePolynomial.eval_scale, eval_atom0319]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0319Coded : CoefficientMerge.Poly := [(nat_lit 247, Int.ofNat (nat_lit 1))]
theorem atom0319Coded_decode : atom0319 = SparsePolynomial.decodeCubic 21 atom0319Coded := by decide +kernel
theorem atom0319Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) := by
  have h := atom0319_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0319Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0320 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0320 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0320 = ((g 0) * (g 11) * (g 17)) := by
  norm_num [atom0320, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0320_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29218419820800 : Int) atom0320) := by
  rw [SparsePolynomial.eval_scale, eval_atom0320]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0320Coded : CoefficientMerge.Poly := [(nat_lit 248, Int.ofNat (nat_lit 1))]
theorem atom0320Coded_decode : atom0320 = SparsePolynomial.decodeCubic 21 atom0320Coded := by decide +kernel
theorem atom0320Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded) := by
  have h := atom0320_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0320Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0321 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0321 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0321 = ((g 0) * (g 11) * (g 18)) := by
  norm_num [atom0321, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0321_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22050818092800 : Int) atom0321) := by
  rw [SparsePolynomial.eval_scale, eval_atom0321]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0321Coded : CoefficientMerge.Poly := [(nat_lit 249, Int.ofNat (nat_lit 1))]
theorem atom0321Coded_decode : atom0321 = SparsePolynomial.decodeCubic 21 atom0321Coded := by decide +kernel
theorem atom0321Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) := by
  have h := atom0321_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0321Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0322 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0322 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0322 = ((g 0) * (g 11) * (g 19)) := by
  norm_num [atom0322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0322_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18736677388800 : Int) atom0322) := by
  rw [SparsePolynomial.eval_scale, eval_atom0322]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0322Coded : CoefficientMerge.Poly := [(nat_lit 250, Int.ofNat (nat_lit 1))]
theorem atom0322Coded_decode : atom0322 = SparsePolynomial.decodeCubic 21 atom0322Coded := by decide +kernel
theorem atom0322Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded) := by
  have h := atom0322_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0322Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0323 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0323 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0323 = ((g 0) * (g 11) * (g 20)) := by
  norm_num [atom0323, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0323_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16733923315200 : Int) atom0323) := by
  rw [SparsePolynomial.eval_scale, eval_atom0323]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0323Coded : CoefficientMerge.Poly := [(nat_lit 251, Int.ofNat (nat_lit 1))]
theorem atom0323Coded_decode : atom0323 = SparsePolynomial.decodeCubic 21 atom0323Coded := by decide +kernel
theorem atom0323Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) := by
  have h := atom0323_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0323Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0324 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0324 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0324 = ((g 0) * (g 12) * (g 12)) := by
  norm_num [atom0324, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0324_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21251467059200 : Int) atom0324) := by
  rw [SparsePolynomial.eval_scale, eval_atom0324]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0324Coded : CoefficientMerge.Poly := [(nat_lit 264, Int.ofNat (nat_lit 1))]
theorem atom0324Coded_decode : atom0324 = SparsePolynomial.decodeCubic 21 atom0324Coded := by decide +kernel
theorem atom0324Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) := by
  have h := atom0324_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0324Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0325 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0325 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0325 = ((g 0) * (g 12) * (g 13)) := by
  norm_num [atom0325, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0325_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39297939296000 : Int) atom0325) := by
  rw [SparsePolynomial.eval_scale, eval_atom0325]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0325Coded : CoefficientMerge.Poly := [(nat_lit 265, Int.ofNat (nat_lit 1))]
theorem atom0325Coded_decode : atom0325 = SparsePolynomial.decodeCubic 21 atom0325Coded := by decide +kernel
theorem atom0325Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded) := by
  have h := atom0325_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0325Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0326 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0326 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0326 = ((g 0) * (g 12) * (g 14)) := by
  norm_num [atom0326, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0326_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35912554563200 : Int) atom0326) := by
  rw [SparsePolynomial.eval_scale, eval_atom0326]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0326Coded : CoefficientMerge.Poly := [(nat_lit 266, Int.ofNat (nat_lit 1))]
theorem atom0326Coded_decode : atom0326 = SparsePolynomial.decodeCubic 21 atom0326Coded := by decide +kernel
theorem atom0326Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) := by
  have h := atom0326_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0326Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0327 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0327 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0327 = ((g 0) * (g 12) * (g 15)) := by
  norm_num [atom0327, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0327_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37646402460800 : Int) atom0327) := by
  rw [SparsePolynomial.eval_scale, eval_atom0327]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0327Coded : CoefficientMerge.Poly := [(nat_lit 267, Int.ofNat (nat_lit 1))]
theorem atom0327Coded_decode : atom0327 = SparsePolynomial.decodeCubic 21 atom0327Coded := by decide +kernel
theorem atom0327Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded) := by
  have h := atom0327_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0327Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0328 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0328 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0328 = ((g 0) * (g 12) * (g 16)) := by
  norm_num [atom0328, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0328_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30033533017600 : Int) atom0328) := by
  rw [SparsePolynomial.eval_scale, eval_atom0328]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0328Coded : CoefficientMerge.Poly := [(nat_lit 268, Int.ofNat (nat_lit 1))]
theorem atom0328Coded_decode : atom0328 = SparsePolynomial.decodeCubic 21 atom0328Coded := by decide +kernel
theorem atom0328Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) := by
  have h := atom0328_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0328Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0329 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0329 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0329 = ((g 0) * (g 12) * (g 17)) := by
  norm_num [atom0329, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0329_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26922129315200 : Int) atom0329) := by
  rw [SparsePolynomial.eval_scale, eval_atom0329]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0329Coded : CoefficientMerge.Poly := [(nat_lit 269, Int.ofNat (nat_lit 1))]
theorem atom0329Coded_decode : atom0329 = SparsePolynomial.decodeCubic 21 atom0329Coded := by decide +kernel
theorem atom0329Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) := by
  have h := atom0329_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0329Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0330 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0330 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0330 = ((g 0) * (g 12) * (g 18)) := by
  norm_num [atom0330, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0330_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18741955075200 : Int) atom0330) := by
  rw [SparsePolynomial.eval_scale, eval_atom0330]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0330Coded : CoefficientMerge.Poly := [(nat_lit 270, Int.ofNat (nat_lit 1))]
theorem atom0330Coded_decode : atom0330 = SparsePolynomial.decodeCubic 21 atom0330Coded := by decide +kernel
theorem atom0330Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded) := by
  have h := atom0330_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0330Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0331 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0331 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0331 = ((g 0) * (g 12) * (g 19)) := by
  norm_num [atom0331, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0331_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15709779478400 : Int) atom0331) := by
  rw [SparsePolynomial.eval_scale, eval_atom0331]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0331Coded : CoefficientMerge.Poly := [(nat_lit 271, Int.ofNat (nat_lit 1))]
theorem atom0331Coded_decode : atom0331 = SparsePolynomial.decodeCubic 21 atom0331Coded := by decide +kernel
theorem atom0331Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) := by
  have h := atom0331_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0331Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0332 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0332 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0332 = ((g 0) * (g 12) * (g 20)) := by
  norm_num [atom0332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0332_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11251970553600 : Int) atom0332) := by
  rw [SparsePolynomial.eval_scale, eval_atom0332]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0332Coded : CoefficientMerge.Poly := [(nat_lit 272, Int.ofNat (nat_lit 1))]
theorem atom0332Coded_decode : atom0332 = SparsePolynomial.decodeCubic 21 atom0332Coded := by decide +kernel
theorem atom0332Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded) := by
  have h := atom0332_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0332Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0333 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0333 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0333 = ((g 0) * (g 13) * (g 13)) := by
  norm_num [atom0333, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0333_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22298267001600 : Int) atom0333) := by
  rw [SparsePolynomial.eval_scale, eval_atom0333]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0333Coded : CoefficientMerge.Poly := [(nat_lit 286, Int.ofNat (nat_lit 1))]
theorem atom0333Coded_decode : atom0333 = SparsePolynomial.decodeCubic 21 atom0333Coded := by decide +kernel
theorem atom0333Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) := by
  have h := atom0333_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0333Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0334 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0334 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0334 = ((g 0) * (g 13) * (g 14)) := by
  norm_num [atom0334, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0334_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41193039456000 : Int) atom0334) := by
  rw [SparsePolynomial.eval_scale, eval_atom0334]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0334Coded : CoefficientMerge.Poly := [(nat_lit 287, Int.ofNat (nat_lit 1))]
theorem atom0334Coded_decode : atom0334 = SparsePolynomial.decodeCubic 21 atom0334Coded := by decide +kernel
theorem atom0334Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) := by
  have h := atom0334_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0334Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0335 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0335 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0335 = ((g 0) * (g 13) * (g 15)) := by
  norm_num [atom0335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0335_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39191522403600 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0335Coded : CoefficientMerge.Poly := [(nat_lit 288, Int.ofNat (nat_lit 1))]
theorem atom0335Coded_decode : atom0335 = SparsePolynomial.decodeCubic 21 atom0335Coded := by decide +kernel
theorem atom0335Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded) := by
  have h := atom0335_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0335Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block005 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 24337174377600)), (nat_lit 140, Int.ofNat (nat_lit 25039315123200)), (nat_lit 141, Int.ofNat (nat_lit 29039577235200)), (nat_lit 142, Int.ofNat (nat_lit 21558664512000)), (nat_lit 143, Int.ofNat (nat_lit 18654996729600)), (nat_lit 144, Int.ofNat (nat_lit 13125428870400)), (nat_lit 145, Int.ofNat (nat_lit 13510927180800)), (nat_lit 146, Int.ofNat (nat_lit 10819430496000)), (nat_lit 154, Int.ofNat (nat_lit 13421582466048)), (nat_lit 155, Int.ofNat (nat_lit 23660965873728)), (nat_lit 156, Int.ofNat (nat_lit 22372041369024)), (nat_lit 157, Int.ofNat (nat_lit 23033831975424)), (nat_lit 158, Int.ofNat (nat_lit 23838356994624)), (nat_lit 159, Int.ofNat (nat_lit 25176291029824)), (nat_lit 160, Int.ofNat (nat_lit 26078455353024)), (nat_lit 161, Int.ofNat (nat_lit 26761266690624)), (nat_lit 162, Int.ofNat (nat_lit 30796193398176)), (nat_lit 163, Int.ofNat (nat_lit 23976290418336)), (nat_lit 164, Int.ofNat (nat_lit 22287869204832)), (nat_lit 165, Int.ofNat (nat_lit 16973062270560)), (nat_lit 166, Int.ofNat (nat_lit 16137647557920)), (nat_lit 167, Int.ofNat (nat_lit 14405932338336)), (nat_lit 176, Int.ofNat (nat_lit 14770003348800)), (nat_lit 177, Int.ofNat (nat_lit 26552598367680)), (nat_lit 178, Int.ofNat (nat_lit 25135035962400)), (nat_lit 179, Int.ofNat (nat_lit 25813436594400)), (nat_lit 180, Int.ofNat (nat_lit 26983204780000)), (nat_lit 181, Int.ofNat (nat_lit 27823998232800)), (nat_lit 182, Int.ofNat (nat_lit 28445438700000)), (nat_lit 183, Int.ofNat (nat_lit 32314904294400)), (nat_lit 184, Int.ofNat (nat_lit 25706174665500)), (nat_lit 185, Int.ofNat (nat_lit 24255404812800)), (nat_lit 186, Int.ofNat (nat_lit 18917112734100)), (nat_lit 187, Int.ofNat (nat_lit 17491669568100)), (nat_lit 188, Int.ofNat (nat_lit 15923188782900)), (nat_lit 198, Int.ofNat (nat_lit 16313214960000)), (nat_lit 199, Int.ofNat (nat_lit 29540683226880)), (nat_lit 200, Int.ofNat (nat_lit 27605876760000)), (nat_lit 201, Int.ofNat (nat_lit 28779027592000)), (nat_lit 202, Int.ofNat (nat_lit 29516408712000)), (nat_lit 203, Int.ofNat (nat_lit 30034436846400)), (nat_lit 204, Int.ofNat (nat_lit 33814866355200)), (nat_lit 205, Int.ofNat (nat_lit 27205547783400)), (nat_lit 206, Int.ofNat (nat_lit 26091698572800)), (nat_lit 207, Int.ofNat (nat_lit 20444060460600)), (nat_lit 208, Int.ofNat (nat_lit 18430701269400)), (nat_lit 209, Int.ofNat (nat_lit 16915074334200)), (nat_lit 220, Int.ofNat (nat_lit 17758088208000)), (nat_lit 221, Int.ofNat (nat_lit 32512456529280)), (nat_lit 222, Int.ofNat (nat_lit 30716949294080)), (nat_lit 223, Int.ofNat (nat_lit 31264753665600)), (nat_lit 224, Int.ofNat (nat_lit 31637328004800)), (nat_lit 225, Int.ofNat (nat_lit 35314828416000)), (nat_lit 226, Int.ofNat (nat_lit 28584761448600)), (nat_lit 227, Int.ofNat (nat_lit 27927992332800)), (nat_lit 228, Int.ofNat (nat_lit 21666826729800)), (nat_lit 229, Int.ofNat (nat_lit 18956883997800)), (nat_lit 230, Int.ofNat (nat_lit 17385443397000)), (nat_lit 242, Int.ofNat (nat_lit 19284988262400)), (nat_lit 243, Int.ofNat (nat_lit 35899040401280)), (nat_lit 244, Int.ofNat (nat_lit 33134812300800)), (nat_lit 245, Int.ofNat (nat_lit 33319891382400)), (nat_lit 246, Int.ofNat (nat_lit 36736809580800)), (nat_lit 247, Int.ofNat (nat_lit 29709470649600)), (nat_lit 248, Int.ofNat (nat_lit 29218419820800)), (nat_lit 249, Int.ofNat (nat_lit 22050818092800)), (nat_lit 250, Int.ofNat (nat_lit 18736677388800)), (nat_lit 251, Int.ofNat (nat_lit 16733923315200)), (nat_lit 264, Int.ofNat (nat_lit 21251467059200)), (nat_lit 265, Int.ofNat (nat_lit 39297939296000)), (nat_lit 266, Int.ofNat (nat_lit 35912554563200)), (nat_lit 267, Int.ofNat (nat_lit 37646402460800)), (nat_lit 268, Int.ofNat (nat_lit 30033533017600)), (nat_lit 269, Int.ofNat (nat_lit 26922129315200)), (nat_lit 270, Int.ofNat (nat_lit 18741955075200)), (nat_lit 271, Int.ofNat (nat_lit 15709779478400)), (nat_lit 272, Int.ofNat (nat_lit 11251970553600)), (nat_lit 286, Int.ofNat (nat_lit 22298267001600)), (nat_lit 287, Int.ofNat (nat_lit 41193039456000)), (nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
def block005_data_flat000 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 24337174377600))]
theorem block005_data_flat000_step : block005_data_flat000 = (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) := by decide +kernel
theorem block005_data_flat000_original : block005_data_flat000 = (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) := by
  rw [block005_data_flat000_step]
def block005_data_flat001 : CoefficientMerge.Poly := [(nat_lit 140, Int.ofNat (nat_lit 25039315123200))]
theorem block005_data_flat001_step : block005_data_flat001 = (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded) := by decide +kernel
theorem block005_data_flat001_original : block005_data_flat001 = (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded) := by
  rw [block005_data_flat001_step]
def block005_data_flat002 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 24337174377600)), (nat_lit 140, Int.ofNat (nat_lit 25039315123200))]
theorem block005_data_flat002_step : block005_data_flat002 = (CoefficientMerge.fastMerge block005_data_flat000 block005_data_flat001) := by decide +kernel
theorem block005_data_flat002_original : block005_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded)) := by
  rw [block005_data_flat002_step, block005_data_flat000_original, block005_data_flat001_original]
def block005_data_flat003 : CoefficientMerge.Poly := [(nat_lit 141, Int.ofNat (nat_lit 29039577235200))]
theorem block005_data_flat003_step : block005_data_flat003 = (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) := by decide +kernel
theorem block005_data_flat003_original : block005_data_flat003 = (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) := by
  rw [block005_data_flat003_step]
def block005_data_flat004 : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 21558664512000))]
theorem block005_data_flat004_step : block005_data_flat004 = (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) := by decide +kernel
theorem block005_data_flat004_original : block005_data_flat004 = (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) := by
  rw [block005_data_flat004_step]
def block005_data_flat005 : CoefficientMerge.Poly := [(nat_lit 143, Int.ofNat (nat_lit 18654996729600))]
theorem block005_data_flat005_step : block005_data_flat005 = (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded) := by decide +kernel
theorem block005_data_flat005_original : block005_data_flat005 = (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded) := by
  rw [block005_data_flat005_step]
def block005_data_flat006 : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 21558664512000)), (nat_lit 143, Int.ofNat (nat_lit 18654996729600))]
theorem block005_data_flat006_step : block005_data_flat006 = (CoefficientMerge.fastMerge block005_data_flat004 block005_data_flat005) := by decide +kernel
theorem block005_data_flat006_original : block005_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded)) := by
  rw [block005_data_flat006_step, block005_data_flat004_original, block005_data_flat005_original]
def block005_data_flat007 : CoefficientMerge.Poly := [(nat_lit 141, Int.ofNat (nat_lit 29039577235200)), (nat_lit 142, Int.ofNat (nat_lit 21558664512000)), (nat_lit 143, Int.ofNat (nat_lit 18654996729600))]
theorem block005_data_flat007_step : block005_data_flat007 = (CoefficientMerge.fastMerge block005_data_flat003 block005_data_flat006) := by decide +kernel
theorem block005_data_flat007_original : block005_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded))) := by
  rw [block005_data_flat007_step, block005_data_flat003_original, block005_data_flat006_original]
def block005_data_flat008 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 24337174377600)), (nat_lit 140, Int.ofNat (nat_lit 25039315123200)), (nat_lit 141, Int.ofNat (nat_lit 29039577235200)), (nat_lit 142, Int.ofNat (nat_lit 21558664512000)), (nat_lit 143, Int.ofNat (nat_lit 18654996729600))]
theorem block005_data_flat008_step : block005_data_flat008 = (CoefficientMerge.fastMerge block005_data_flat002 block005_data_flat007) := by decide +kernel
theorem block005_data_flat008_original : block005_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded)))) := by
  rw [block005_data_flat008_step, block005_data_flat002_original, block005_data_flat007_original]
def block005_data_flat009 : CoefficientMerge.Poly := [(nat_lit 144, Int.ofNat (nat_lit 13125428870400))]
theorem block005_data_flat009_step : block005_data_flat009 = (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) := by decide +kernel
theorem block005_data_flat009_original : block005_data_flat009 = (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) := by
  rw [block005_data_flat009_step]
def block005_data_flat010 : CoefficientMerge.Poly := [(nat_lit 145, Int.ofNat (nat_lit 13510927180800))]
theorem block005_data_flat010_step : block005_data_flat010 = (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded) := by decide +kernel
theorem block005_data_flat010_original : block005_data_flat010 = (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded) := by
  rw [block005_data_flat010_step]
def block005_data_flat011 : CoefficientMerge.Poly := [(nat_lit 144, Int.ofNat (nat_lit 13125428870400)), (nat_lit 145, Int.ofNat (nat_lit 13510927180800))]
theorem block005_data_flat011_step : block005_data_flat011 = (CoefficientMerge.fastMerge block005_data_flat009 block005_data_flat010) := by decide +kernel
theorem block005_data_flat011_original : block005_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded)) := by
  rw [block005_data_flat011_step, block005_data_flat009_original, block005_data_flat010_original]
def block005_data_flat012 : CoefficientMerge.Poly := [(nat_lit 146, Int.ofNat (nat_lit 10819430496000))]
theorem block005_data_flat012_step : block005_data_flat012 = (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) := by decide +kernel
theorem block005_data_flat012_original : block005_data_flat012 = (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) := by
  rw [block005_data_flat012_step]
def block005_data_flat013 : CoefficientMerge.Poly := [(nat_lit 154, Int.ofNat (nat_lit 13421582466048))]
theorem block005_data_flat013_step : block005_data_flat013 = (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) := by decide +kernel
theorem block005_data_flat013_original : block005_data_flat013 = (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) := by
  rw [block005_data_flat013_step]
def block005_data_flat014 : CoefficientMerge.Poly := [(nat_lit 155, Int.ofNat (nat_lit 23660965873728))]
theorem block005_data_flat014_step : block005_data_flat014 = (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded) := by decide +kernel
theorem block005_data_flat014_original : block005_data_flat014 = (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded) := by
  rw [block005_data_flat014_step]
def block005_data_flat015 : CoefficientMerge.Poly := [(nat_lit 154, Int.ofNat (nat_lit 13421582466048)), (nat_lit 155, Int.ofNat (nat_lit 23660965873728))]
theorem block005_data_flat015_step : block005_data_flat015 = (CoefficientMerge.fastMerge block005_data_flat013 block005_data_flat014) := by decide +kernel
theorem block005_data_flat015_original : block005_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded)) := by
  rw [block005_data_flat015_step, block005_data_flat013_original, block005_data_flat014_original]
def block005_data_flat016 : CoefficientMerge.Poly := [(nat_lit 146, Int.ofNat (nat_lit 10819430496000)), (nat_lit 154, Int.ofNat (nat_lit 13421582466048)), (nat_lit 155, Int.ofNat (nat_lit 23660965873728))]
theorem block005_data_flat016_step : block005_data_flat016 = (CoefficientMerge.fastMerge block005_data_flat012 block005_data_flat015) := by decide +kernel
theorem block005_data_flat016_original : block005_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded))) := by
  rw [block005_data_flat016_step, block005_data_flat012_original, block005_data_flat015_original]
def block005_data_flat017 : CoefficientMerge.Poly := [(nat_lit 144, Int.ofNat (nat_lit 13125428870400)), (nat_lit 145, Int.ofNat (nat_lit 13510927180800)), (nat_lit 146, Int.ofNat (nat_lit 10819430496000)), (nat_lit 154, Int.ofNat (nat_lit 13421582466048)), (nat_lit 155, Int.ofNat (nat_lit 23660965873728))]
theorem block005_data_flat017_step : block005_data_flat017 = (CoefficientMerge.fastMerge block005_data_flat011 block005_data_flat016) := by decide +kernel
theorem block005_data_flat017_original : block005_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded)))) := by
  rw [block005_data_flat017_step, block005_data_flat011_original, block005_data_flat016_original]
def block005_data_flat018 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 24337174377600)), (nat_lit 140, Int.ofNat (nat_lit 25039315123200)), (nat_lit 141, Int.ofNat (nat_lit 29039577235200)), (nat_lit 142, Int.ofNat (nat_lit 21558664512000)), (nat_lit 143, Int.ofNat (nat_lit 18654996729600)), (nat_lit 144, Int.ofNat (nat_lit 13125428870400)), (nat_lit 145, Int.ofNat (nat_lit 13510927180800)), (nat_lit 146, Int.ofNat (nat_lit 10819430496000)), (nat_lit 154, Int.ofNat (nat_lit 13421582466048)), (nat_lit 155, Int.ofNat (nat_lit 23660965873728))]
theorem block005_data_flat018_step : block005_data_flat018 = (CoefficientMerge.fastMerge block005_data_flat008 block005_data_flat017) := by decide +kernel
theorem block005_data_flat018_original : block005_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded))))) := by
  rw [block005_data_flat018_step, block005_data_flat008_original, block005_data_flat017_original]
def block005_data_flat019 : CoefficientMerge.Poly := [(nat_lit 156, Int.ofNat (nat_lit 22372041369024))]
theorem block005_data_flat019_step : block005_data_flat019 = (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) := by decide +kernel
theorem block005_data_flat019_original : block005_data_flat019 = (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) := by
  rw [block005_data_flat019_step]
def block005_data_flat020 : CoefficientMerge.Poly := [(nat_lit 157, Int.ofNat (nat_lit 23033831975424))]
theorem block005_data_flat020_step : block005_data_flat020 = (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded) := by decide +kernel
theorem block005_data_flat020_original : block005_data_flat020 = (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded) := by
  rw [block005_data_flat020_step]
def block005_data_flat021 : CoefficientMerge.Poly := [(nat_lit 156, Int.ofNat (nat_lit 22372041369024)), (nat_lit 157, Int.ofNat (nat_lit 23033831975424))]
theorem block005_data_flat021_step : block005_data_flat021 = (CoefficientMerge.fastMerge block005_data_flat019 block005_data_flat020) := by decide +kernel
theorem block005_data_flat021_original : block005_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded)) := by
  rw [block005_data_flat021_step, block005_data_flat019_original, block005_data_flat020_original]
def block005_data_flat022 : CoefficientMerge.Poly := [(nat_lit 158, Int.ofNat (nat_lit 23838356994624))]
theorem block005_data_flat022_step : block005_data_flat022 = (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) := by decide +kernel
theorem block005_data_flat022_original : block005_data_flat022 = (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) := by
  rw [block005_data_flat022_step]
def block005_data_flat023 : CoefficientMerge.Poly := [(nat_lit 159, Int.ofNat (nat_lit 25176291029824))]
theorem block005_data_flat023_step : block005_data_flat023 = (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) := by decide +kernel
theorem block005_data_flat023_original : block005_data_flat023 = (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) := by
  rw [block005_data_flat023_step]
def block005_data_flat024 : CoefficientMerge.Poly := [(nat_lit 160, Int.ofNat (nat_lit 26078455353024))]
theorem block005_data_flat024_step : block005_data_flat024 = (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded) := by decide +kernel
theorem block005_data_flat024_original : block005_data_flat024 = (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded) := by
  rw [block005_data_flat024_step]
def block005_data_flat025 : CoefficientMerge.Poly := [(nat_lit 159, Int.ofNat (nat_lit 25176291029824)), (nat_lit 160, Int.ofNat (nat_lit 26078455353024))]
theorem block005_data_flat025_step : block005_data_flat025 = (CoefficientMerge.fastMerge block005_data_flat023 block005_data_flat024) := by decide +kernel
theorem block005_data_flat025_original : block005_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded)) := by
  rw [block005_data_flat025_step, block005_data_flat023_original, block005_data_flat024_original]
def block005_data_flat026 : CoefficientMerge.Poly := [(nat_lit 158, Int.ofNat (nat_lit 23838356994624)), (nat_lit 159, Int.ofNat (nat_lit 25176291029824)), (nat_lit 160, Int.ofNat (nat_lit 26078455353024))]
theorem block005_data_flat026_step : block005_data_flat026 = (CoefficientMerge.fastMerge block005_data_flat022 block005_data_flat025) := by decide +kernel
theorem block005_data_flat026_original : block005_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded))) := by
  rw [block005_data_flat026_step, block005_data_flat022_original, block005_data_flat025_original]
def block005_data_flat027 : CoefficientMerge.Poly := [(nat_lit 156, Int.ofNat (nat_lit 22372041369024)), (nat_lit 157, Int.ofNat (nat_lit 23033831975424)), (nat_lit 158, Int.ofNat (nat_lit 23838356994624)), (nat_lit 159, Int.ofNat (nat_lit 25176291029824)), (nat_lit 160, Int.ofNat (nat_lit 26078455353024))]
theorem block005_data_flat027_step : block005_data_flat027 = (CoefficientMerge.fastMerge block005_data_flat021 block005_data_flat026) := by decide +kernel
theorem block005_data_flat027_original : block005_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded)))) := by
  rw [block005_data_flat027_step, block005_data_flat021_original, block005_data_flat026_original]
def block005_data_flat028 : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 26761266690624))]
theorem block005_data_flat028_step : block005_data_flat028 = (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) := by decide +kernel
theorem block005_data_flat028_original : block005_data_flat028 = (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) := by
  rw [block005_data_flat028_step]
def block005_data_flat029 : CoefficientMerge.Poly := [(nat_lit 162, Int.ofNat (nat_lit 30796193398176))]
theorem block005_data_flat029_step : block005_data_flat029 = (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded) := by decide +kernel
theorem block005_data_flat029_original : block005_data_flat029 = (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded) := by
  rw [block005_data_flat029_step]
def block005_data_flat030 : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 26761266690624)), (nat_lit 162, Int.ofNat (nat_lit 30796193398176))]
theorem block005_data_flat030_step : block005_data_flat030 = (CoefficientMerge.fastMerge block005_data_flat028 block005_data_flat029) := by decide +kernel
theorem block005_data_flat030_original : block005_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded)) := by
  rw [block005_data_flat030_step, block005_data_flat028_original, block005_data_flat029_original]
def block005_data_flat031 : CoefficientMerge.Poly := [(nat_lit 163, Int.ofNat (nat_lit 23976290418336))]
theorem block005_data_flat031_step : block005_data_flat031 = (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) := by decide +kernel
theorem block005_data_flat031_original : block005_data_flat031 = (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) := by
  rw [block005_data_flat031_step]
def block005_data_flat032 : CoefficientMerge.Poly := [(nat_lit 164, Int.ofNat (nat_lit 22287869204832))]
theorem block005_data_flat032_step : block005_data_flat032 = (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) := by decide +kernel
theorem block005_data_flat032_original : block005_data_flat032 = (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) := by
  rw [block005_data_flat032_step]
def block005_data_flat033 : CoefficientMerge.Poly := [(nat_lit 165, Int.ofNat (nat_lit 16973062270560))]
theorem block005_data_flat033_step : block005_data_flat033 = (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded) := by decide +kernel
theorem block005_data_flat033_original : block005_data_flat033 = (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded) := by
  rw [block005_data_flat033_step]
def block005_data_flat034 : CoefficientMerge.Poly := [(nat_lit 164, Int.ofNat (nat_lit 22287869204832)), (nat_lit 165, Int.ofNat (nat_lit 16973062270560))]
theorem block005_data_flat034_step : block005_data_flat034 = (CoefficientMerge.fastMerge block005_data_flat032 block005_data_flat033) := by decide +kernel
theorem block005_data_flat034_original : block005_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded)) := by
  rw [block005_data_flat034_step, block005_data_flat032_original, block005_data_flat033_original]
def block005_data_flat035 : CoefficientMerge.Poly := [(nat_lit 163, Int.ofNat (nat_lit 23976290418336)), (nat_lit 164, Int.ofNat (nat_lit 22287869204832)), (nat_lit 165, Int.ofNat (nat_lit 16973062270560))]
theorem block005_data_flat035_step : block005_data_flat035 = (CoefficientMerge.fastMerge block005_data_flat031 block005_data_flat034) := by decide +kernel
theorem block005_data_flat035_original : block005_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded))) := by
  rw [block005_data_flat035_step, block005_data_flat031_original, block005_data_flat034_original]
def block005_data_flat036 : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 26761266690624)), (nat_lit 162, Int.ofNat (nat_lit 30796193398176)), (nat_lit 163, Int.ofNat (nat_lit 23976290418336)), (nat_lit 164, Int.ofNat (nat_lit 22287869204832)), (nat_lit 165, Int.ofNat (nat_lit 16973062270560))]
theorem block005_data_flat036_step : block005_data_flat036 = (CoefficientMerge.fastMerge block005_data_flat030 block005_data_flat035) := by decide +kernel
theorem block005_data_flat036_original : block005_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded)))) := by
  rw [block005_data_flat036_step, block005_data_flat030_original, block005_data_flat035_original]
def block005_data_flat037 : CoefficientMerge.Poly := [(nat_lit 156, Int.ofNat (nat_lit 22372041369024)), (nat_lit 157, Int.ofNat (nat_lit 23033831975424)), (nat_lit 158, Int.ofNat (nat_lit 23838356994624)), (nat_lit 159, Int.ofNat (nat_lit 25176291029824)), (nat_lit 160, Int.ofNat (nat_lit 26078455353024)), (nat_lit 161, Int.ofNat (nat_lit 26761266690624)), (nat_lit 162, Int.ofNat (nat_lit 30796193398176)), (nat_lit 163, Int.ofNat (nat_lit 23976290418336)), (nat_lit 164, Int.ofNat (nat_lit 22287869204832)), (nat_lit 165, Int.ofNat (nat_lit 16973062270560))]
theorem block005_data_flat037_step : block005_data_flat037 = (CoefficientMerge.fastMerge block005_data_flat027 block005_data_flat036) := by decide +kernel
theorem block005_data_flat037_original : block005_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded))))) := by
  rw [block005_data_flat037_step, block005_data_flat027_original, block005_data_flat036_original]
def block005_data_flat038 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 24337174377600)), (nat_lit 140, Int.ofNat (nat_lit 25039315123200)), (nat_lit 141, Int.ofNat (nat_lit 29039577235200)), (nat_lit 142, Int.ofNat (nat_lit 21558664512000)), (nat_lit 143, Int.ofNat (nat_lit 18654996729600)), (nat_lit 144, Int.ofNat (nat_lit 13125428870400)), (nat_lit 145, Int.ofNat (nat_lit 13510927180800)), (nat_lit 146, Int.ofNat (nat_lit 10819430496000)), (nat_lit 154, Int.ofNat (nat_lit 13421582466048)), (nat_lit 155, Int.ofNat (nat_lit 23660965873728)), (nat_lit 156, Int.ofNat (nat_lit 22372041369024)), (nat_lit 157, Int.ofNat (nat_lit 23033831975424)), (nat_lit 158, Int.ofNat (nat_lit 23838356994624)), (nat_lit 159, Int.ofNat (nat_lit 25176291029824)), (nat_lit 160, Int.ofNat (nat_lit 26078455353024)), (nat_lit 161, Int.ofNat (nat_lit 26761266690624)), (nat_lit 162, Int.ofNat (nat_lit 30796193398176)), (nat_lit 163, Int.ofNat (nat_lit 23976290418336)), (nat_lit 164, Int.ofNat (nat_lit 22287869204832)), (nat_lit 165, Int.ofNat (nat_lit 16973062270560))]
theorem block005_data_flat038_step : block005_data_flat038 = (CoefficientMerge.fastMerge block005_data_flat018 block005_data_flat037) := by decide +kernel
theorem block005_data_flat038_original : block005_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded)))))) := by
  rw [block005_data_flat038_step, block005_data_flat018_original, block005_data_flat037_original]
def block005_data_flat039 : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 16137647557920))]
theorem block005_data_flat039_step : block005_data_flat039 = (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) := by decide +kernel
theorem block005_data_flat039_original : block005_data_flat039 = (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) := by
  rw [block005_data_flat039_step]
def block005_data_flat040 : CoefficientMerge.Poly := [(nat_lit 167, Int.ofNat (nat_lit 14405932338336))]
theorem block005_data_flat040_step : block005_data_flat040 = (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded) := by decide +kernel
theorem block005_data_flat040_original : block005_data_flat040 = (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded) := by
  rw [block005_data_flat040_step]
def block005_data_flat041 : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 16137647557920)), (nat_lit 167, Int.ofNat (nat_lit 14405932338336))]
theorem block005_data_flat041_step : block005_data_flat041 = (CoefficientMerge.fastMerge block005_data_flat039 block005_data_flat040) := by decide +kernel
theorem block005_data_flat041_original : block005_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded)) := by
  rw [block005_data_flat041_step, block005_data_flat039_original, block005_data_flat040_original]
def block005_data_flat042 : CoefficientMerge.Poly := [(nat_lit 176, Int.ofNat (nat_lit 14770003348800))]
theorem block005_data_flat042_step : block005_data_flat042 = (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) := by decide +kernel
theorem block005_data_flat042_original : block005_data_flat042 = (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) := by
  rw [block005_data_flat042_step]
def block005_data_flat043 : CoefficientMerge.Poly := [(nat_lit 177, Int.ofNat (nat_lit 26552598367680))]
theorem block005_data_flat043_step : block005_data_flat043 = (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) := by decide +kernel
theorem block005_data_flat043_original : block005_data_flat043 = (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) := by
  rw [block005_data_flat043_step]
def block005_data_flat044 : CoefficientMerge.Poly := [(nat_lit 178, Int.ofNat (nat_lit 25135035962400))]
theorem block005_data_flat044_step : block005_data_flat044 = (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded) := by decide +kernel
theorem block005_data_flat044_original : block005_data_flat044 = (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded) := by
  rw [block005_data_flat044_step]
def block005_data_flat045 : CoefficientMerge.Poly := [(nat_lit 177, Int.ofNat (nat_lit 26552598367680)), (nat_lit 178, Int.ofNat (nat_lit 25135035962400))]
theorem block005_data_flat045_step : block005_data_flat045 = (CoefficientMerge.fastMerge block005_data_flat043 block005_data_flat044) := by decide +kernel
theorem block005_data_flat045_original : block005_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded)) := by
  rw [block005_data_flat045_step, block005_data_flat043_original, block005_data_flat044_original]
def block005_data_flat046 : CoefficientMerge.Poly := [(nat_lit 176, Int.ofNat (nat_lit 14770003348800)), (nat_lit 177, Int.ofNat (nat_lit 26552598367680)), (nat_lit 178, Int.ofNat (nat_lit 25135035962400))]
theorem block005_data_flat046_step : block005_data_flat046 = (CoefficientMerge.fastMerge block005_data_flat042 block005_data_flat045) := by decide +kernel
theorem block005_data_flat046_original : block005_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded))) := by
  rw [block005_data_flat046_step, block005_data_flat042_original, block005_data_flat045_original]
def block005_data_flat047 : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 16137647557920)), (nat_lit 167, Int.ofNat (nat_lit 14405932338336)), (nat_lit 176, Int.ofNat (nat_lit 14770003348800)), (nat_lit 177, Int.ofNat (nat_lit 26552598367680)), (nat_lit 178, Int.ofNat (nat_lit 25135035962400))]
theorem block005_data_flat047_step : block005_data_flat047 = (CoefficientMerge.fastMerge block005_data_flat041 block005_data_flat046) := by decide +kernel
theorem block005_data_flat047_original : block005_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded)))) := by
  rw [block005_data_flat047_step, block005_data_flat041_original, block005_data_flat046_original]
def block005_data_flat048 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 25813436594400))]
theorem block005_data_flat048_step : block005_data_flat048 = (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) := by decide +kernel
theorem block005_data_flat048_original : block005_data_flat048 = (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) := by
  rw [block005_data_flat048_step]
def block005_data_flat049 : CoefficientMerge.Poly := [(nat_lit 180, Int.ofNat (nat_lit 26983204780000))]
theorem block005_data_flat049_step : block005_data_flat049 = (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded) := by decide +kernel
theorem block005_data_flat049_original : block005_data_flat049 = (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded) := by
  rw [block005_data_flat049_step]
def block005_data_flat050 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 25813436594400)), (nat_lit 180, Int.ofNat (nat_lit 26983204780000))]
theorem block005_data_flat050_step : block005_data_flat050 = (CoefficientMerge.fastMerge block005_data_flat048 block005_data_flat049) := by decide +kernel
theorem block005_data_flat050_original : block005_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded)) := by
  rw [block005_data_flat050_step, block005_data_flat048_original, block005_data_flat049_original]
def block005_data_flat051 : CoefficientMerge.Poly := [(nat_lit 181, Int.ofNat (nat_lit 27823998232800))]
theorem block005_data_flat051_step : block005_data_flat051 = (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) := by decide +kernel
theorem block005_data_flat051_original : block005_data_flat051 = (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) := by
  rw [block005_data_flat051_step]
def block005_data_flat052 : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 28445438700000))]
theorem block005_data_flat052_step : block005_data_flat052 = (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) := by decide +kernel
theorem block005_data_flat052_original : block005_data_flat052 = (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) := by
  rw [block005_data_flat052_step]
def block005_data_flat053 : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 32314904294400))]
theorem block005_data_flat053_step : block005_data_flat053 = (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded) := by decide +kernel
theorem block005_data_flat053_original : block005_data_flat053 = (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded) := by
  rw [block005_data_flat053_step]
def block005_data_flat054 : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 28445438700000)), (nat_lit 183, Int.ofNat (nat_lit 32314904294400))]
theorem block005_data_flat054_step : block005_data_flat054 = (CoefficientMerge.fastMerge block005_data_flat052 block005_data_flat053) := by decide +kernel
theorem block005_data_flat054_original : block005_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded)) := by
  rw [block005_data_flat054_step, block005_data_flat052_original, block005_data_flat053_original]
def block005_data_flat055 : CoefficientMerge.Poly := [(nat_lit 181, Int.ofNat (nat_lit 27823998232800)), (nat_lit 182, Int.ofNat (nat_lit 28445438700000)), (nat_lit 183, Int.ofNat (nat_lit 32314904294400))]
theorem block005_data_flat055_step : block005_data_flat055 = (CoefficientMerge.fastMerge block005_data_flat051 block005_data_flat054) := by decide +kernel
theorem block005_data_flat055_original : block005_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded))) := by
  rw [block005_data_flat055_step, block005_data_flat051_original, block005_data_flat054_original]
def block005_data_flat056 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 25813436594400)), (nat_lit 180, Int.ofNat (nat_lit 26983204780000)), (nat_lit 181, Int.ofNat (nat_lit 27823998232800)), (nat_lit 182, Int.ofNat (nat_lit 28445438700000)), (nat_lit 183, Int.ofNat (nat_lit 32314904294400))]
theorem block005_data_flat056_step : block005_data_flat056 = (CoefficientMerge.fastMerge block005_data_flat050 block005_data_flat055) := by decide +kernel
theorem block005_data_flat056_original : block005_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded)))) := by
  rw [block005_data_flat056_step, block005_data_flat050_original, block005_data_flat055_original]
def block005_data_flat057 : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 16137647557920)), (nat_lit 167, Int.ofNat (nat_lit 14405932338336)), (nat_lit 176, Int.ofNat (nat_lit 14770003348800)), (nat_lit 177, Int.ofNat (nat_lit 26552598367680)), (nat_lit 178, Int.ofNat (nat_lit 25135035962400)), (nat_lit 179, Int.ofNat (nat_lit 25813436594400)), (nat_lit 180, Int.ofNat (nat_lit 26983204780000)), (nat_lit 181, Int.ofNat (nat_lit 27823998232800)), (nat_lit 182, Int.ofNat (nat_lit 28445438700000)), (nat_lit 183, Int.ofNat (nat_lit 32314904294400))]
theorem block005_data_flat057_step : block005_data_flat057 = (CoefficientMerge.fastMerge block005_data_flat047 block005_data_flat056) := by decide +kernel
theorem block005_data_flat057_original : block005_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded))))) := by
  rw [block005_data_flat057_step, block005_data_flat047_original, block005_data_flat056_original]
def block005_data_flat058 : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 25706174665500))]
theorem block005_data_flat058_step : block005_data_flat058 = (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) := by decide +kernel
theorem block005_data_flat058_original : block005_data_flat058 = (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) := by
  rw [block005_data_flat058_step]
def block005_data_flat059 : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 24255404812800))]
theorem block005_data_flat059_step : block005_data_flat059 = (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded) := by decide +kernel
theorem block005_data_flat059_original : block005_data_flat059 = (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded) := by
  rw [block005_data_flat059_step]
def block005_data_flat060 : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 25706174665500)), (nat_lit 185, Int.ofNat (nat_lit 24255404812800))]
theorem block005_data_flat060_step : block005_data_flat060 = (CoefficientMerge.fastMerge block005_data_flat058 block005_data_flat059) := by decide +kernel
theorem block005_data_flat060_original : block005_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded)) := by
  rw [block005_data_flat060_step, block005_data_flat058_original, block005_data_flat059_original]
def block005_data_flat061 : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 18917112734100))]
theorem block005_data_flat061_step : block005_data_flat061 = (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) := by decide +kernel
theorem block005_data_flat061_original : block005_data_flat061 = (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) := by
  rw [block005_data_flat061_step]
def block005_data_flat062 : CoefficientMerge.Poly := [(nat_lit 187, Int.ofNat (nat_lit 17491669568100))]
theorem block005_data_flat062_step : block005_data_flat062 = (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) := by decide +kernel
theorem block005_data_flat062_original : block005_data_flat062 = (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) := by
  rw [block005_data_flat062_step]
def block005_data_flat063 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 15923188782900))]
theorem block005_data_flat063_step : block005_data_flat063 = (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded) := by decide +kernel
theorem block005_data_flat063_original : block005_data_flat063 = (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded) := by
  rw [block005_data_flat063_step]
def block005_data_flat064 : CoefficientMerge.Poly := [(nat_lit 187, Int.ofNat (nat_lit 17491669568100)), (nat_lit 188, Int.ofNat (nat_lit 15923188782900))]
theorem block005_data_flat064_step : block005_data_flat064 = (CoefficientMerge.fastMerge block005_data_flat062 block005_data_flat063) := by decide +kernel
theorem block005_data_flat064_original : block005_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded)) := by
  rw [block005_data_flat064_step, block005_data_flat062_original, block005_data_flat063_original]
def block005_data_flat065 : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 18917112734100)), (nat_lit 187, Int.ofNat (nat_lit 17491669568100)), (nat_lit 188, Int.ofNat (nat_lit 15923188782900))]
theorem block005_data_flat065_step : block005_data_flat065 = (CoefficientMerge.fastMerge block005_data_flat061 block005_data_flat064) := by decide +kernel
theorem block005_data_flat065_original : block005_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded))) := by
  rw [block005_data_flat065_step, block005_data_flat061_original, block005_data_flat064_original]
def block005_data_flat066 : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 25706174665500)), (nat_lit 185, Int.ofNat (nat_lit 24255404812800)), (nat_lit 186, Int.ofNat (nat_lit 18917112734100)), (nat_lit 187, Int.ofNat (nat_lit 17491669568100)), (nat_lit 188, Int.ofNat (nat_lit 15923188782900))]
theorem block005_data_flat066_step : block005_data_flat066 = (CoefficientMerge.fastMerge block005_data_flat060 block005_data_flat065) := by decide +kernel
theorem block005_data_flat066_original : block005_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded)))) := by
  rw [block005_data_flat066_step, block005_data_flat060_original, block005_data_flat065_original]
def block005_data_flat067 : CoefficientMerge.Poly := [(nat_lit 198, Int.ofNat (nat_lit 16313214960000))]
theorem block005_data_flat067_step : block005_data_flat067 = (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) := by decide +kernel
theorem block005_data_flat067_original : block005_data_flat067 = (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) := by
  rw [block005_data_flat067_step]
def block005_data_flat068 : CoefficientMerge.Poly := [(nat_lit 199, Int.ofNat (nat_lit 29540683226880))]
theorem block005_data_flat068_step : block005_data_flat068 = (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded) := by decide +kernel
theorem block005_data_flat068_original : block005_data_flat068 = (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded) := by
  rw [block005_data_flat068_step]
def block005_data_flat069 : CoefficientMerge.Poly := [(nat_lit 198, Int.ofNat (nat_lit 16313214960000)), (nat_lit 199, Int.ofNat (nat_lit 29540683226880))]
theorem block005_data_flat069_step : block005_data_flat069 = (CoefficientMerge.fastMerge block005_data_flat067 block005_data_flat068) := by decide +kernel
theorem block005_data_flat069_original : block005_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded)) := by
  rw [block005_data_flat069_step, block005_data_flat067_original, block005_data_flat068_original]
def block005_data_flat070 : CoefficientMerge.Poly := [(nat_lit 200, Int.ofNat (nat_lit 27605876760000))]
theorem block005_data_flat070_step : block005_data_flat070 = (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) := by decide +kernel
theorem block005_data_flat070_original : block005_data_flat070 = (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) := by
  rw [block005_data_flat070_step]
def block005_data_flat071 : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 28779027592000))]
theorem block005_data_flat071_step : block005_data_flat071 = (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) := by decide +kernel
theorem block005_data_flat071_original : block005_data_flat071 = (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) := by
  rw [block005_data_flat071_step]
def block005_data_flat072 : CoefficientMerge.Poly := [(nat_lit 202, Int.ofNat (nat_lit 29516408712000))]
theorem block005_data_flat072_step : block005_data_flat072 = (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded) := by decide +kernel
theorem block005_data_flat072_original : block005_data_flat072 = (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded) := by
  rw [block005_data_flat072_step]
def block005_data_flat073 : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 28779027592000)), (nat_lit 202, Int.ofNat (nat_lit 29516408712000))]
theorem block005_data_flat073_step : block005_data_flat073 = (CoefficientMerge.fastMerge block005_data_flat071 block005_data_flat072) := by decide +kernel
theorem block005_data_flat073_original : block005_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded)) := by
  rw [block005_data_flat073_step, block005_data_flat071_original, block005_data_flat072_original]
def block005_data_flat074 : CoefficientMerge.Poly := [(nat_lit 200, Int.ofNat (nat_lit 27605876760000)), (nat_lit 201, Int.ofNat (nat_lit 28779027592000)), (nat_lit 202, Int.ofNat (nat_lit 29516408712000))]
theorem block005_data_flat074_step : block005_data_flat074 = (CoefficientMerge.fastMerge block005_data_flat070 block005_data_flat073) := by decide +kernel
theorem block005_data_flat074_original : block005_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded))) := by
  rw [block005_data_flat074_step, block005_data_flat070_original, block005_data_flat073_original]
def block005_data_flat075 : CoefficientMerge.Poly := [(nat_lit 198, Int.ofNat (nat_lit 16313214960000)), (nat_lit 199, Int.ofNat (nat_lit 29540683226880)), (nat_lit 200, Int.ofNat (nat_lit 27605876760000)), (nat_lit 201, Int.ofNat (nat_lit 28779027592000)), (nat_lit 202, Int.ofNat (nat_lit 29516408712000))]
theorem block005_data_flat075_step : block005_data_flat075 = (CoefficientMerge.fastMerge block005_data_flat069 block005_data_flat074) := by decide +kernel
theorem block005_data_flat075_original : block005_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded)))) := by
  rw [block005_data_flat075_step, block005_data_flat069_original, block005_data_flat074_original]
def block005_data_flat076 : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 25706174665500)), (nat_lit 185, Int.ofNat (nat_lit 24255404812800)), (nat_lit 186, Int.ofNat (nat_lit 18917112734100)), (nat_lit 187, Int.ofNat (nat_lit 17491669568100)), (nat_lit 188, Int.ofNat (nat_lit 15923188782900)), (nat_lit 198, Int.ofNat (nat_lit 16313214960000)), (nat_lit 199, Int.ofNat (nat_lit 29540683226880)), (nat_lit 200, Int.ofNat (nat_lit 27605876760000)), (nat_lit 201, Int.ofNat (nat_lit 28779027592000)), (nat_lit 202, Int.ofNat (nat_lit 29516408712000))]
theorem block005_data_flat076_step : block005_data_flat076 = (CoefficientMerge.fastMerge block005_data_flat066 block005_data_flat075) := by decide +kernel
theorem block005_data_flat076_original : block005_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded))))) := by
  rw [block005_data_flat076_step, block005_data_flat066_original, block005_data_flat075_original]
def block005_data_flat077 : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 16137647557920)), (nat_lit 167, Int.ofNat (nat_lit 14405932338336)), (nat_lit 176, Int.ofNat (nat_lit 14770003348800)), (nat_lit 177, Int.ofNat (nat_lit 26552598367680)), (nat_lit 178, Int.ofNat (nat_lit 25135035962400)), (nat_lit 179, Int.ofNat (nat_lit 25813436594400)), (nat_lit 180, Int.ofNat (nat_lit 26983204780000)), (nat_lit 181, Int.ofNat (nat_lit 27823998232800)), (nat_lit 182, Int.ofNat (nat_lit 28445438700000)), (nat_lit 183, Int.ofNat (nat_lit 32314904294400)), (nat_lit 184, Int.ofNat (nat_lit 25706174665500)), (nat_lit 185, Int.ofNat (nat_lit 24255404812800)), (nat_lit 186, Int.ofNat (nat_lit 18917112734100)), (nat_lit 187, Int.ofNat (nat_lit 17491669568100)), (nat_lit 188, Int.ofNat (nat_lit 15923188782900)), (nat_lit 198, Int.ofNat (nat_lit 16313214960000)), (nat_lit 199, Int.ofNat (nat_lit 29540683226880)), (nat_lit 200, Int.ofNat (nat_lit 27605876760000)), (nat_lit 201, Int.ofNat (nat_lit 28779027592000)), (nat_lit 202, Int.ofNat (nat_lit 29516408712000))]
theorem block005_data_flat077_step : block005_data_flat077 = (CoefficientMerge.fastMerge block005_data_flat057 block005_data_flat076) := by decide +kernel
theorem block005_data_flat077_original : block005_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded)))))) := by
  rw [block005_data_flat077_step, block005_data_flat057_original, block005_data_flat076_original]
def block005_data_flat078 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 24337174377600)), (nat_lit 140, Int.ofNat (nat_lit 25039315123200)), (nat_lit 141, Int.ofNat (nat_lit 29039577235200)), (nat_lit 142, Int.ofNat (nat_lit 21558664512000)), (nat_lit 143, Int.ofNat (nat_lit 18654996729600)), (nat_lit 144, Int.ofNat (nat_lit 13125428870400)), (nat_lit 145, Int.ofNat (nat_lit 13510927180800)), (nat_lit 146, Int.ofNat (nat_lit 10819430496000)), (nat_lit 154, Int.ofNat (nat_lit 13421582466048)), (nat_lit 155, Int.ofNat (nat_lit 23660965873728)), (nat_lit 156, Int.ofNat (nat_lit 22372041369024)), (nat_lit 157, Int.ofNat (nat_lit 23033831975424)), (nat_lit 158, Int.ofNat (nat_lit 23838356994624)), (nat_lit 159, Int.ofNat (nat_lit 25176291029824)), (nat_lit 160, Int.ofNat (nat_lit 26078455353024)), (nat_lit 161, Int.ofNat (nat_lit 26761266690624)), (nat_lit 162, Int.ofNat (nat_lit 30796193398176)), (nat_lit 163, Int.ofNat (nat_lit 23976290418336)), (nat_lit 164, Int.ofNat (nat_lit 22287869204832)), (nat_lit 165, Int.ofNat (nat_lit 16973062270560)), (nat_lit 166, Int.ofNat (nat_lit 16137647557920)), (nat_lit 167, Int.ofNat (nat_lit 14405932338336)), (nat_lit 176, Int.ofNat (nat_lit 14770003348800)), (nat_lit 177, Int.ofNat (nat_lit 26552598367680)), (nat_lit 178, Int.ofNat (nat_lit 25135035962400)), (nat_lit 179, Int.ofNat (nat_lit 25813436594400)), (nat_lit 180, Int.ofNat (nat_lit 26983204780000)), (nat_lit 181, Int.ofNat (nat_lit 27823998232800)), (nat_lit 182, Int.ofNat (nat_lit 28445438700000)), (nat_lit 183, Int.ofNat (nat_lit 32314904294400)), (nat_lit 184, Int.ofNat (nat_lit 25706174665500)), (nat_lit 185, Int.ofNat (nat_lit 24255404812800)), (nat_lit 186, Int.ofNat (nat_lit 18917112734100)), (nat_lit 187, Int.ofNat (nat_lit 17491669568100)), (nat_lit 188, Int.ofNat (nat_lit 15923188782900)), (nat_lit 198, Int.ofNat (nat_lit 16313214960000)), (nat_lit 199, Int.ofNat (nat_lit 29540683226880)), (nat_lit 200, Int.ofNat (nat_lit 27605876760000)), (nat_lit 201, Int.ofNat (nat_lit 28779027592000)), (nat_lit 202, Int.ofNat (nat_lit 29516408712000))]
theorem block005_data_flat078_step : block005_data_flat078 = (CoefficientMerge.fastMerge block005_data_flat038 block005_data_flat077) := by decide +kernel
theorem block005_data_flat078_original : block005_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded))))))) := by
  rw [block005_data_flat078_step, block005_data_flat038_original, block005_data_flat077_original]
def block005_data_flat079 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 30034436846400))]
theorem block005_data_flat079_step : block005_data_flat079 = (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) := by decide +kernel
theorem block005_data_flat079_original : block005_data_flat079 = (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) := by
  rw [block005_data_flat079_step]
def block005_data_flat080 : CoefficientMerge.Poly := [(nat_lit 204, Int.ofNat (nat_lit 33814866355200))]
theorem block005_data_flat080_step : block005_data_flat080 = (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded) := by decide +kernel
theorem block005_data_flat080_original : block005_data_flat080 = (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded) := by
  rw [block005_data_flat080_step]
def block005_data_flat081 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 30034436846400)), (nat_lit 204, Int.ofNat (nat_lit 33814866355200))]
theorem block005_data_flat081_step : block005_data_flat081 = (CoefficientMerge.fastMerge block005_data_flat079 block005_data_flat080) := by decide +kernel
theorem block005_data_flat081_original : block005_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded)) := by
  rw [block005_data_flat081_step, block005_data_flat079_original, block005_data_flat080_original]
def block005_data_flat082 : CoefficientMerge.Poly := [(nat_lit 205, Int.ofNat (nat_lit 27205547783400))]
theorem block005_data_flat082_step : block005_data_flat082 = (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) := by decide +kernel
theorem block005_data_flat082_original : block005_data_flat082 = (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) := by
  rw [block005_data_flat082_step]
def block005_data_flat083 : CoefficientMerge.Poly := [(nat_lit 206, Int.ofNat (nat_lit 26091698572800))]
theorem block005_data_flat083_step : block005_data_flat083 = (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) := by decide +kernel
theorem block005_data_flat083_original : block005_data_flat083 = (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) := by
  rw [block005_data_flat083_step]
def block005_data_flat084 : CoefficientMerge.Poly := [(nat_lit 207, Int.ofNat (nat_lit 20444060460600))]
theorem block005_data_flat084_step : block005_data_flat084 = (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded) := by decide +kernel
theorem block005_data_flat084_original : block005_data_flat084 = (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded) := by
  rw [block005_data_flat084_step]
def block005_data_flat085 : CoefficientMerge.Poly := [(nat_lit 206, Int.ofNat (nat_lit 26091698572800)), (nat_lit 207, Int.ofNat (nat_lit 20444060460600))]
theorem block005_data_flat085_step : block005_data_flat085 = (CoefficientMerge.fastMerge block005_data_flat083 block005_data_flat084) := by decide +kernel
theorem block005_data_flat085_original : block005_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded)) := by
  rw [block005_data_flat085_step, block005_data_flat083_original, block005_data_flat084_original]
def block005_data_flat086 : CoefficientMerge.Poly := [(nat_lit 205, Int.ofNat (nat_lit 27205547783400)), (nat_lit 206, Int.ofNat (nat_lit 26091698572800)), (nat_lit 207, Int.ofNat (nat_lit 20444060460600))]
theorem block005_data_flat086_step : block005_data_flat086 = (CoefficientMerge.fastMerge block005_data_flat082 block005_data_flat085) := by decide +kernel
theorem block005_data_flat086_original : block005_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded))) := by
  rw [block005_data_flat086_step, block005_data_flat082_original, block005_data_flat085_original]
def block005_data_flat087 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 30034436846400)), (nat_lit 204, Int.ofNat (nat_lit 33814866355200)), (nat_lit 205, Int.ofNat (nat_lit 27205547783400)), (nat_lit 206, Int.ofNat (nat_lit 26091698572800)), (nat_lit 207, Int.ofNat (nat_lit 20444060460600))]
theorem block005_data_flat087_step : block005_data_flat087 = (CoefficientMerge.fastMerge block005_data_flat081 block005_data_flat086) := by decide +kernel
theorem block005_data_flat087_original : block005_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded)))) := by
  rw [block005_data_flat087_step, block005_data_flat081_original, block005_data_flat086_original]
def block005_data_flat088 : CoefficientMerge.Poly := [(nat_lit 208, Int.ofNat (nat_lit 18430701269400))]
theorem block005_data_flat088_step : block005_data_flat088 = (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) := by decide +kernel
theorem block005_data_flat088_original : block005_data_flat088 = (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) := by
  rw [block005_data_flat088_step]
def block005_data_flat089 : CoefficientMerge.Poly := [(nat_lit 209, Int.ofNat (nat_lit 16915074334200))]
theorem block005_data_flat089_step : block005_data_flat089 = (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded) := by decide +kernel
theorem block005_data_flat089_original : block005_data_flat089 = (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded) := by
  rw [block005_data_flat089_step]
def block005_data_flat090 : CoefficientMerge.Poly := [(nat_lit 208, Int.ofNat (nat_lit 18430701269400)), (nat_lit 209, Int.ofNat (nat_lit 16915074334200))]
theorem block005_data_flat090_step : block005_data_flat090 = (CoefficientMerge.fastMerge block005_data_flat088 block005_data_flat089) := by decide +kernel
theorem block005_data_flat090_original : block005_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded)) := by
  rw [block005_data_flat090_step, block005_data_flat088_original, block005_data_flat089_original]
def block005_data_flat091 : CoefficientMerge.Poly := [(nat_lit 220, Int.ofNat (nat_lit 17758088208000))]
theorem block005_data_flat091_step : block005_data_flat091 = (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) := by decide +kernel
theorem block005_data_flat091_original : block005_data_flat091 = (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) := by
  rw [block005_data_flat091_step]
def block005_data_flat092 : CoefficientMerge.Poly := [(nat_lit 221, Int.ofNat (nat_lit 32512456529280))]
theorem block005_data_flat092_step : block005_data_flat092 = (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) := by decide +kernel
theorem block005_data_flat092_original : block005_data_flat092 = (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) := by
  rw [block005_data_flat092_step]
def block005_data_flat093 : CoefficientMerge.Poly := [(nat_lit 222, Int.ofNat (nat_lit 30716949294080))]
theorem block005_data_flat093_step : block005_data_flat093 = (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded) := by decide +kernel
theorem block005_data_flat093_original : block005_data_flat093 = (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded) := by
  rw [block005_data_flat093_step]
def block005_data_flat094 : CoefficientMerge.Poly := [(nat_lit 221, Int.ofNat (nat_lit 32512456529280)), (nat_lit 222, Int.ofNat (nat_lit 30716949294080))]
theorem block005_data_flat094_step : block005_data_flat094 = (CoefficientMerge.fastMerge block005_data_flat092 block005_data_flat093) := by decide +kernel
theorem block005_data_flat094_original : block005_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded)) := by
  rw [block005_data_flat094_step, block005_data_flat092_original, block005_data_flat093_original]
def block005_data_flat095 : CoefficientMerge.Poly := [(nat_lit 220, Int.ofNat (nat_lit 17758088208000)), (nat_lit 221, Int.ofNat (nat_lit 32512456529280)), (nat_lit 222, Int.ofNat (nat_lit 30716949294080))]
theorem block005_data_flat095_step : block005_data_flat095 = (CoefficientMerge.fastMerge block005_data_flat091 block005_data_flat094) := by decide +kernel
theorem block005_data_flat095_original : block005_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded))) := by
  rw [block005_data_flat095_step, block005_data_flat091_original, block005_data_flat094_original]
def block005_data_flat096 : CoefficientMerge.Poly := [(nat_lit 208, Int.ofNat (nat_lit 18430701269400)), (nat_lit 209, Int.ofNat (nat_lit 16915074334200)), (nat_lit 220, Int.ofNat (nat_lit 17758088208000)), (nat_lit 221, Int.ofNat (nat_lit 32512456529280)), (nat_lit 222, Int.ofNat (nat_lit 30716949294080))]
theorem block005_data_flat096_step : block005_data_flat096 = (CoefficientMerge.fastMerge block005_data_flat090 block005_data_flat095) := by decide +kernel
theorem block005_data_flat096_original : block005_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded)))) := by
  rw [block005_data_flat096_step, block005_data_flat090_original, block005_data_flat095_original]
def block005_data_flat097 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 30034436846400)), (nat_lit 204, Int.ofNat (nat_lit 33814866355200)), (nat_lit 205, Int.ofNat (nat_lit 27205547783400)), (nat_lit 206, Int.ofNat (nat_lit 26091698572800)), (nat_lit 207, Int.ofNat (nat_lit 20444060460600)), (nat_lit 208, Int.ofNat (nat_lit 18430701269400)), (nat_lit 209, Int.ofNat (nat_lit 16915074334200)), (nat_lit 220, Int.ofNat (nat_lit 17758088208000)), (nat_lit 221, Int.ofNat (nat_lit 32512456529280)), (nat_lit 222, Int.ofNat (nat_lit 30716949294080))]
theorem block005_data_flat097_step : block005_data_flat097 = (CoefficientMerge.fastMerge block005_data_flat087 block005_data_flat096) := by decide +kernel
theorem block005_data_flat097_original : block005_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded))))) := by
  rw [block005_data_flat097_step, block005_data_flat087_original, block005_data_flat096_original]
def block005_data_flat098 : CoefficientMerge.Poly := [(nat_lit 223, Int.ofNat (nat_lit 31264753665600))]
theorem block005_data_flat098_step : block005_data_flat098 = (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) := by decide +kernel
theorem block005_data_flat098_original : block005_data_flat098 = (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) := by
  rw [block005_data_flat098_step]
def block005_data_flat099 : CoefficientMerge.Poly := [(nat_lit 224, Int.ofNat (nat_lit 31637328004800))]
theorem block005_data_flat099_step : block005_data_flat099 = (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded) := by decide +kernel
theorem block005_data_flat099_original : block005_data_flat099 = (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded) := by
  rw [block005_data_flat099_step]
def block005_data_flat100 : CoefficientMerge.Poly := [(nat_lit 223, Int.ofNat (nat_lit 31264753665600)), (nat_lit 224, Int.ofNat (nat_lit 31637328004800))]
theorem block005_data_flat100_step : block005_data_flat100 = (CoefficientMerge.fastMerge block005_data_flat098 block005_data_flat099) := by decide +kernel
theorem block005_data_flat100_original : block005_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded)) := by
  rw [block005_data_flat100_step, block005_data_flat098_original, block005_data_flat099_original]
def block005_data_flat101 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 35314828416000))]
theorem block005_data_flat101_step : block005_data_flat101 = (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) := by decide +kernel
theorem block005_data_flat101_original : block005_data_flat101 = (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) := by
  rw [block005_data_flat101_step]
def block005_data_flat102 : CoefficientMerge.Poly := [(nat_lit 226, Int.ofNat (nat_lit 28584761448600))]
theorem block005_data_flat102_step : block005_data_flat102 = (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) := by decide +kernel
theorem block005_data_flat102_original : block005_data_flat102 = (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) := by
  rw [block005_data_flat102_step]
def block005_data_flat103 : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 27927992332800))]
theorem block005_data_flat103_step : block005_data_flat103 = (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded) := by decide +kernel
theorem block005_data_flat103_original : block005_data_flat103 = (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded) := by
  rw [block005_data_flat103_step]
def block005_data_flat104 : CoefficientMerge.Poly := [(nat_lit 226, Int.ofNat (nat_lit 28584761448600)), (nat_lit 227, Int.ofNat (nat_lit 27927992332800))]
theorem block005_data_flat104_step : block005_data_flat104 = (CoefficientMerge.fastMerge block005_data_flat102 block005_data_flat103) := by decide +kernel
theorem block005_data_flat104_original : block005_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded)) := by
  rw [block005_data_flat104_step, block005_data_flat102_original, block005_data_flat103_original]
def block005_data_flat105 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 35314828416000)), (nat_lit 226, Int.ofNat (nat_lit 28584761448600)), (nat_lit 227, Int.ofNat (nat_lit 27927992332800))]
theorem block005_data_flat105_step : block005_data_flat105 = (CoefficientMerge.fastMerge block005_data_flat101 block005_data_flat104) := by decide +kernel
theorem block005_data_flat105_original : block005_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded))) := by
  rw [block005_data_flat105_step, block005_data_flat101_original, block005_data_flat104_original]
def block005_data_flat106 : CoefficientMerge.Poly := [(nat_lit 223, Int.ofNat (nat_lit 31264753665600)), (nat_lit 224, Int.ofNat (nat_lit 31637328004800)), (nat_lit 225, Int.ofNat (nat_lit 35314828416000)), (nat_lit 226, Int.ofNat (nat_lit 28584761448600)), (nat_lit 227, Int.ofNat (nat_lit 27927992332800))]
theorem block005_data_flat106_step : block005_data_flat106 = (CoefficientMerge.fastMerge block005_data_flat100 block005_data_flat105) := by decide +kernel
theorem block005_data_flat106_original : block005_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded)))) := by
  rw [block005_data_flat106_step, block005_data_flat100_original, block005_data_flat105_original]
def block005_data_flat107 : CoefficientMerge.Poly := [(nat_lit 228, Int.ofNat (nat_lit 21666826729800))]
theorem block005_data_flat107_step : block005_data_flat107 = (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) := by decide +kernel
theorem block005_data_flat107_original : block005_data_flat107 = (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) := by
  rw [block005_data_flat107_step]
def block005_data_flat108 : CoefficientMerge.Poly := [(nat_lit 229, Int.ofNat (nat_lit 18956883997800))]
theorem block005_data_flat108_step : block005_data_flat108 = (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded) := by decide +kernel
theorem block005_data_flat108_original : block005_data_flat108 = (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded) := by
  rw [block005_data_flat108_step]
def block005_data_flat109 : CoefficientMerge.Poly := [(nat_lit 228, Int.ofNat (nat_lit 21666826729800)), (nat_lit 229, Int.ofNat (nat_lit 18956883997800))]
theorem block005_data_flat109_step : block005_data_flat109 = (CoefficientMerge.fastMerge block005_data_flat107 block005_data_flat108) := by decide +kernel
theorem block005_data_flat109_original : block005_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded)) := by
  rw [block005_data_flat109_step, block005_data_flat107_original, block005_data_flat108_original]
def block005_data_flat110 : CoefficientMerge.Poly := [(nat_lit 230, Int.ofNat (nat_lit 17385443397000))]
theorem block005_data_flat110_step : block005_data_flat110 = (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) := by decide +kernel
theorem block005_data_flat110_original : block005_data_flat110 = (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) := by
  rw [block005_data_flat110_step]
def block005_data_flat111 : CoefficientMerge.Poly := [(nat_lit 242, Int.ofNat (nat_lit 19284988262400))]
theorem block005_data_flat111_step : block005_data_flat111 = (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) := by decide +kernel
theorem block005_data_flat111_original : block005_data_flat111 = (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) := by
  rw [block005_data_flat111_step]
def block005_data_flat112 : CoefficientMerge.Poly := [(nat_lit 243, Int.ofNat (nat_lit 35899040401280))]
theorem block005_data_flat112_step : block005_data_flat112 = (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded) := by decide +kernel
theorem block005_data_flat112_original : block005_data_flat112 = (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded) := by
  rw [block005_data_flat112_step]
def block005_data_flat113 : CoefficientMerge.Poly := [(nat_lit 242, Int.ofNat (nat_lit 19284988262400)), (nat_lit 243, Int.ofNat (nat_lit 35899040401280))]
theorem block005_data_flat113_step : block005_data_flat113 = (CoefficientMerge.fastMerge block005_data_flat111 block005_data_flat112) := by decide +kernel
theorem block005_data_flat113_original : block005_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded)) := by
  rw [block005_data_flat113_step, block005_data_flat111_original, block005_data_flat112_original]
def block005_data_flat114 : CoefficientMerge.Poly := [(nat_lit 230, Int.ofNat (nat_lit 17385443397000)), (nat_lit 242, Int.ofNat (nat_lit 19284988262400)), (nat_lit 243, Int.ofNat (nat_lit 35899040401280))]
theorem block005_data_flat114_step : block005_data_flat114 = (CoefficientMerge.fastMerge block005_data_flat110 block005_data_flat113) := by decide +kernel
theorem block005_data_flat114_original : block005_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded))) := by
  rw [block005_data_flat114_step, block005_data_flat110_original, block005_data_flat113_original]
def block005_data_flat115 : CoefficientMerge.Poly := [(nat_lit 228, Int.ofNat (nat_lit 21666826729800)), (nat_lit 229, Int.ofNat (nat_lit 18956883997800)), (nat_lit 230, Int.ofNat (nat_lit 17385443397000)), (nat_lit 242, Int.ofNat (nat_lit 19284988262400)), (nat_lit 243, Int.ofNat (nat_lit 35899040401280))]
theorem block005_data_flat115_step : block005_data_flat115 = (CoefficientMerge.fastMerge block005_data_flat109 block005_data_flat114) := by decide +kernel
theorem block005_data_flat115_original : block005_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded)))) := by
  rw [block005_data_flat115_step, block005_data_flat109_original, block005_data_flat114_original]
def block005_data_flat116 : CoefficientMerge.Poly := [(nat_lit 223, Int.ofNat (nat_lit 31264753665600)), (nat_lit 224, Int.ofNat (nat_lit 31637328004800)), (nat_lit 225, Int.ofNat (nat_lit 35314828416000)), (nat_lit 226, Int.ofNat (nat_lit 28584761448600)), (nat_lit 227, Int.ofNat (nat_lit 27927992332800)), (nat_lit 228, Int.ofNat (nat_lit 21666826729800)), (nat_lit 229, Int.ofNat (nat_lit 18956883997800)), (nat_lit 230, Int.ofNat (nat_lit 17385443397000)), (nat_lit 242, Int.ofNat (nat_lit 19284988262400)), (nat_lit 243, Int.ofNat (nat_lit 35899040401280))]
theorem block005_data_flat116_step : block005_data_flat116 = (CoefficientMerge.fastMerge block005_data_flat106 block005_data_flat115) := by decide +kernel
theorem block005_data_flat116_original : block005_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded))))) := by
  rw [block005_data_flat116_step, block005_data_flat106_original, block005_data_flat115_original]
def block005_data_flat117 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 30034436846400)), (nat_lit 204, Int.ofNat (nat_lit 33814866355200)), (nat_lit 205, Int.ofNat (nat_lit 27205547783400)), (nat_lit 206, Int.ofNat (nat_lit 26091698572800)), (nat_lit 207, Int.ofNat (nat_lit 20444060460600)), (nat_lit 208, Int.ofNat (nat_lit 18430701269400)), (nat_lit 209, Int.ofNat (nat_lit 16915074334200)), (nat_lit 220, Int.ofNat (nat_lit 17758088208000)), (nat_lit 221, Int.ofNat (nat_lit 32512456529280)), (nat_lit 222, Int.ofNat (nat_lit 30716949294080)), (nat_lit 223, Int.ofNat (nat_lit 31264753665600)), (nat_lit 224, Int.ofNat (nat_lit 31637328004800)), (nat_lit 225, Int.ofNat (nat_lit 35314828416000)), (nat_lit 226, Int.ofNat (nat_lit 28584761448600)), (nat_lit 227, Int.ofNat (nat_lit 27927992332800)), (nat_lit 228, Int.ofNat (nat_lit 21666826729800)), (nat_lit 229, Int.ofNat (nat_lit 18956883997800)), (nat_lit 230, Int.ofNat (nat_lit 17385443397000)), (nat_lit 242, Int.ofNat (nat_lit 19284988262400)), (nat_lit 243, Int.ofNat (nat_lit 35899040401280))]
theorem block005_data_flat117_step : block005_data_flat117 = (CoefficientMerge.fastMerge block005_data_flat097 block005_data_flat116) := by decide +kernel
theorem block005_data_flat117_original : block005_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded)))))) := by
  rw [block005_data_flat117_step, block005_data_flat097_original, block005_data_flat116_original]
def block005_data_flat118 : CoefficientMerge.Poly := [(nat_lit 244, Int.ofNat (nat_lit 33134812300800))]
theorem block005_data_flat118_step : block005_data_flat118 = (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) := by decide +kernel
theorem block005_data_flat118_original : block005_data_flat118 = (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) := by
  rw [block005_data_flat118_step]
def block005_data_flat119 : CoefficientMerge.Poly := [(nat_lit 245, Int.ofNat (nat_lit 33319891382400))]
theorem block005_data_flat119_step : block005_data_flat119 = (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded) := by decide +kernel
theorem block005_data_flat119_original : block005_data_flat119 = (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded) := by
  rw [block005_data_flat119_step]
def block005_data_flat120 : CoefficientMerge.Poly := [(nat_lit 244, Int.ofNat (nat_lit 33134812300800)), (nat_lit 245, Int.ofNat (nat_lit 33319891382400))]
theorem block005_data_flat120_step : block005_data_flat120 = (CoefficientMerge.fastMerge block005_data_flat118 block005_data_flat119) := by decide +kernel
theorem block005_data_flat120_original : block005_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded)) := by
  rw [block005_data_flat120_step, block005_data_flat118_original, block005_data_flat119_original]
def block005_data_flat121 : CoefficientMerge.Poly := [(nat_lit 246, Int.ofNat (nat_lit 36736809580800))]
theorem block005_data_flat121_step : block005_data_flat121 = (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) := by decide +kernel
theorem block005_data_flat121_original : block005_data_flat121 = (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) := by
  rw [block005_data_flat121_step]
def block005_data_flat122 : CoefficientMerge.Poly := [(nat_lit 247, Int.ofNat (nat_lit 29709470649600))]
theorem block005_data_flat122_step : block005_data_flat122 = (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) := by decide +kernel
theorem block005_data_flat122_original : block005_data_flat122 = (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) := by
  rw [block005_data_flat122_step]
def block005_data_flat123 : CoefficientMerge.Poly := [(nat_lit 248, Int.ofNat (nat_lit 29218419820800))]
theorem block005_data_flat123_step : block005_data_flat123 = (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded) := by decide +kernel
theorem block005_data_flat123_original : block005_data_flat123 = (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded) := by
  rw [block005_data_flat123_step]
def block005_data_flat124 : CoefficientMerge.Poly := [(nat_lit 247, Int.ofNat (nat_lit 29709470649600)), (nat_lit 248, Int.ofNat (nat_lit 29218419820800))]
theorem block005_data_flat124_step : block005_data_flat124 = (CoefficientMerge.fastMerge block005_data_flat122 block005_data_flat123) := by decide +kernel
theorem block005_data_flat124_original : block005_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded)) := by
  rw [block005_data_flat124_step, block005_data_flat122_original, block005_data_flat123_original]
def block005_data_flat125 : CoefficientMerge.Poly := [(nat_lit 246, Int.ofNat (nat_lit 36736809580800)), (nat_lit 247, Int.ofNat (nat_lit 29709470649600)), (nat_lit 248, Int.ofNat (nat_lit 29218419820800))]
theorem block005_data_flat125_step : block005_data_flat125 = (CoefficientMerge.fastMerge block005_data_flat121 block005_data_flat124) := by decide +kernel
theorem block005_data_flat125_original : block005_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded))) := by
  rw [block005_data_flat125_step, block005_data_flat121_original, block005_data_flat124_original]
def block005_data_flat126 : CoefficientMerge.Poly := [(nat_lit 244, Int.ofNat (nat_lit 33134812300800)), (nat_lit 245, Int.ofNat (nat_lit 33319891382400)), (nat_lit 246, Int.ofNat (nat_lit 36736809580800)), (nat_lit 247, Int.ofNat (nat_lit 29709470649600)), (nat_lit 248, Int.ofNat (nat_lit 29218419820800))]
theorem block005_data_flat126_step : block005_data_flat126 = (CoefficientMerge.fastMerge block005_data_flat120 block005_data_flat125) := by decide +kernel
theorem block005_data_flat126_original : block005_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded)))) := by
  rw [block005_data_flat126_step, block005_data_flat120_original, block005_data_flat125_original]
def block005_data_flat127 : CoefficientMerge.Poly := [(nat_lit 249, Int.ofNat (nat_lit 22050818092800))]
theorem block005_data_flat127_step : block005_data_flat127 = (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) := by decide +kernel
theorem block005_data_flat127_original : block005_data_flat127 = (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) := by
  rw [block005_data_flat127_step]
def block005_data_flat128 : CoefficientMerge.Poly := [(nat_lit 250, Int.ofNat (nat_lit 18736677388800))]
theorem block005_data_flat128_step : block005_data_flat128 = (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded) := by decide +kernel
theorem block005_data_flat128_original : block005_data_flat128 = (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded) := by
  rw [block005_data_flat128_step]
def block005_data_flat129 : CoefficientMerge.Poly := [(nat_lit 249, Int.ofNat (nat_lit 22050818092800)), (nat_lit 250, Int.ofNat (nat_lit 18736677388800))]
theorem block005_data_flat129_step : block005_data_flat129 = (CoefficientMerge.fastMerge block005_data_flat127 block005_data_flat128) := by decide +kernel
theorem block005_data_flat129_original : block005_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded)) := by
  rw [block005_data_flat129_step, block005_data_flat127_original, block005_data_flat128_original]
def block005_data_flat130 : CoefficientMerge.Poly := [(nat_lit 251, Int.ofNat (nat_lit 16733923315200))]
theorem block005_data_flat130_step : block005_data_flat130 = (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) := by decide +kernel
theorem block005_data_flat130_original : block005_data_flat130 = (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) := by
  rw [block005_data_flat130_step]
def block005_data_flat131 : CoefficientMerge.Poly := [(nat_lit 264, Int.ofNat (nat_lit 21251467059200))]
theorem block005_data_flat131_step : block005_data_flat131 = (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) := by decide +kernel
theorem block005_data_flat131_original : block005_data_flat131 = (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) := by
  rw [block005_data_flat131_step]
def block005_data_flat132 : CoefficientMerge.Poly := [(nat_lit 265, Int.ofNat (nat_lit 39297939296000))]
theorem block005_data_flat132_step : block005_data_flat132 = (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded) := by decide +kernel
theorem block005_data_flat132_original : block005_data_flat132 = (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded) := by
  rw [block005_data_flat132_step]
def block005_data_flat133 : CoefficientMerge.Poly := [(nat_lit 264, Int.ofNat (nat_lit 21251467059200)), (nat_lit 265, Int.ofNat (nat_lit 39297939296000))]
theorem block005_data_flat133_step : block005_data_flat133 = (CoefficientMerge.fastMerge block005_data_flat131 block005_data_flat132) := by decide +kernel
theorem block005_data_flat133_original : block005_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded)) := by
  rw [block005_data_flat133_step, block005_data_flat131_original, block005_data_flat132_original]
def block005_data_flat134 : CoefficientMerge.Poly := [(nat_lit 251, Int.ofNat (nat_lit 16733923315200)), (nat_lit 264, Int.ofNat (nat_lit 21251467059200)), (nat_lit 265, Int.ofNat (nat_lit 39297939296000))]
theorem block005_data_flat134_step : block005_data_flat134 = (CoefficientMerge.fastMerge block005_data_flat130 block005_data_flat133) := by decide +kernel
theorem block005_data_flat134_original : block005_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded))) := by
  rw [block005_data_flat134_step, block005_data_flat130_original, block005_data_flat133_original]
def block005_data_flat135 : CoefficientMerge.Poly := [(nat_lit 249, Int.ofNat (nat_lit 22050818092800)), (nat_lit 250, Int.ofNat (nat_lit 18736677388800)), (nat_lit 251, Int.ofNat (nat_lit 16733923315200)), (nat_lit 264, Int.ofNat (nat_lit 21251467059200)), (nat_lit 265, Int.ofNat (nat_lit 39297939296000))]
theorem block005_data_flat135_step : block005_data_flat135 = (CoefficientMerge.fastMerge block005_data_flat129 block005_data_flat134) := by decide +kernel
theorem block005_data_flat135_original : block005_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded)))) := by
  rw [block005_data_flat135_step, block005_data_flat129_original, block005_data_flat134_original]
def block005_data_flat136 : CoefficientMerge.Poly := [(nat_lit 244, Int.ofNat (nat_lit 33134812300800)), (nat_lit 245, Int.ofNat (nat_lit 33319891382400)), (nat_lit 246, Int.ofNat (nat_lit 36736809580800)), (nat_lit 247, Int.ofNat (nat_lit 29709470649600)), (nat_lit 248, Int.ofNat (nat_lit 29218419820800)), (nat_lit 249, Int.ofNat (nat_lit 22050818092800)), (nat_lit 250, Int.ofNat (nat_lit 18736677388800)), (nat_lit 251, Int.ofNat (nat_lit 16733923315200)), (nat_lit 264, Int.ofNat (nat_lit 21251467059200)), (nat_lit 265, Int.ofNat (nat_lit 39297939296000))]
theorem block005_data_flat136_step : block005_data_flat136 = (CoefficientMerge.fastMerge block005_data_flat126 block005_data_flat135) := by decide +kernel
theorem block005_data_flat136_original : block005_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded))))) := by
  rw [block005_data_flat136_step, block005_data_flat126_original, block005_data_flat135_original]
def block005_data_flat137 : CoefficientMerge.Poly := [(nat_lit 266, Int.ofNat (nat_lit 35912554563200))]
theorem block005_data_flat137_step : block005_data_flat137 = (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) := by decide +kernel
theorem block005_data_flat137_original : block005_data_flat137 = (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) := by
  rw [block005_data_flat137_step]
def block005_data_flat138 : CoefficientMerge.Poly := [(nat_lit 267, Int.ofNat (nat_lit 37646402460800))]
theorem block005_data_flat138_step : block005_data_flat138 = (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded) := by decide +kernel
theorem block005_data_flat138_original : block005_data_flat138 = (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded) := by
  rw [block005_data_flat138_step]
def block005_data_flat139 : CoefficientMerge.Poly := [(nat_lit 266, Int.ofNat (nat_lit 35912554563200)), (nat_lit 267, Int.ofNat (nat_lit 37646402460800))]
theorem block005_data_flat139_step : block005_data_flat139 = (CoefficientMerge.fastMerge block005_data_flat137 block005_data_flat138) := by decide +kernel
theorem block005_data_flat139_original : block005_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded)) := by
  rw [block005_data_flat139_step, block005_data_flat137_original, block005_data_flat138_original]
def block005_data_flat140 : CoefficientMerge.Poly := [(nat_lit 268, Int.ofNat (nat_lit 30033533017600))]
theorem block005_data_flat140_step : block005_data_flat140 = (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) := by decide +kernel
theorem block005_data_flat140_original : block005_data_flat140 = (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) := by
  rw [block005_data_flat140_step]
def block005_data_flat141 : CoefficientMerge.Poly := [(nat_lit 269, Int.ofNat (nat_lit 26922129315200))]
theorem block005_data_flat141_step : block005_data_flat141 = (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) := by decide +kernel
theorem block005_data_flat141_original : block005_data_flat141 = (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) := by
  rw [block005_data_flat141_step]
def block005_data_flat142 : CoefficientMerge.Poly := [(nat_lit 270, Int.ofNat (nat_lit 18741955075200))]
theorem block005_data_flat142_step : block005_data_flat142 = (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded) := by decide +kernel
theorem block005_data_flat142_original : block005_data_flat142 = (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded) := by
  rw [block005_data_flat142_step]
def block005_data_flat143 : CoefficientMerge.Poly := [(nat_lit 269, Int.ofNat (nat_lit 26922129315200)), (nat_lit 270, Int.ofNat (nat_lit 18741955075200))]
theorem block005_data_flat143_step : block005_data_flat143 = (CoefficientMerge.fastMerge block005_data_flat141 block005_data_flat142) := by decide +kernel
theorem block005_data_flat143_original : block005_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded)) := by
  rw [block005_data_flat143_step, block005_data_flat141_original, block005_data_flat142_original]
def block005_data_flat144 : CoefficientMerge.Poly := [(nat_lit 268, Int.ofNat (nat_lit 30033533017600)), (nat_lit 269, Int.ofNat (nat_lit 26922129315200)), (nat_lit 270, Int.ofNat (nat_lit 18741955075200))]
theorem block005_data_flat144_step : block005_data_flat144 = (CoefficientMerge.fastMerge block005_data_flat140 block005_data_flat143) := by decide +kernel
theorem block005_data_flat144_original : block005_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded))) := by
  rw [block005_data_flat144_step, block005_data_flat140_original, block005_data_flat143_original]
def block005_data_flat145 : CoefficientMerge.Poly := [(nat_lit 266, Int.ofNat (nat_lit 35912554563200)), (nat_lit 267, Int.ofNat (nat_lit 37646402460800)), (nat_lit 268, Int.ofNat (nat_lit 30033533017600)), (nat_lit 269, Int.ofNat (nat_lit 26922129315200)), (nat_lit 270, Int.ofNat (nat_lit 18741955075200))]
theorem block005_data_flat145_step : block005_data_flat145 = (CoefficientMerge.fastMerge block005_data_flat139 block005_data_flat144) := by decide +kernel
theorem block005_data_flat145_original : block005_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded)))) := by
  rw [block005_data_flat145_step, block005_data_flat139_original, block005_data_flat144_original]
def block005_data_flat146 : CoefficientMerge.Poly := [(nat_lit 271, Int.ofNat (nat_lit 15709779478400))]
theorem block005_data_flat146_step : block005_data_flat146 = (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) := by decide +kernel
theorem block005_data_flat146_original : block005_data_flat146 = (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) := by
  rw [block005_data_flat146_step]
def block005_data_flat147 : CoefficientMerge.Poly := [(nat_lit 272, Int.ofNat (nat_lit 11251970553600))]
theorem block005_data_flat147_step : block005_data_flat147 = (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded) := by decide +kernel
theorem block005_data_flat147_original : block005_data_flat147 = (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded) := by
  rw [block005_data_flat147_step]
def block005_data_flat148 : CoefficientMerge.Poly := [(nat_lit 271, Int.ofNat (nat_lit 15709779478400)), (nat_lit 272, Int.ofNat (nat_lit 11251970553600))]
theorem block005_data_flat148_step : block005_data_flat148 = (CoefficientMerge.fastMerge block005_data_flat146 block005_data_flat147) := by decide +kernel
theorem block005_data_flat148_original : block005_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded)) := by
  rw [block005_data_flat148_step, block005_data_flat146_original, block005_data_flat147_original]
def block005_data_flat149 : CoefficientMerge.Poly := [(nat_lit 286, Int.ofNat (nat_lit 22298267001600))]
theorem block005_data_flat149_step : block005_data_flat149 = (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) := by decide +kernel
theorem block005_data_flat149_original : block005_data_flat149 = (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) := by
  rw [block005_data_flat149_step]
def block005_data_flat150 : CoefficientMerge.Poly := [(nat_lit 287, Int.ofNat (nat_lit 41193039456000))]
theorem block005_data_flat150_step : block005_data_flat150 = (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) := by decide +kernel
theorem block005_data_flat150_original : block005_data_flat150 = (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) := by
  rw [block005_data_flat150_step]
def block005_data_flat151 : CoefficientMerge.Poly := [(nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
theorem block005_data_flat151_step : block005_data_flat151 = (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded) := by decide +kernel
theorem block005_data_flat151_original : block005_data_flat151 = (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded) := by
  rw [block005_data_flat151_step]
def block005_data_flat152 : CoefficientMerge.Poly := [(nat_lit 287, Int.ofNat (nat_lit 41193039456000)), (nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
theorem block005_data_flat152_step : block005_data_flat152 = (CoefficientMerge.fastMerge block005_data_flat150 block005_data_flat151) := by decide +kernel
theorem block005_data_flat152_original : block005_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded)) := by
  rw [block005_data_flat152_step, block005_data_flat150_original, block005_data_flat151_original]
def block005_data_flat153 : CoefficientMerge.Poly := [(nat_lit 286, Int.ofNat (nat_lit 22298267001600)), (nat_lit 287, Int.ofNat (nat_lit 41193039456000)), (nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
theorem block005_data_flat153_step : block005_data_flat153 = (CoefficientMerge.fastMerge block005_data_flat149 block005_data_flat152) := by decide +kernel
theorem block005_data_flat153_original : block005_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded))) := by
  rw [block005_data_flat153_step, block005_data_flat149_original, block005_data_flat152_original]
def block005_data_flat154 : CoefficientMerge.Poly := [(nat_lit 271, Int.ofNat (nat_lit 15709779478400)), (nat_lit 272, Int.ofNat (nat_lit 11251970553600)), (nat_lit 286, Int.ofNat (nat_lit 22298267001600)), (nat_lit 287, Int.ofNat (nat_lit 41193039456000)), (nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
theorem block005_data_flat154_step : block005_data_flat154 = (CoefficientMerge.fastMerge block005_data_flat148 block005_data_flat153) := by decide +kernel
theorem block005_data_flat154_original : block005_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded)))) := by
  rw [block005_data_flat154_step, block005_data_flat148_original, block005_data_flat153_original]
def block005_data_flat155 : CoefficientMerge.Poly := [(nat_lit 266, Int.ofNat (nat_lit 35912554563200)), (nat_lit 267, Int.ofNat (nat_lit 37646402460800)), (nat_lit 268, Int.ofNat (nat_lit 30033533017600)), (nat_lit 269, Int.ofNat (nat_lit 26922129315200)), (nat_lit 270, Int.ofNat (nat_lit 18741955075200)), (nat_lit 271, Int.ofNat (nat_lit 15709779478400)), (nat_lit 272, Int.ofNat (nat_lit 11251970553600)), (nat_lit 286, Int.ofNat (nat_lit 22298267001600)), (nat_lit 287, Int.ofNat (nat_lit 41193039456000)), (nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
theorem block005_data_flat155_step : block005_data_flat155 = (CoefficientMerge.fastMerge block005_data_flat145 block005_data_flat154) := by decide +kernel
theorem block005_data_flat155_original : block005_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded))))) := by
  rw [block005_data_flat155_step, block005_data_flat145_original, block005_data_flat154_original]
def block005_data_flat156 : CoefficientMerge.Poly := [(nat_lit 244, Int.ofNat (nat_lit 33134812300800)), (nat_lit 245, Int.ofNat (nat_lit 33319891382400)), (nat_lit 246, Int.ofNat (nat_lit 36736809580800)), (nat_lit 247, Int.ofNat (nat_lit 29709470649600)), (nat_lit 248, Int.ofNat (nat_lit 29218419820800)), (nat_lit 249, Int.ofNat (nat_lit 22050818092800)), (nat_lit 250, Int.ofNat (nat_lit 18736677388800)), (nat_lit 251, Int.ofNat (nat_lit 16733923315200)), (nat_lit 264, Int.ofNat (nat_lit 21251467059200)), (nat_lit 265, Int.ofNat (nat_lit 39297939296000)), (nat_lit 266, Int.ofNat (nat_lit 35912554563200)), (nat_lit 267, Int.ofNat (nat_lit 37646402460800)), (nat_lit 268, Int.ofNat (nat_lit 30033533017600)), (nat_lit 269, Int.ofNat (nat_lit 26922129315200)), (nat_lit 270, Int.ofNat (nat_lit 18741955075200)), (nat_lit 271, Int.ofNat (nat_lit 15709779478400)), (nat_lit 272, Int.ofNat (nat_lit 11251970553600)), (nat_lit 286, Int.ofNat (nat_lit 22298267001600)), (nat_lit 287, Int.ofNat (nat_lit 41193039456000)), (nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
theorem block005_data_flat156_step : block005_data_flat156 = (CoefficientMerge.fastMerge block005_data_flat136 block005_data_flat155) := by decide +kernel
theorem block005_data_flat156_original : block005_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded)))))) := by
  rw [block005_data_flat156_step, block005_data_flat136_original, block005_data_flat155_original]
def block005_data_flat157 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 30034436846400)), (nat_lit 204, Int.ofNat (nat_lit 33814866355200)), (nat_lit 205, Int.ofNat (nat_lit 27205547783400)), (nat_lit 206, Int.ofNat (nat_lit 26091698572800)), (nat_lit 207, Int.ofNat (nat_lit 20444060460600)), (nat_lit 208, Int.ofNat (nat_lit 18430701269400)), (nat_lit 209, Int.ofNat (nat_lit 16915074334200)), (nat_lit 220, Int.ofNat (nat_lit 17758088208000)), (nat_lit 221, Int.ofNat (nat_lit 32512456529280)), (nat_lit 222, Int.ofNat (nat_lit 30716949294080)), (nat_lit 223, Int.ofNat (nat_lit 31264753665600)), (nat_lit 224, Int.ofNat (nat_lit 31637328004800)), (nat_lit 225, Int.ofNat (nat_lit 35314828416000)), (nat_lit 226, Int.ofNat (nat_lit 28584761448600)), (nat_lit 227, Int.ofNat (nat_lit 27927992332800)), (nat_lit 228, Int.ofNat (nat_lit 21666826729800)), (nat_lit 229, Int.ofNat (nat_lit 18956883997800)), (nat_lit 230, Int.ofNat (nat_lit 17385443397000)), (nat_lit 242, Int.ofNat (nat_lit 19284988262400)), (nat_lit 243, Int.ofNat (nat_lit 35899040401280)), (nat_lit 244, Int.ofNat (nat_lit 33134812300800)), (nat_lit 245, Int.ofNat (nat_lit 33319891382400)), (nat_lit 246, Int.ofNat (nat_lit 36736809580800)), (nat_lit 247, Int.ofNat (nat_lit 29709470649600)), (nat_lit 248, Int.ofNat (nat_lit 29218419820800)), (nat_lit 249, Int.ofNat (nat_lit 22050818092800)), (nat_lit 250, Int.ofNat (nat_lit 18736677388800)), (nat_lit 251, Int.ofNat (nat_lit 16733923315200)), (nat_lit 264, Int.ofNat (nat_lit 21251467059200)), (nat_lit 265, Int.ofNat (nat_lit 39297939296000)), (nat_lit 266, Int.ofNat (nat_lit 35912554563200)), (nat_lit 267, Int.ofNat (nat_lit 37646402460800)), (nat_lit 268, Int.ofNat (nat_lit 30033533017600)), (nat_lit 269, Int.ofNat (nat_lit 26922129315200)), (nat_lit 270, Int.ofNat (nat_lit 18741955075200)), (nat_lit 271, Int.ofNat (nat_lit 15709779478400)), (nat_lit 272, Int.ofNat (nat_lit 11251970553600)), (nat_lit 286, Int.ofNat (nat_lit 22298267001600)), (nat_lit 287, Int.ofNat (nat_lit 41193039456000)), (nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
theorem block005_data_flat157_step : block005_data_flat157 = (CoefficientMerge.fastMerge block005_data_flat117 block005_data_flat156) := by decide +kernel
theorem block005_data_flat157_original : block005_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded))))))) := by
  rw [block005_data_flat157_step, block005_data_flat117_original, block005_data_flat156_original]
def block005_data_flat158 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 24337174377600)), (nat_lit 140, Int.ofNat (nat_lit 25039315123200)), (nat_lit 141, Int.ofNat (nat_lit 29039577235200)), (nat_lit 142, Int.ofNat (nat_lit 21558664512000)), (nat_lit 143, Int.ofNat (nat_lit 18654996729600)), (nat_lit 144, Int.ofNat (nat_lit 13125428870400)), (nat_lit 145, Int.ofNat (nat_lit 13510927180800)), (nat_lit 146, Int.ofNat (nat_lit 10819430496000)), (nat_lit 154, Int.ofNat (nat_lit 13421582466048)), (nat_lit 155, Int.ofNat (nat_lit 23660965873728)), (nat_lit 156, Int.ofNat (nat_lit 22372041369024)), (nat_lit 157, Int.ofNat (nat_lit 23033831975424)), (nat_lit 158, Int.ofNat (nat_lit 23838356994624)), (nat_lit 159, Int.ofNat (nat_lit 25176291029824)), (nat_lit 160, Int.ofNat (nat_lit 26078455353024)), (nat_lit 161, Int.ofNat (nat_lit 26761266690624)), (nat_lit 162, Int.ofNat (nat_lit 30796193398176)), (nat_lit 163, Int.ofNat (nat_lit 23976290418336)), (nat_lit 164, Int.ofNat (nat_lit 22287869204832)), (nat_lit 165, Int.ofNat (nat_lit 16973062270560)), (nat_lit 166, Int.ofNat (nat_lit 16137647557920)), (nat_lit 167, Int.ofNat (nat_lit 14405932338336)), (nat_lit 176, Int.ofNat (nat_lit 14770003348800)), (nat_lit 177, Int.ofNat (nat_lit 26552598367680)), (nat_lit 178, Int.ofNat (nat_lit 25135035962400)), (nat_lit 179, Int.ofNat (nat_lit 25813436594400)), (nat_lit 180, Int.ofNat (nat_lit 26983204780000)), (nat_lit 181, Int.ofNat (nat_lit 27823998232800)), (nat_lit 182, Int.ofNat (nat_lit 28445438700000)), (nat_lit 183, Int.ofNat (nat_lit 32314904294400)), (nat_lit 184, Int.ofNat (nat_lit 25706174665500)), (nat_lit 185, Int.ofNat (nat_lit 24255404812800)), (nat_lit 186, Int.ofNat (nat_lit 18917112734100)), (nat_lit 187, Int.ofNat (nat_lit 17491669568100)), (nat_lit 188, Int.ofNat (nat_lit 15923188782900)), (nat_lit 198, Int.ofNat (nat_lit 16313214960000)), (nat_lit 199, Int.ofNat (nat_lit 29540683226880)), (nat_lit 200, Int.ofNat (nat_lit 27605876760000)), (nat_lit 201, Int.ofNat (nat_lit 28779027592000)), (nat_lit 202, Int.ofNat (nat_lit 29516408712000)), (nat_lit 203, Int.ofNat (nat_lit 30034436846400)), (nat_lit 204, Int.ofNat (nat_lit 33814866355200)), (nat_lit 205, Int.ofNat (nat_lit 27205547783400)), (nat_lit 206, Int.ofNat (nat_lit 26091698572800)), (nat_lit 207, Int.ofNat (nat_lit 20444060460600)), (nat_lit 208, Int.ofNat (nat_lit 18430701269400)), (nat_lit 209, Int.ofNat (nat_lit 16915074334200)), (nat_lit 220, Int.ofNat (nat_lit 17758088208000)), (nat_lit 221, Int.ofNat (nat_lit 32512456529280)), (nat_lit 222, Int.ofNat (nat_lit 30716949294080)), (nat_lit 223, Int.ofNat (nat_lit 31264753665600)), (nat_lit 224, Int.ofNat (nat_lit 31637328004800)), (nat_lit 225, Int.ofNat (nat_lit 35314828416000)), (nat_lit 226, Int.ofNat (nat_lit 28584761448600)), (nat_lit 227, Int.ofNat (nat_lit 27927992332800)), (nat_lit 228, Int.ofNat (nat_lit 21666826729800)), (nat_lit 229, Int.ofNat (nat_lit 18956883997800)), (nat_lit 230, Int.ofNat (nat_lit 17385443397000)), (nat_lit 242, Int.ofNat (nat_lit 19284988262400)), (nat_lit 243, Int.ofNat (nat_lit 35899040401280)), (nat_lit 244, Int.ofNat (nat_lit 33134812300800)), (nat_lit 245, Int.ofNat (nat_lit 33319891382400)), (nat_lit 246, Int.ofNat (nat_lit 36736809580800)), (nat_lit 247, Int.ofNat (nat_lit 29709470649600)), (nat_lit 248, Int.ofNat (nat_lit 29218419820800)), (nat_lit 249, Int.ofNat (nat_lit 22050818092800)), (nat_lit 250, Int.ofNat (nat_lit 18736677388800)), (nat_lit 251, Int.ofNat (nat_lit 16733923315200)), (nat_lit 264, Int.ofNat (nat_lit 21251467059200)), (nat_lit 265, Int.ofNat (nat_lit 39297939296000)), (nat_lit 266, Int.ofNat (nat_lit 35912554563200)), (nat_lit 267, Int.ofNat (nat_lit 37646402460800)), (nat_lit 268, Int.ofNat (nat_lit 30033533017600)), (nat_lit 269, Int.ofNat (nat_lit 26922129315200)), (nat_lit 270, Int.ofNat (nat_lit 18741955075200)), (nat_lit 271, Int.ofNat (nat_lit 15709779478400)), (nat_lit 272, Int.ofNat (nat_lit 11251970553600)), (nat_lit 286, Int.ofNat (nat_lit 22298267001600)), (nat_lit 287, Int.ofNat (nat_lit 41193039456000)), (nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
theorem block005_data_flat158_step : block005_data_flat158 = (CoefficientMerge.fastMerge block005_data_flat078 block005_data_flat157) := by decide +kernel
theorem block005_data_flat158_original : block005_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded)))))))) := by
  rw [block005_data_flat158_step, block005_data_flat078_original, block005_data_flat157_original]
def block005_data_flat159 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 24337174377600)), (nat_lit 140, Int.ofNat (nat_lit 25039315123200)), (nat_lit 141, Int.ofNat (nat_lit 29039577235200)), (nat_lit 142, Int.ofNat (nat_lit 21558664512000)), (nat_lit 143, Int.ofNat (nat_lit 18654996729600)), (nat_lit 144, Int.ofNat (nat_lit 13125428870400)), (nat_lit 145, Int.ofNat (nat_lit 13510927180800)), (nat_lit 146, Int.ofNat (nat_lit 10819430496000)), (nat_lit 154, Int.ofNat (nat_lit 13421582466048)), (nat_lit 155, Int.ofNat (nat_lit 23660965873728)), (nat_lit 156, Int.ofNat (nat_lit 22372041369024)), (nat_lit 157, Int.ofNat (nat_lit 23033831975424)), (nat_lit 158, Int.ofNat (nat_lit 23838356994624)), (nat_lit 159, Int.ofNat (nat_lit 25176291029824)), (nat_lit 160, Int.ofNat (nat_lit 26078455353024)), (nat_lit 161, Int.ofNat (nat_lit 26761266690624)), (nat_lit 162, Int.ofNat (nat_lit 30796193398176)), (nat_lit 163, Int.ofNat (nat_lit 23976290418336)), (nat_lit 164, Int.ofNat (nat_lit 22287869204832)), (nat_lit 165, Int.ofNat (nat_lit 16973062270560)), (nat_lit 166, Int.ofNat (nat_lit 16137647557920)), (nat_lit 167, Int.ofNat (nat_lit 14405932338336)), (nat_lit 176, Int.ofNat (nat_lit 14770003348800)), (nat_lit 177, Int.ofNat (nat_lit 26552598367680)), (nat_lit 178, Int.ofNat (nat_lit 25135035962400)), (nat_lit 179, Int.ofNat (nat_lit 25813436594400)), (nat_lit 180, Int.ofNat (nat_lit 26983204780000)), (nat_lit 181, Int.ofNat (nat_lit 27823998232800)), (nat_lit 182, Int.ofNat (nat_lit 28445438700000)), (nat_lit 183, Int.ofNat (nat_lit 32314904294400)), (nat_lit 184, Int.ofNat (nat_lit 25706174665500)), (nat_lit 185, Int.ofNat (nat_lit 24255404812800)), (nat_lit 186, Int.ofNat (nat_lit 18917112734100)), (nat_lit 187, Int.ofNat (nat_lit 17491669568100)), (nat_lit 188, Int.ofNat (nat_lit 15923188782900)), (nat_lit 198, Int.ofNat (nat_lit 16313214960000)), (nat_lit 199, Int.ofNat (nat_lit 29540683226880)), (nat_lit 200, Int.ofNat (nat_lit 27605876760000)), (nat_lit 201, Int.ofNat (nat_lit 28779027592000)), (nat_lit 202, Int.ofNat (nat_lit 29516408712000)), (nat_lit 203, Int.ofNat (nat_lit 30034436846400)), (nat_lit 204, Int.ofNat (nat_lit 33814866355200)), (nat_lit 205, Int.ofNat (nat_lit 27205547783400)), (nat_lit 206, Int.ofNat (nat_lit 26091698572800)), (nat_lit 207, Int.ofNat (nat_lit 20444060460600)), (nat_lit 208, Int.ofNat (nat_lit 18430701269400)), (nat_lit 209, Int.ofNat (nat_lit 16915074334200)), (nat_lit 220, Int.ofNat (nat_lit 17758088208000)), (nat_lit 221, Int.ofNat (nat_lit 32512456529280)), (nat_lit 222, Int.ofNat (nat_lit 30716949294080)), (nat_lit 223, Int.ofNat (nat_lit 31264753665600)), (nat_lit 224, Int.ofNat (nat_lit 31637328004800)), (nat_lit 225, Int.ofNat (nat_lit 35314828416000)), (nat_lit 226, Int.ofNat (nat_lit 28584761448600)), (nat_lit 227, Int.ofNat (nat_lit 27927992332800)), (nat_lit 228, Int.ofNat (nat_lit 21666826729800)), (nat_lit 229, Int.ofNat (nat_lit 18956883997800)), (nat_lit 230, Int.ofNat (nat_lit 17385443397000)), (nat_lit 242, Int.ofNat (nat_lit 19284988262400)), (nat_lit 243, Int.ofNat (nat_lit 35899040401280)), (nat_lit 244, Int.ofNat (nat_lit 33134812300800)), (nat_lit 245, Int.ofNat (nat_lit 33319891382400)), (nat_lit 246, Int.ofNat (nat_lit 36736809580800)), (nat_lit 247, Int.ofNat (nat_lit 29709470649600)), (nat_lit 248, Int.ofNat (nat_lit 29218419820800)), (nat_lit 249, Int.ofNat (nat_lit 22050818092800)), (nat_lit 250, Int.ofNat (nat_lit 18736677388800)), (nat_lit 251, Int.ofNat (nat_lit 16733923315200)), (nat_lit 264, Int.ofNat (nat_lit 21251467059200)), (nat_lit 265, Int.ofNat (nat_lit 39297939296000)), (nat_lit 266, Int.ofNat (nat_lit 35912554563200)), (nat_lit 267, Int.ofNat (nat_lit 37646402460800)), (nat_lit 268, Int.ofNat (nat_lit 30033533017600)), (nat_lit 269, Int.ofNat (nat_lit 26922129315200)), (nat_lit 270, Int.ofNat (nat_lit 18741955075200)), (nat_lit 271, Int.ofNat (nat_lit 15709779478400)), (nat_lit 272, Int.ofNat (nat_lit 11251970553600)), (nat_lit 286, Int.ofNat (nat_lit 22298267001600)), (nat_lit 287, Int.ofNat (nat_lit 41193039456000)), (nat_lit 288, Int.ofNat (nat_lit 39191522403600))]
theorem block005_data_flat159_step : block005_data_flat159 = (CoefficientMerge.trim block005_data_flat158) := by decide +kernel
theorem block005_data_flat159_original : block005_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded))))))))) := by
  rw [block005_data_flat159_step, block005_data_flat158_original]
theorem block005_data : block005 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24337174377600 : Int) atom0256Coded) (CoefficientMerge.scale (25039315123200 : Int) atom0257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29039577235200 : Int) atom0258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21558664512000 : Int) atom0259Coded) (CoefficientMerge.scale (18654996729600 : Int) atom0260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13125428870400 : Int) atom0261Coded) (CoefficientMerge.scale (13510927180800 : Int) atom0262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10819430496000 : Int) atom0263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13421582466048 : Int) atom0264Coded) (CoefficientMerge.scale (23660965873728 : Int) atom0265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22372041369024 : Int) atom0266Coded) (CoefficientMerge.scale (23033831975424 : Int) atom0267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23838356994624 : Int) atom0268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25176291029824 : Int) atom0269Coded) (CoefficientMerge.scale (26078455353024 : Int) atom0270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26761266690624 : Int) atom0271Coded) (CoefficientMerge.scale (30796193398176 : Int) atom0272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23976290418336 : Int) atom0273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22287869204832 : Int) atom0274Coded) (CoefficientMerge.scale (16973062270560 : Int) atom0275Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16137647557920 : Int) atom0276Coded) (CoefficientMerge.scale (14405932338336 : Int) atom0277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14770003348800 : Int) atom0278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26552598367680 : Int) atom0279Coded) (CoefficientMerge.scale (25135035962400 : Int) atom0280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25813436594400 : Int) atom0281Coded) (CoefficientMerge.scale (26983204780000 : Int) atom0282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27823998232800 : Int) atom0283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28445438700000 : Int) atom0284Coded) (CoefficientMerge.scale (32314904294400 : Int) atom0285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25706174665500 : Int) atom0286Coded) (CoefficientMerge.scale (24255404812800 : Int) atom0287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18917112734100 : Int) atom0288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17491669568100 : Int) atom0289Coded) (CoefficientMerge.scale (15923188782900 : Int) atom0290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16313214960000 : Int) atom0291Coded) (CoefficientMerge.scale (29540683226880 : Int) atom0292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27605876760000 : Int) atom0293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28779027592000 : Int) atom0294Coded) (CoefficientMerge.scale (29516408712000 : Int) atom0295Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034436846400 : Int) atom0296Coded) (CoefficientMerge.scale (33814866355200 : Int) atom0297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27205547783400 : Int) atom0298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26091698572800 : Int) atom0299Coded) (CoefficientMerge.scale (20444060460600 : Int) atom0300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18430701269400 : Int) atom0301Coded) (CoefficientMerge.scale (16915074334200 : Int) atom0302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17758088208000 : Int) atom0303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32512456529280 : Int) atom0304Coded) (CoefficientMerge.scale (30716949294080 : Int) atom0305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31264753665600 : Int) atom0306Coded) (CoefficientMerge.scale (31637328004800 : Int) atom0307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35314828416000 : Int) atom0308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28584761448600 : Int) atom0309Coded) (CoefficientMerge.scale (27927992332800 : Int) atom0310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21666826729800 : Int) atom0311Coded) (CoefficientMerge.scale (18956883997800 : Int) atom0312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17385443397000 : Int) atom0313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19284988262400 : Int) atom0314Coded) (CoefficientMerge.scale (35899040401280 : Int) atom0315Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33134812300800 : Int) atom0316Coded) (CoefficientMerge.scale (33319891382400 : Int) atom0317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36736809580800 : Int) atom0318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29709470649600 : Int) atom0319Coded) (CoefficientMerge.scale (29218419820800 : Int) atom0320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22050818092800 : Int) atom0321Coded) (CoefficientMerge.scale (18736677388800 : Int) atom0322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16733923315200 : Int) atom0323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21251467059200 : Int) atom0324Coded) (CoefficientMerge.scale (39297939296000 : Int) atom0325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35912554563200 : Int) atom0326Coded) (CoefficientMerge.scale (37646402460800 : Int) atom0327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30033533017600 : Int) atom0328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26922129315200 : Int) atom0329Coded) (CoefficientMerge.scale (18741955075200 : Int) atom0330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15709779478400 : Int) atom0331Coded) (CoefficientMerge.scale (11251970553600 : Int) atom0332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22298267001600 : Int) atom0333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41193039456000 : Int) atom0334Coded) (CoefficientMerge.scale (39191522403600 : Int) atom0335Coded)))))))) := by
  have h : block005 = block005_data_flat159 := by decide +kernel
  exact h.trans block005_data_flat159_original
theorem block005_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block005 := by
  rw [block005_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0256Coded_nonneg g hg hA hB) (atom0257Coded_nonneg g hg hA hB)) (add_nonneg (atom0258Coded_nonneg g hg hA hB) (add_nonneg (atom0259Coded_nonneg g hg hA hB) (atom0260Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0261Coded_nonneg g hg hA hB) (atom0262Coded_nonneg g hg hA hB)) (add_nonneg (atom0263Coded_nonneg g hg hA hB) (add_nonneg (atom0264Coded_nonneg g hg hA hB) (atom0265Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0266Coded_nonneg g hg hA hB) (atom0267Coded_nonneg g hg hA hB)) (add_nonneg (atom0268Coded_nonneg g hg hA hB) (add_nonneg (atom0269Coded_nonneg g hg hA hB) (atom0270Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0271Coded_nonneg g hg hA hB) (atom0272Coded_nonneg g hg hA hB)) (add_nonneg (atom0273Coded_nonneg g hg hA hB) (add_nonneg (atom0274Coded_nonneg g hg hA hB) (atom0275Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0276Coded_nonneg g hg hA hB) (atom0277Coded_nonneg g hg hA hB)) (add_nonneg (atom0278Coded_nonneg g hg hA hB) (add_nonneg (atom0279Coded_nonneg g hg hA hB) (atom0280Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0281Coded_nonneg g hg hA hB) (atom0282Coded_nonneg g hg hA hB)) (add_nonneg (atom0283Coded_nonneg g hg hA hB) (add_nonneg (atom0284Coded_nonneg g hg hA hB) (atom0285Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0286Coded_nonneg g hg hA hB) (atom0287Coded_nonneg g hg hA hB)) (add_nonneg (atom0288Coded_nonneg g hg hA hB) (add_nonneg (atom0289Coded_nonneg g hg hA hB) (atom0290Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0291Coded_nonneg g hg hA hB) (atom0292Coded_nonneg g hg hA hB)) (add_nonneg (atom0293Coded_nonneg g hg hA hB) (add_nonneg (atom0294Coded_nonneg g hg hA hB) (atom0295Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0296Coded_nonneg g hg hA hB) (atom0297Coded_nonneg g hg hA hB)) (add_nonneg (atom0298Coded_nonneg g hg hA hB) (add_nonneg (atom0299Coded_nonneg g hg hA hB) (atom0300Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0301Coded_nonneg g hg hA hB) (atom0302Coded_nonneg g hg hA hB)) (add_nonneg (atom0303Coded_nonneg g hg hA hB) (add_nonneg (atom0304Coded_nonneg g hg hA hB) (atom0305Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0306Coded_nonneg g hg hA hB) (atom0307Coded_nonneg g hg hA hB)) (add_nonneg (atom0308Coded_nonneg g hg hA hB) (add_nonneg (atom0309Coded_nonneg g hg hA hB) (atom0310Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0311Coded_nonneg g hg hA hB) (atom0312Coded_nonneg g hg hA hB)) (add_nonneg (atom0313Coded_nonneg g hg hA hB) (add_nonneg (atom0314Coded_nonneg g hg hA hB) (atom0315Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0316Coded_nonneg g hg hA hB) (atom0317Coded_nonneg g hg hA hB)) (add_nonneg (atom0318Coded_nonneg g hg hA hB) (add_nonneg (atom0319Coded_nonneg g hg hA hB) (atom0320Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0321Coded_nonneg g hg hA hB) (atom0322Coded_nonneg g hg hA hB)) (add_nonneg (atom0323Coded_nonneg g hg hA hB) (add_nonneg (atom0324Coded_nonneg g hg hA hB) (atom0325Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0326Coded_nonneg g hg hA hB) (atom0327Coded_nonneg g hg hA hB)) (add_nonneg (atom0328Coded_nonneg g hg hA hB) (add_nonneg (atom0329Coded_nonneg g hg hA hB) (atom0330Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0331Coded_nonneg g hg hA hB) (atom0332Coded_nonneg g hg hA hB)) (add_nonneg (atom0333Coded_nonneg g hg hA hB) (add_nonneg (atom0334Coded_nonneg g hg hA hB) (atom0335Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
