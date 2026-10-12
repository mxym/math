-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2289 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2289 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2289 = ((g 12) * (g 13) * (g 22)) := by
  norm_num [atom2289, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2289_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (93303439004160 : Int) atom2289) := by
  rw [SparsePolynomial.eval_scale, eval_atom2289]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2289Coded : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 1))]
theorem atom2289Coded_decode : atom2289 = SparsePolynomial.decodeCubic 24 atom2289Coded := by decide +kernel
theorem atom2289Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) := by
  have h := atom2289_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2289Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2290 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2290 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2290 = ((g 12) * (g 13) * (g 23)) := by
  norm_num [atom2290, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2290_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144759386217600 : Int) atom2290) := by
  rw [SparsePolynomial.eval_scale, eval_atom2290]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2290Coded : CoefficientMerge.Poly := [(nat_lit 7247, Int.ofNat (nat_lit 1))]
theorem atom2290Coded_decode : atom2290 = SparsePolynomial.decodeCubic 24 atom2290Coded := by decide +kernel
theorem atom2290Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded) := by
  have h := atom2290_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2290Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2291 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2291 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2291 = ((g 12) * (g 14) * (g 14)) := by
  norm_num [atom2291, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2291_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11813892552000 : Int) atom2291) := by
  rw [SparsePolynomial.eval_scale, eval_atom2291]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2291Coded : CoefficientMerge.Poly := [(nat_lit 7262, Int.ofNat (nat_lit 1))]
theorem atom2291Coded_decode : atom2291 = SparsePolynomial.decodeCubic 24 atom2291Coded := by decide +kernel
theorem atom2291Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) := by
  have h := atom2291_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2291Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2292 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2292 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2292 = ((g 12) * (g 14) * (g 15)) := by
  norm_num [atom2292, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2292_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20555375702400 : Int) atom2292) := by
  rw [SparsePolynomial.eval_scale, eval_atom2292]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2292Coded : CoefficientMerge.Poly := [(nat_lit 7263, Int.ofNat (nat_lit 1))]
theorem atom2292Coded_decode : atom2292 = SparsePolynomial.decodeCubic 24 atom2292Coded := by decide +kernel
theorem atom2292Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) := by
  have h := atom2292_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2292Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2293 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2293 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2293 = ((g 12) * (g 14) * (g 16)) := by
  norm_num [atom2293, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2293_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25700864112000 : Int) atom2293) := by
  rw [SparsePolynomial.eval_scale, eval_atom2293]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2293Coded : CoefficientMerge.Poly := [(nat_lit 7264, Int.ofNat (nat_lit 1))]
theorem atom2293Coded_decode : atom2293 = SparsePolynomial.decodeCubic 24 atom2293Coded := by decide +kernel
theorem atom2293Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded) := by
  have h := atom2293_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2293Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2294 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2294 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2294 = ((g 12) * (g 14) * (g 17)) := by
  norm_num [atom2294, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2294_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30846352521600 : Int) atom2294) := by
  rw [SparsePolynomial.eval_scale, eval_atom2294]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2294Coded : CoefficientMerge.Poly := [(nat_lit 7265, Int.ofNat (nat_lit 1))]
theorem atom2294Coded_decode : atom2294 = SparsePolynomial.decodeCubic 24 atom2294Coded := by decide +kernel
theorem atom2294Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) := by
  have h := atom2294_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2294Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2295 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2295 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2295 = ((g 12) * (g 14) * (g 18)) := by
  norm_num [atom2295, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2295_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63030033376992 : Int) atom2295) := by
  rw [SparsePolynomial.eval_scale, eval_atom2295]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2295Coded : CoefficientMerge.Poly := [(nat_lit 7266, Int.ofNat (nat_lit 1))]
theorem atom2295Coded_decode : atom2295 = SparsePolynomial.decodeCubic 24 atom2295Coded := by decide +kernel
theorem atom2295Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded) := by
  have h := atom2295_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2295Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2296 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2296 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2296 = ((g 12) * (g 14) * (g 20)) := by
  norm_num [atom2296, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2296_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (147325511250720 : Int) atom2296) := by
  rw [SparsePolynomial.eval_scale, eval_atom2296]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2296Coded : CoefficientMerge.Poly := [(nat_lit 7268, Int.ofNat (nat_lit 1))]
theorem atom2296Coded_decode : atom2296 = SparsePolynomial.decodeCubic 24 atom2296Coded := by decide +kernel
theorem atom2296Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) := by
  have h := atom2296_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2296Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2297 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2297 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2297 = ((g 12) * (g 14) * (g 21)) := by
  norm_num [atom2297, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2297_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90760107715200 : Int) atom2297) := by
  rw [SparsePolynomial.eval_scale, eval_atom2297]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2297Coded : CoefficientMerge.Poly := [(nat_lit 7269, Int.ofNat (nat_lit 1))]
theorem atom2297Coded_decode : atom2297 = SparsePolynomial.decodeCubic 24 atom2297Coded := by decide +kernel
theorem atom2297Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) := by
  have h := atom2297_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2297Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2298 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2298 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2298 = ((g 12) * (g 14) * (g 22)) := by
  norm_num [atom2298, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2298_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158618185165440 : Int) atom2298) := by
  rw [SparsePolynomial.eval_scale, eval_atom2298]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2298Coded : CoefficientMerge.Poly := [(nat_lit 7270, Int.ofNat (nat_lit 1))]
theorem atom2298Coded_decode : atom2298 = SparsePolynomial.decodeCubic 24 atom2298Coded := by decide +kernel
theorem atom2298Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded) := by
  have h := atom2298_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2298Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2299 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2299 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2299 = ((g 12) * (g 14) * (g 23)) := by
  norm_num [atom2299, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2299_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254072443640400 : Int) atom2299) := by
  rw [SparsePolynomial.eval_scale, eval_atom2299]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2299Coded : CoefficientMerge.Poly := [(nat_lit 7271, Int.ofNat (nat_lit 1))]
theorem atom2299Coded_decode : atom2299 = SparsePolynomial.decodeCubic 24 atom2299Coded := by decide +kernel
theorem atom2299Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) := by
  have h := atom2299_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2299Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2300 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2300 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2300 = ((g 12) * (g 15) * (g 15)) := by
  norm_num [atom2300, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2300_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28260319348800 : Int) atom2300) := by
  rw [SparsePolynomial.eval_scale, eval_atom2300]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2300Coded : CoefficientMerge.Poly := [(nat_lit 7287, Int.ofNat (nat_lit 1))]
theorem atom2300Coded_decode : atom2300 = SparsePolynomial.decodeCubic 24 atom2300Coded := by decide +kernel
theorem atom2300Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded) := by
  have h := atom2300_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2300Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2301 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2301 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2301 = ((g 12) * (g 15) * (g 16)) := by
  norm_num [atom2301, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2301_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49355227152000 : Int) atom2301) := by
  rw [SparsePolynomial.eval_scale, eval_atom2301]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2301Coded : CoefficientMerge.Poly := [(nat_lit 7288, Int.ofNat (nat_lit 1))]
theorem atom2301Coded_decode : atom2301 = SparsePolynomial.decodeCubic 24 atom2301Coded := by decide +kernel
theorem atom2301Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) := by
  have h := atom2301_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2301Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2302 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2302 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2302 = ((g 12) * (g 15) * (g 17)) := by
  norm_num [atom2302, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2302_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55542570652800 : Int) atom2302) := by
  rw [SparsePolynomial.eval_scale, eval_atom2302]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2302Coded : CoefficientMerge.Poly := [(nat_lit 7289, Int.ofNat (nat_lit 1))]
theorem atom2302Coded_decode : atom2302 = SparsePolynomial.decodeCubic 24 atom2302Coded := by decide +kernel
theorem atom2302Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) := by
  have h := atom2302_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2302Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2303 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2303 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2303 = ((g 12) * (g 15) * (g 18)) := by
  norm_num [atom2303, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2303_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108801504755136 : Int) atom2303) := by
  rw [SparsePolynomial.eval_scale, eval_atom2303]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2303Coded : CoefficientMerge.Poly := [(nat_lit 7290, Int.ofNat (nat_lit 1))]
theorem atom2303Coded_decode : atom2303 = SparsePolynomial.decodeCubic 24 atom2303Coded := by decide +kernel
theorem atom2303Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded) := by
  have h := atom2303_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2303Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2304 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2304 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2304 = ((g 12) * (g 15) * (g 19)) := by
  norm_num [atom2304, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2304_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58637029386240 : Int) atom2304) := by
  rw [SparsePolynomial.eval_scale, eval_atom2304]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2304Coded : CoefficientMerge.Poly := [(nat_lit 7291, Int.ofNat (nat_lit 1))]
theorem atom2304Coded_decode : atom2304 = SparsePolynomial.decodeCubic 24 atom2304Coded := by decide +kernel
theorem atom2304Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) := by
  have h := atom2304_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2304Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2305 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2305 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2305 = ((g 12) * (g 15) * (g 20)) := by
  norm_num [atom2305, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2305_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (259360392663360 : Int) atom2305) := by
  rw [SparsePolynomial.eval_scale, eval_atom2305]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2305Coded : CoefficientMerge.Poly := [(nat_lit 7292, Int.ofNat (nat_lit 1))]
theorem atom2305Coded_decode : atom2305 = SparsePolynomial.decodeCubic 24 atom2305Coded := by decide +kernel
theorem atom2305Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded) := by
  have h := atom2305_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2305Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2306 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2306 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2306 = ((g 12) * (g 15) * (g 21)) := by
  norm_num [atom2306, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2306_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226557274695840 : Int) atom2306) := by
  rw [SparsePolynomial.eval_scale, eval_atom2306]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2306Coded : CoefficientMerge.Poly := [(nat_lit 7293, Int.ofNat (nat_lit 1))]
theorem atom2306Coded_decode : atom2306 = SparsePolynomial.decodeCubic 24 atom2306Coded := by decide +kernel
theorem atom2306Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) := by
  have h := atom2306_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2306Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2307 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2307 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2307 = ((g 12) * (g 15) * (g 22)) := by
  norm_num [atom2307, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2307_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (249624699571584 : Int) atom2307) := by
  rw [SparsePolynomial.eval_scale, eval_atom2307]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2307Coded : CoefficientMerge.Poly := [(nat_lit 7294, Int.ofNat (nat_lit 1))]
theorem atom2307Coded_decode : atom2307 = SparsePolynomial.decodeCubic 24 atom2307Coded := by decide +kernel
theorem atom2307Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) := by
  have h := atom2307_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2307Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2308 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2308 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2308 = ((g 12) * (g 15) * (g 23)) := by
  norm_num [atom2308, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2308_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353960904553200 : Int) atom2308) := by
  rw [SparsePolynomial.eval_scale, eval_atom2308]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2308Coded : CoefficientMerge.Poly := [(nat_lit 7295, Int.ofNat (nat_lit 1))]
theorem atom2308Coded_decode : atom2308 = SparsePolynomial.decodeCubic 24 atom2308Coded := by decide +kernel
theorem atom2308Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded) := by
  have h := atom2308_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2308Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2309 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2309 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2309 = ((g 12) * (g 16) * (g 16)) := by
  norm_num [atom2309, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2309_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43696784577600 : Int) atom2309) := by
  rw [SparsePolynomial.eval_scale, eval_atom2309]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2309Coded : CoefficientMerge.Poly := [(nat_lit 7312, Int.ofNat (nat_lit 1))]
theorem atom2309Coded_decode : atom2309 = SparsePolynomial.decodeCubic 24 atom2309Coded := by decide +kernel
theorem atom2309Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) := by
  have h := atom2309_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2309Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2310 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2310 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2310 = ((g 12) * (g 16) * (g 17)) := by
  norm_num [atom2310, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2310_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90519134428800 : Int) atom2310) := by
  rw [SparsePolynomial.eval_scale, eval_atom2310]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2310Coded : CoefficientMerge.Poly := [(nat_lit 7313, Int.ofNat (nat_lit 1))]
theorem atom2310Coded_decode : atom2310 = SparsePolynomial.decodeCubic 24 atom2310Coded := by decide +kernel
theorem atom2310Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded) := by
  have h := atom2310_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2310Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2311 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2311 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2311 = ((g 12) * (g 16) * (g 18)) := by
  norm_num [atom2311, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2311_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140214692166336 : Int) atom2311) := by
  rw [SparsePolynomial.eval_scale, eval_atom2311]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2311Coded : CoefficientMerge.Poly := [(nat_lit 7314, Int.ofNat (nat_lit 1))]
theorem atom2311Coded_decode : atom2311 = SparsePolynomial.decodeCubic 24 atom2311Coded := by decide +kernel
theorem atom2311Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) := by
  have h := atom2311_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2311Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2312 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2312 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2312 = ((g 12) * (g 16) * (g 19)) := by
  norm_num [atom2312, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2312_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118395827159040 : Int) atom2312) := by
  rw [SparsePolynomial.eval_scale, eval_atom2312]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2312Coded : CoefficientMerge.Poly := [(nat_lit 7315, Int.ofNat (nat_lit 1))]
theorem atom2312Coded_decode : atom2312 = SparsePolynomial.decodeCubic 24 atom2312Coded := by decide +kernel
theorem atom2312Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) := by
  have h := atom2312_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2312Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2313 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2313 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2313 = ((g 12) * (g 16) * (g 20)) := by
  norm_num [atom2313, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2313_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347464800797760 : Int) atom2313) := by
  rw [SparsePolynomial.eval_scale, eval_atom2313]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2313Coded : CoefficientMerge.Poly := [(nat_lit 7316, Int.ofNat (nat_lit 1))]
theorem atom2313Coded_decode : atom2313 = SparsePolynomial.decodeCubic 24 atom2313Coded := by decide +kernel
theorem atom2313Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded) := by
  have h := atom2313_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2313Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2314 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2314 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2314 = ((g 12) * (g 16) * (g 21)) := by
  norm_num [atom2314, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2314_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (335468340836640 : Int) atom2314) := by
  rw [SparsePolynomial.eval_scale, eval_atom2314]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2314Coded : CoefficientMerge.Poly := [(nat_lit 7317, Int.ofNat (nat_lit 1))]
theorem atom2314Coded_decode : atom2314 = SparsePolynomial.decodeCubic 24 atom2314Coded := by decide +kernel
theorem atom2314Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) := by
  have h := atom2314_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2314Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2315 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2315 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2315 = ((g 12) * (g 16) * (g 22)) := by
  norm_num [atom2315, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2315_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (321549426739584 : Int) atom2315) := by
  rw [SparsePolynomial.eval_scale, eval_atom2315]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2315Coded : CoefficientMerge.Poly := [(nat_lit 7318, Int.ofNat (nat_lit 1))]
theorem atom2315Coded_decode : atom2315 = SparsePolynomial.decodeCubic 24 atom2315Coded := by decide +kernel
theorem atom2315Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded) := by
  have h := atom2315_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2315Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2316 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2316 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2316 = ((g 12) * (g 16) * (g 23)) := by
  norm_num [atom2316, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2316_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (519457604526000 : Int) atom2316) := by
  rw [SparsePolynomial.eval_scale, eval_atom2316]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2316Coded : CoefficientMerge.Poly := [(nat_lit 7319, Int.ofNat (nat_lit 1))]
theorem atom2316Coded_decode : atom2316 = SparsePolynomial.decodeCubic 24 atom2316Coded := by decide +kernel
theorem atom2316Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) := by
  have h := atom2316_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2316Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2317 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2317 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2317 = ((g 12) * (g 17) * (g 17)) := by
  norm_num [atom2317, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2317_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64633110696000 : Int) atom2317) := by
  rw [SparsePolynomial.eval_scale, eval_atom2317]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2317Coded : CoefficientMerge.Poly := [(nat_lit 7337, Int.ofNat (nat_lit 1))]
theorem atom2317Coded_decode : atom2317 = SparsePolynomial.decodeCubic 24 atom2317Coded := by decide +kernel
theorem atom2317Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) := by
  have h := atom2317_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2317Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2318 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2318 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2318 = ((g 12) * (g 17) * (g 18)) := by
  norm_num [atom2318, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2318_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (186526987263936 : Int) atom2318) := by
  rw [SparsePolynomial.eval_scale, eval_atom2318]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2318Coded : CoefficientMerge.Poly := [(nat_lit 7338, Int.ofNat (nat_lit 1))]
theorem atom2318Coded_decode : atom2318 = SparsePolynomial.decodeCubic 24 atom2318Coded := by decide +kernel
theorem atom2318Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded) := by
  have h := atom2318_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2318Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2319 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2319 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2319 = ((g 12) * (g 17) * (g 19)) := by
  norm_num [atom2319, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2319_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198020101847040 : Int) atom2319) := by
  rw [SparsePolynomial.eval_scale, eval_atom2319]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2319Coded : CoefficientMerge.Poly := [(nat_lit 7339, Int.ofNat (nat_lit 1))]
theorem atom2319Coded_decode : atom2319 = SparsePolynomial.decodeCubic 24 atom2319Coded := by decide +kernel
theorem atom2319Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) := by
  have h := atom2319_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2319Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2320 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2320 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2320 = ((g 12) * (g 17) * (g 20)) := by
  norm_num [atom2320, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2320_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (460401055076160 : Int) atom2320) := by
  rw [SparsePolynomial.eval_scale, eval_atom2320]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2320Coded : CoefficientMerge.Poly := [(nat_lit 7340, Int.ofNat (nat_lit 1))]
theorem atom2320Coded_decode : atom2320 = SparsePolynomial.decodeCubic 24 atom2320Coded := by decide +kernel
theorem atom2320Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded) := by
  have h := atom2320_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2320Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2321 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2321 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2321 = ((g 12) * (g 17) * (g 21)) := by
  norm_num [atom2321, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2321_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (471694437735840 : Int) atom2321) := by
  rw [SparsePolynomial.eval_scale, eval_atom2321]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2321Coded : CoefficientMerge.Poly := [(nat_lit 7341, Int.ofNat (nat_lit 1))]
theorem atom2321Coded_decode : atom2321 = SparsePolynomial.decodeCubic 24 atom2321Coded := by decide +kernel
theorem atom2321Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) := by
  have h := atom2321_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2321Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2322 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2322 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2322 = ((g 12) * (g 17) * (g 22)) := by
  norm_num [atom2322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2322_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (479941683341184 : Int) atom2322) := by
  rw [SparsePolynomial.eval_scale, eval_atom2322]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2322Coded : CoefficientMerge.Poly := [(nat_lit 7342, Int.ofNat (nat_lit 1))]
theorem atom2322Coded_decode : atom2322 = SparsePolynomial.decodeCubic 24 atom2322Coded := by decide +kernel
theorem atom2322Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) := by
  have h := atom2322_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2322Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2323 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2323 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2323 = ((g 12) * (g 17) * (g 23)) := by
  norm_num [atom2323, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2323_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (696128635263600 : Int) atom2323) := by
  rw [SparsePolynomial.eval_scale, eval_atom2323]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2323Coded : CoefficientMerge.Poly := [(nat_lit 7343, Int.ofNat (nat_lit 1))]
theorem atom2323Coded_decode : atom2323 = SparsePolynomial.decodeCubic 24 atom2323Coded := by decide +kernel
theorem atom2323Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded) := by
  have h := atom2323_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2323Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2324 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2324 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2324 = ((g 12) * (g 18) * (g 18)) := by
  norm_num [atom2324, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2324_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151845018393024 : Int) atom2324) := by
  rw [SparsePolynomial.eval_scale, eval_atom2324]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2324Coded : CoefficientMerge.Poly := [(nat_lit 7362, Int.ofNat (nat_lit 1))]
theorem atom2324Coded_decode : atom2324 = SparsePolynomial.decodeCubic 24 atom2324Coded := by decide +kernel
theorem atom2324Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) := by
  have h := atom2324_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2324Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2325 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2325 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2325 = ((g 12) * (g 18) * (g 19)) := by
  norm_num [atom2325, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2325_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (329206824644544 : Int) atom2325) := by
  rw [SparsePolynomial.eval_scale, eval_atom2325]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2325Coded : CoefficientMerge.Poly := [(nat_lit 7363, Int.ofNat (nat_lit 1))]
theorem atom2325Coded_decode : atom2325 = SparsePolynomial.decodeCubic 24 atom2325Coded := by decide +kernel
theorem atom2325Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded) := by
  have h := atom2325_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2325Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2326 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2326 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2326 = ((g 12) * (g 18) * (g 20)) := by
  norm_num [atom2326, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2326_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (621009330277248 : Int) atom2326) := by
  rw [SparsePolynomial.eval_scale, eval_atom2326]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2326Coded : CoefficientMerge.Poly := [(nat_lit 7364, Int.ofNat (nat_lit 1))]
theorem atom2326Coded_decode : atom2326 = SparsePolynomial.decodeCubic 24 atom2326Coded := by decide +kernel
theorem atom2326Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) := by
  have h := atom2326_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2326Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2327 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2327 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2327 = ((g 12) * (g 18) * (g 21)) := by
  norm_num [atom2327, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2327_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (644312525376960 : Int) atom2327) := by
  rw [SparsePolynomial.eval_scale, eval_atom2327]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2327Coded : CoefficientMerge.Poly := [(nat_lit 7365, Int.ofNat (nat_lit 1))]
theorem atom2327Coded_decode : atom2327 = SparsePolynomial.decodeCubic 24 atom2327Coded := by decide +kernel
theorem atom2327Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) := by
  have h := atom2327_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2327Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2328 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2328 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2328 = ((g 12) * (g 18) * (g 22)) := by
  norm_num [atom2328, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2328_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (505633160724480 : Int) atom2328) := by
  rw [SparsePolynomial.eval_scale, eval_atom2328]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2328Coded : CoefficientMerge.Poly := [(nat_lit 7366, Int.ofNat (nat_lit 1))]
theorem atom2328Coded_decode : atom2328 = SparsePolynomial.decodeCubic 24 atom2328Coded := by decide +kernel
theorem atom2328Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded) := by
  have h := atom2328_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2328Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2329 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2329 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2329 = ((g 12) * (g 18) * (g 23)) := by
  norm_num [atom2329, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2329_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (763431802113024 : Int) atom2329) := by
  rw [SparsePolynomial.eval_scale, eval_atom2329]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2329Coded : CoefficientMerge.Poly := [(nat_lit 7367, Int.ofNat (nat_lit 1))]
theorem atom2329Coded_decode : atom2329 = SparsePolynomial.decodeCubic 24 atom2329Coded := by decide +kernel
theorem atom2329Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) := by
  have h := atom2329_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2329Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2330 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2330 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2330 = ((g 12) * (g 19) * (g 19)) := by
  norm_num [atom2330, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2330_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139381029526464 : Int) atom2330) := by
  rw [SparsePolynomial.eval_scale, eval_atom2330]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2330Coded : CoefficientMerge.Poly := [(nat_lit 7387, Int.ofNat (nat_lit 1))]
theorem atom2330Coded_decode : atom2330 = SparsePolynomial.decodeCubic 24 atom2330Coded := by decide +kernel
theorem atom2330Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded) := by
  have h := atom2330_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2330Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2331 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2331 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2331 = ((g 12) * (g 19) * (g 20)) := by
  norm_num [atom2331, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2331_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (564236889682752 : Int) atom2331) := by
  rw [SparsePolynomial.eval_scale, eval_atom2331]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2331Coded : CoefficientMerge.Poly := [(nat_lit 7388, Int.ofNat (nat_lit 1))]
theorem atom2331Coded_decode : atom2331 = SparsePolynomial.decodeCubic 24 atom2331Coded := by decide +kernel
theorem atom2331Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) := by
  have h := atom2331_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2331Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2332 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2332 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2332 = ((g 12) * (g 19) * (g 21)) := by
  norm_num [atom2332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2332_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (661893873071904 : Int) atom2332) := by
  rw [SparsePolynomial.eval_scale, eval_atom2332]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2332Coded : CoefficientMerge.Poly := [(nat_lit 7389, Int.ofNat (nat_lit 1))]
theorem atom2332Coded_decode : atom2332 = SparsePolynomial.decodeCubic 24 atom2332Coded := by decide +kernel
theorem atom2332Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) := by
  have h := atom2332_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2332Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2333 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2333 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2333 = ((g 12) * (g 19) * (g 22)) := by
  norm_num [atom2333, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2333_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (499016944603008 : Int) atom2333) := by
  rw [SparsePolynomial.eval_scale, eval_atom2333]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2333Coded : CoefficientMerge.Poly := [(nat_lit 7390, Int.ofNat (nat_lit 1))]
theorem atom2333Coded_decode : atom2333 = SparsePolynomial.decodeCubic 24 atom2333Coded := by decide +kernel
theorem atom2333Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded) := by
  have h := atom2333_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2333Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2334 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2334 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2334 = ((g 12) * (g 19) * (g 23)) := by
  norm_num [atom2334, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2334_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (653547015318384 : Int) atom2334) := by
  rw [SparsePolynomial.eval_scale, eval_atom2334]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2334Coded : CoefficientMerge.Poly := [(nat_lit 7391, Int.ofNat (nat_lit 1))]
theorem atom2334Coded_decode : atom2334 = SparsePolynomial.decodeCubic 24 atom2334Coded := by decide +kernel
theorem atom2334Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) := by
  have h := atom2334_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2334Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2335 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2335 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2335 = ((g 12) * (g 20) * (g 20)) := by
  norm_num [atom2335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2335_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (402272962559424 : Int) atom2335) := by
  rw [SparsePolynomial.eval_scale, eval_atom2335]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2335Coded : CoefficientMerge.Poly := [(nat_lit 7412, Int.ofNat (nat_lit 1))]
theorem atom2335Coded_decode : atom2335 = SparsePolynomial.decodeCubic 24 atom2335Coded := by decide +kernel
theorem atom2335Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded) := by
  have h := atom2335_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2335Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2336 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2336 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2336 = ((g 12) * (g 20) * (g 21)) := by
  norm_num [atom2336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2336_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (772992938684736 : Int) atom2336) := by
  rw [SparsePolynomial.eval_scale, eval_atom2336]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2336Coded : CoefficientMerge.Poly := [(nat_lit 7413, Int.ofNat (nat_lit 1))]
theorem atom2336Coded_decode : atom2336 = SparsePolynomial.decodeCubic 24 atom2336Coded := by decide +kernel
theorem atom2336Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) := by
  have h := atom2336_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2336Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2337 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2337 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2337 = ((g 12) * (g 20) * (g 22)) := by
  norm_num [atom2337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2337_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (523075355781120 : Int) atom2337) := by
  rw [SparsePolynomial.eval_scale, eval_atom2337]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2337Coded : CoefficientMerge.Poly := [(nat_lit 7414, Int.ofNat (nat_lit 1))]
theorem atom2337Coded_decode : atom2337 = SparsePolynomial.decodeCubic 24 atom2337Coded := by decide +kernel
theorem atom2337Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) := by
  have h := atom2337_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2337Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2338 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2338 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2338 = ((g 12) * (g 20) * (g 23)) := by
  norm_num [atom2338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2338_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (448819934618880 : Int) atom2338) := by
  rw [SparsePolynomial.eval_scale, eval_atom2338]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2338Coded : CoefficientMerge.Poly := [(nat_lit 7415, Int.ofNat (nat_lit 1))]
theorem atom2338Coded_decode : atom2338 = SparsePolynomial.decodeCubic 24 atom2338Coded := by decide +kernel
theorem atom2338Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded) := by
  have h := atom2338_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2338Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2339 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2339 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2339 = ((g 12) * (g 21) * (g 21)) := by
  norm_num [atom2339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2339_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (327897775234656 : Int) atom2339) := by
  rw [SparsePolynomial.eval_scale, eval_atom2339]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 12) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2339Coded : CoefficientMerge.Poly := [(nat_lit 7437, Int.ofNat (nat_lit 1))]
theorem atom2339Coded_decode : atom2339 = SparsePolynomial.decodeCubic 24 atom2339Coded := by decide +kernel
theorem atom2339Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) := by
  have h := atom2339_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2339Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2340 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2340 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2340 = ((g 12) * (g 21) * (g 22)) := by
  norm_num [atom2340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2340_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (434805549584256 : Int) atom2340) := by
  rw [SparsePolynomial.eval_scale, eval_atom2340]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2340Coded : CoefficientMerge.Poly := [(nat_lit 7438, Int.ofNat (nat_lit 1))]
theorem atom2340Coded_decode : atom2340 = SparsePolynomial.decodeCubic 24 atom2340Coded := by decide +kernel
theorem atom2340Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded) := by
  have h := atom2340_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2340Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2341 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2341 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2341 = ((g 12) * (g 21) * (g 23)) := by
  norm_num [atom2341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2341_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (385561625880816 : Int) atom2341) := by
  rw [SparsePolynomial.eval_scale, eval_atom2341]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2341Coded : CoefficientMerge.Poly := [(nat_lit 7439, Int.ofNat (nat_lit 1))]
theorem atom2341Coded_decode : atom2341 = SparsePolynomial.decodeCubic 24 atom2341Coded := by decide +kernel
theorem atom2341Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) := by
  have h := atom2341_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2341Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2342 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 22, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2342 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2342 = ((g 12) * (g 22) * (g 22)) := by
  norm_num [atom2342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2342_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68278699175040 : Int) atom2342) := by
  rw [SparsePolynomial.eval_scale, eval_atom2342]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 12) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2342Coded : CoefficientMerge.Poly := [(nat_lit 7462, Int.ofNat (nat_lit 1))]
theorem atom2342Coded_decode : atom2342 = SparsePolynomial.decodeCubic 24 atom2342Coded := by decide +kernel
theorem atom2342Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) := by
  have h := atom2342_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2342Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2343 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2343 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2343 = ((g 12) * (g 22) * (g 23)) := by
  norm_num [atom2343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2343_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100562774904576 : Int) atom2343) := by
  rw [SparsePolynomial.eval_scale, eval_atom2343]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 12) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2343Coded : CoefficientMerge.Poly := [(nat_lit 7463, Int.ofNat (nat_lit 1))]
theorem atom2343Coded_decode : atom2343 = SparsePolynomial.decodeCubic 24 atom2343Coded := by decide +kernel
theorem atom2343Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded) := by
  have h := atom2343_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2343Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2344 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom2344 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2344 = ((g 13) * (g 13) * (g 13)) := by
  norm_num [atom2344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2344_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5136629097600 : Int) atom2344) := by
  rw [SparsePolynomial.eval_scale, eval_atom2344]
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 13) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2344Coded : CoefficientMerge.Poly := [(nat_lit 7813, Int.ofNat (nat_lit 1))]
theorem atom2344Coded_decode : atom2344 = SparsePolynomial.decodeCubic 24 atom2344Coded := by decide +kernel
theorem atom2344Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) := by
  have h := atom2344_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2344Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2345 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2345 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2345 = ((g 13) * (g 13) * (g 14)) := by
  norm_num [atom2345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2345_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2345) := by
  rw [SparsePolynomial.eval_scale, eval_atom2345]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2345Coded : CoefficientMerge.Poly := [(nat_lit 7814, Int.ofNat (nat_lit 1))]
theorem atom2345Coded_decode : atom2345 = SparsePolynomial.decodeCubic 24 atom2345Coded := by decide +kernel
theorem atom2345Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded) := by
  have h := atom2345_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2345Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2346 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2346 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2346 = ((g 13) * (g 13) * (g 18)) := by
  norm_num [atom2346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2346_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34624275840000 : Int) atom2346) := by
  rw [SparsePolynomial.eval_scale, eval_atom2346]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2346Coded : CoefficientMerge.Poly := [(nat_lit 7818, Int.ofNat (nat_lit 1))]
theorem atom2346Coded_decode : atom2346 = SparsePolynomial.decodeCubic 24 atom2346Coded := by decide +kernel
theorem atom2346Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) := by
  have h := atom2346_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2346Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2347 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2347 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2347 = ((g 13) * (g 13) * (g 20)) := by
  norm_num [atom2347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2347_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49043900505600 : Int) atom2347) := by
  rw [SparsePolynomial.eval_scale, eval_atom2347]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2347Coded : CoefficientMerge.Poly := [(nat_lit 7820, Int.ofNat (nat_lit 1))]
theorem atom2347Coded_decode : atom2347 = SparsePolynomial.decodeCubic 24 atom2347Coded := by decide +kernel
theorem atom2347Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) := by
  have h := atom2347_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2347Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2348 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom2348 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2348 = ((g 13) * (g 14) * (g 14)) := by
  norm_num [atom2348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2348_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4108948905600 : Int) atom2348) := by
  rw [SparsePolynomial.eval_scale, eval_atom2348]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2348Coded : CoefficientMerge.Poly := [(nat_lit 7838, Int.ofNat (nat_lit 1))]
theorem atom2348Coded_decode : atom2348 = SparsePolynomial.decodeCubic 24 atom2348Coded := by decide +kernel
theorem atom2348Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded) := by
  have h := atom2348_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2348Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2349 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2349 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2349 = ((g 13) * (g 14) * (g 16)) := by
  norm_num [atom2349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2349_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom2349) := by
  rw [SparsePolynomial.eval_scale, eval_atom2349]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2349Coded : CoefficientMerge.Poly := [(nat_lit 7840, Int.ofNat (nat_lit 1))]
theorem atom2349Coded_decode : atom2349 = SparsePolynomial.decodeCubic 24 atom2349Coded := by decide +kernel
theorem atom2349Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) := by
  have h := atom2349_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2349Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2350 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2350 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2350 = ((g 13) * (g 14) * (g 17)) := by
  norm_num [atom2350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2350_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom2350) := by
  rw [SparsePolynomial.eval_scale, eval_atom2350]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2350Coded : CoefficientMerge.Poly := [(nat_lit 7841, Int.ofNat (nat_lit 1))]
theorem atom2350Coded_decode : atom2350 = SparsePolynomial.decodeCubic 24 atom2350Coded := by decide +kernel
theorem atom2350Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded) := by
  have h := atom2350_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2350Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2351 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2351 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2351 = ((g 13) * (g 14) * (g 18)) := by
  norm_num [atom2351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2351_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51223348582560 : Int) atom2351) := by
  rw [SparsePolynomial.eval_scale, eval_atom2351]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2351Coded : CoefficientMerge.Poly := [(nat_lit 7842, Int.ofNat (nat_lit 1))]
theorem atom2351Coded_decode : atom2351 = SparsePolynomial.decodeCubic 24 atom2351Coded := by decide +kernel
theorem atom2351Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) := by
  have h := atom2351_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2351Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2352 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2352 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2352 = ((g 13) * (g 14) * (g 20)) := by
  norm_num [atom2352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2352_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132506149960800 : Int) atom2352) := by
  rw [SparsePolynomial.eval_scale, eval_atom2352]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2352Coded : CoefficientMerge.Poly := [(nat_lit 7844, Int.ofNat (nat_lit 1))]
theorem atom2352Coded_decode : atom2352 = SparsePolynomial.decodeCubic 24 atom2352Coded := by decide +kernel
theorem atom2352Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) := by
  have h := atom2352_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2352Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2353 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2353 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2353 = ((g 13) * (g 14) * (g 21)) := by
  norm_num [atom2353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2353_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61132353559200 : Int) atom2353) := by
  rw [SparsePolynomial.eval_scale, eval_atom2353]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2353Coded : CoefficientMerge.Poly := [(nat_lit 7845, Int.ofNat (nat_lit 1))]
theorem atom2353Coded_decode : atom2353 = SparsePolynomial.decodeCubic 24 atom2353Coded := by decide +kernel
theorem atom2353Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded) := by
  have h := atom2353_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2353Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2354 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2354 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2354 = ((g 13) * (g 14) * (g 22)) := by
  norm_num [atom2354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2354_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (93303439004160 : Int) atom2354) := by
  rw [SparsePolynomial.eval_scale, eval_atom2354]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2354Coded : CoefficientMerge.Poly := [(nat_lit 7846, Int.ofNat (nat_lit 1))]
theorem atom2354Coded_decode : atom2354 = SparsePolynomial.decodeCubic 24 atom2354Coded := by decide +kernel
theorem atom2354Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) := by
  have h := atom2354_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2354Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2355 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2355 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2355 = ((g 13) * (g 14) * (g 23)) := by
  norm_num [atom2355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2355_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144759386217600 : Int) atom2355) := by
  rw [SparsePolynomial.eval_scale, eval_atom2355]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2355Coded : CoefficientMerge.Poly := [(nat_lit 7847, Int.ofNat (nat_lit 1))]
theorem atom2355Coded_decode : atom2355 = SparsePolynomial.decodeCubic 24 atom2355Coded := by decide +kernel
theorem atom2355Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded) := by
  have h := atom2355_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2355Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2356 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom2356 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2356 = ((g 13) * (g 15) * (g 15)) := by
  norm_num [atom2356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2356_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12326846716800 : Int) atom2356) := by
  rw [SparsePolynomial.eval_scale, eval_atom2356]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2356Coded : CoefficientMerge.Poly := [(nat_lit 7863, Int.ofNat (nat_lit 1))]
theorem atom2356Coded_decode : atom2356 = SparsePolynomial.decodeCubic 24 atom2356Coded := by decide +kernel
theorem atom2356Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) := by
  have h := atom2356_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2356Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2357 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2357 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2357 = ((g 13) * (g 15) * (g 16)) := by
  norm_num [atom2357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2357_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16446426796800 : Int) atom2357) := by
  rw [SparsePolynomial.eval_scale, eval_atom2357]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2357Coded : CoefficientMerge.Poly := [(nat_lit 7864, Int.ofNat (nat_lit 1))]
theorem atom2357Coded_decode : atom2357 = SparsePolynomial.decodeCubic 24 atom2357Coded := by decide +kernel
theorem atom2357Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) := by
  have h := atom2357_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2357Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2358 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2358 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2358 = ((g 13) * (g 15) * (g 17)) := by
  norm_num [atom2358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2358_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21591915206400 : Int) atom2358) := by
  rw [SparsePolynomial.eval_scale, eval_atom2358]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2358Coded : CoefficientMerge.Poly := [(nat_lit 7865, Int.ofNat (nat_lit 1))]
theorem atom2358Coded_decode : atom2358 = SparsePolynomial.decodeCubic 24 atom2358Coded := by decide +kernel
theorem atom2358Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded) := by
  have h := atom2358_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2358Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2359 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2359 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2359 = ((g 13) * (g 15) * (g 18)) := by
  norm_num [atom2359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2359_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56573559584640 : Int) atom2359) := by
  rw [SparsePolynomial.eval_scale, eval_atom2359]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2359Coded : CoefficientMerge.Poly := [(nat_lit 7866, Int.ofNat (nat_lit 1))]
theorem atom2359Coded_decode : atom2359 = SparsePolynomial.decodeCubic 24 atom2359Coded := by decide +kernel
theorem atom2359Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) := by
  have h := atom2359_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2359Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2360 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2360 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2360 = ((g 13) * (g 15) * (g 20)) := by
  norm_num [atom2360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2360_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193558447555200 : Int) atom2360) := by
  rw [SparsePolynomial.eval_scale, eval_atom2360]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2360Coded : CoefficientMerge.Poly := [(nat_lit 7868, Int.ofNat (nat_lit 1))]
theorem atom2360Coded_decode : atom2360 = SparsePolynomial.decodeCubic 24 atom2360Coded := by decide +kernel
theorem atom2360Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded) := by
  have h := atom2360_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2360Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2361 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2361 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2361 = ((g 13) * (g 15) * (g 21)) := by
  norm_num [atom2361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2361_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150284455876800 : Int) atom2361) := by
  rw [SparsePolynomial.eval_scale, eval_atom2361]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 13) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2361Coded : CoefficientMerge.Poly := [(nat_lit 7869, Int.ofNat (nat_lit 1))]
theorem atom2361Coded_decode : atom2361 = SparsePolynomial.decodeCubic 24 atom2361Coded := by decide +kernel
theorem atom2361Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) := by
  have h := atom2361_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2361Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2362 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2362 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2362 = ((g 13) * (g 15) * (g 22)) := by
  norm_num [atom2362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2362_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167872622480640 : Int) atom2362) := by
  rw [SparsePolynomial.eval_scale, eval_atom2362]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 13) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2362Coded : CoefficientMerge.Poly := [(nat_lit 7870, Int.ofNat (nat_lit 1))]
theorem atom2362Coded_decode : atom2362 = SparsePolynomial.decodeCubic 24 atom2362Coded := by decide +kernel
theorem atom2362Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) := by
  have h := atom2362_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2362Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2363 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2363 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2363 = ((g 13) * (g 15) * (g 23)) := by
  norm_num [atom2363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2363_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (269694894016800 : Int) atom2363) := by
  rw [SparsePolynomial.eval_scale, eval_atom2363]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 13) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2363Coded : CoefficientMerge.Poly := [(nat_lit 7871, Int.ofNat (nat_lit 1))]
theorem atom2363Coded_decode : atom2363 = SparsePolynomial.decodeCubic 24 atom2363Coded := by decide +kernel
theorem atom2363Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded) := by
  have h := atom2363_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2363Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2364 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2364 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2364 = ((g 13) * (g 16) * (g 16)) := by
  norm_num [atom2364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2364_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23638416278400 : Int) atom2364) := by
  rw [SparsePolynomial.eval_scale, eval_atom2364]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2364Coded : CoefficientMerge.Poly := [(nat_lit 7888, Int.ofNat (nat_lit 1))]
theorem atom2364Coded_decode : atom2364 = SparsePolynomial.decodeCubic 24 atom2364Coded := by decide +kernel
theorem atom2364Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) := by
  have h := atom2364_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2364Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2365 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2365 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2365 = ((g 13) * (g 16) * (g 17)) := by
  norm_num [atom2365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2365_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50381135481600 : Int) atom2365) := by
  rw [SparsePolynomial.eval_scale, eval_atom2365]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2365Coded : CoefficientMerge.Poly := [(nat_lit 7889, Int.ofNat (nat_lit 1))]
theorem atom2365Coded_decode : atom2365 = SparsePolynomial.decodeCubic 24 atom2365Coded := by decide +kernel
theorem atom2365Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded) := by
  have h := atom2365_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2365Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2366 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2366 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2366 = ((g 13) * (g 16) * (g 18)) := by
  norm_num [atom2366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2366_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83843818128000 : Int) atom2366) := by
  rw [SparsePolynomial.eval_scale, eval_atom2366]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2366Coded : CoefficientMerge.Poly := [(nat_lit 7890, Int.ofNat (nat_lit 1))]
theorem atom2366Coded_decode : atom2366 = SparsePolynomial.decodeCubic 24 atom2366Coded := by decide +kernel
theorem atom2366Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) := by
  have h := atom2366_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2366Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2367 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2367 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2367 = ((g 13) * (g 16) * (g 19)) := by
  norm_num [atom2367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2367_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59016453753600 : Int) atom2367) := by
  rw [SparsePolynomial.eval_scale, eval_atom2367]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2367Coded : CoefficientMerge.Poly := [(nat_lit 7891, Int.ofNat (nat_lit 1))]
theorem atom2367Coded_decode : atom2367 = SparsePolynomial.decodeCubic 24 atom2367Coded := by decide +kernel
theorem atom2367Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) := by
  have h := atom2367_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2367Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2368 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2368 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2368 = ((g 13) * (g 16) * (g 20)) := by
  norm_num [atom2368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2368_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (287033436950400 : Int) atom2368) := by
  rw [SparsePolynomial.eval_scale, eval_atom2368]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2368Coded : CoefficientMerge.Poly := [(nat_lit 7892, Int.ofNat (nat_lit 1))]
theorem atom2368Coded_decode : atom2368 = SparsePolynomial.decodeCubic 24 atom2368Coded := by decide +kernel
theorem atom2368Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded) := by
  have h := atom2368_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2368Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block031 : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7247, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7262, Int.ofNat (nat_lit 11813892552000)), (nat_lit 7263, Int.ofNat (nat_lit 20555375702400)), (nat_lit 7264, Int.ofNat (nat_lit 25700864112000)), (nat_lit 7265, Int.ofNat (nat_lit 30846352521600)), (nat_lit 7266, Int.ofNat (nat_lit 63030033376992)), (nat_lit 7268, Int.ofNat (nat_lit 147325511250720)), (nat_lit 7269, Int.ofNat (nat_lit 90760107715200)), (nat_lit 7270, Int.ofNat (nat_lit 158618185165440)), (nat_lit 7271, Int.ofNat (nat_lit 254072443640400)), (nat_lit 7287, Int.ofNat (nat_lit 28260319348800)), (nat_lit 7288, Int.ofNat (nat_lit 49355227152000)), (nat_lit 7289, Int.ofNat (nat_lit 55542570652800)), (nat_lit 7290, Int.ofNat (nat_lit 108801504755136)), (nat_lit 7291, Int.ofNat (nat_lit 58637029386240)), (nat_lit 7292, Int.ofNat (nat_lit 259360392663360)), (nat_lit 7293, Int.ofNat (nat_lit 226557274695840)), (nat_lit 7294, Int.ofNat (nat_lit 249624699571584)), (nat_lit 7295, Int.ofNat (nat_lit 353960904553200)), (nat_lit 7312, Int.ofNat (nat_lit 43696784577600)), (nat_lit 7313, Int.ofNat (nat_lit 90519134428800)), (nat_lit 7314, Int.ofNat (nat_lit 140214692166336)), (nat_lit 7315, Int.ofNat (nat_lit 118395827159040)), (nat_lit 7316, Int.ofNat (nat_lit 347464800797760)), (nat_lit 7317, Int.ofNat (nat_lit 335468340836640)), (nat_lit 7318, Int.ofNat (nat_lit 321549426739584)), (nat_lit 7319, Int.ofNat (nat_lit 519457604526000)), (nat_lit 7337, Int.ofNat (nat_lit 64633110696000)), (nat_lit 7338, Int.ofNat (nat_lit 186526987263936)), (nat_lit 7339, Int.ofNat (nat_lit 198020101847040)), (nat_lit 7340, Int.ofNat (nat_lit 460401055076160)), (nat_lit 7341, Int.ofNat (nat_lit 471694437735840)), (nat_lit 7342, Int.ofNat (nat_lit 479941683341184)), (nat_lit 7343, Int.ofNat (nat_lit 696128635263600)), (nat_lit 7362, Int.ofNat (nat_lit 151845018393024)), (nat_lit 7363, Int.ofNat (nat_lit 329206824644544)), (nat_lit 7364, Int.ofNat (nat_lit 621009330277248)), (nat_lit 7365, Int.ofNat (nat_lit 644312525376960)), (nat_lit 7366, Int.ofNat (nat_lit 505633160724480)), (nat_lit 7367, Int.ofNat (nat_lit 763431802113024)), (nat_lit 7387, Int.ofNat (nat_lit 139381029526464)), (nat_lit 7388, Int.ofNat (nat_lit 564236889682752)), (nat_lit 7389, Int.ofNat (nat_lit 661893873071904)), (nat_lit 7390, Int.ofNat (nat_lit 499016944603008)), (nat_lit 7391, Int.ofNat (nat_lit 653547015318384)), (nat_lit 7412, Int.ofNat (nat_lit 402272962559424)), (nat_lit 7413, Int.ofNat (nat_lit 772992938684736)), (nat_lit 7414, Int.ofNat (nat_lit 523075355781120)), (nat_lit 7415, Int.ofNat (nat_lit 448819934618880)), (nat_lit 7437, Int.ofNat (nat_lit 327897775234656)), (nat_lit 7438, Int.ofNat (nat_lit 434805549584256)), (nat_lit 7439, Int.ofNat (nat_lit 385561625880816)), (nat_lit 7462, Int.ofNat (nat_lit 68278699175040)), (nat_lit 7463, Int.ofNat (nat_lit 100562774904576)), (nat_lit 7813, Int.ofNat (nat_lit 5136629097600)), (nat_lit 7814, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7818, Int.ofNat (nat_lit 34624275840000)), (nat_lit 7820, Int.ofNat (nat_lit 49043900505600)), (nat_lit 7838, Int.ofNat (nat_lit 4108948905600)), (nat_lit 7840, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7841, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7842, Int.ofNat (nat_lit 51223348582560)), (nat_lit 7844, Int.ofNat (nat_lit 132506149960800)), (nat_lit 7845, Int.ofNat (nat_lit 61132353559200)), (nat_lit 7846, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7847, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7863, Int.ofNat (nat_lit 12326846716800)), (nat_lit 7864, Int.ofNat (nat_lit 16446426796800)), (nat_lit 7865, Int.ofNat (nat_lit 21591915206400)), (nat_lit 7866, Int.ofNat (nat_lit 56573559584640)), (nat_lit 7868, Int.ofNat (nat_lit 193558447555200)), (nat_lit 7869, Int.ofNat (nat_lit 150284455876800)), (nat_lit 7870, Int.ofNat (nat_lit 167872622480640)), (nat_lit 7871, Int.ofNat (nat_lit 269694894016800)), (nat_lit 7888, Int.ofNat (nat_lit 23638416278400)), (nat_lit 7889, Int.ofNat (nat_lit 50381135481600)), (nat_lit 7890, Int.ofNat (nat_lit 83843818128000)), (nat_lit 7891, Int.ofNat (nat_lit 59016453753600)), (nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
def block031_data_flat000 : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 93303439004160))]
theorem block031_data_flat000_step : block031_data_flat000 = (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) := by decide +kernel
theorem block031_data_flat000_original : block031_data_flat000 = (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) := by
  rw [block031_data_flat000_step]
def block031_data_flat001 : CoefficientMerge.Poly := [(nat_lit 7247, Int.ofNat (nat_lit 144759386217600))]
theorem block031_data_flat001_step : block031_data_flat001 = (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded) := by decide +kernel
theorem block031_data_flat001_original : block031_data_flat001 = (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded) := by
  rw [block031_data_flat001_step]
def block031_data_flat002 : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7247, Int.ofNat (nat_lit 144759386217600))]
theorem block031_data_flat002_step : block031_data_flat002 = (CoefficientMerge.fastMerge block031_data_flat000 block031_data_flat001) := by decide +kernel
theorem block031_data_flat002_original : block031_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded)) := by
  rw [block031_data_flat002_step, block031_data_flat000_original, block031_data_flat001_original]
def block031_data_flat003 : CoefficientMerge.Poly := [(nat_lit 7262, Int.ofNat (nat_lit 11813892552000))]
theorem block031_data_flat003_step : block031_data_flat003 = (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) := by decide +kernel
theorem block031_data_flat003_original : block031_data_flat003 = (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) := by
  rw [block031_data_flat003_step]
def block031_data_flat004 : CoefficientMerge.Poly := [(nat_lit 7263, Int.ofNat (nat_lit 20555375702400))]
theorem block031_data_flat004_step : block031_data_flat004 = (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) := by decide +kernel
theorem block031_data_flat004_original : block031_data_flat004 = (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) := by
  rw [block031_data_flat004_step]
def block031_data_flat005 : CoefficientMerge.Poly := [(nat_lit 7264, Int.ofNat (nat_lit 25700864112000))]
theorem block031_data_flat005_step : block031_data_flat005 = (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded) := by decide +kernel
theorem block031_data_flat005_original : block031_data_flat005 = (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded) := by
  rw [block031_data_flat005_step]
def block031_data_flat006 : CoefficientMerge.Poly := [(nat_lit 7263, Int.ofNat (nat_lit 20555375702400)), (nat_lit 7264, Int.ofNat (nat_lit 25700864112000))]
theorem block031_data_flat006_step : block031_data_flat006 = (CoefficientMerge.fastMerge block031_data_flat004 block031_data_flat005) := by decide +kernel
theorem block031_data_flat006_original : block031_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded)) := by
  rw [block031_data_flat006_step, block031_data_flat004_original, block031_data_flat005_original]
def block031_data_flat007 : CoefficientMerge.Poly := [(nat_lit 7262, Int.ofNat (nat_lit 11813892552000)), (nat_lit 7263, Int.ofNat (nat_lit 20555375702400)), (nat_lit 7264, Int.ofNat (nat_lit 25700864112000))]
theorem block031_data_flat007_step : block031_data_flat007 = (CoefficientMerge.fastMerge block031_data_flat003 block031_data_flat006) := by decide +kernel
theorem block031_data_flat007_original : block031_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded))) := by
  rw [block031_data_flat007_step, block031_data_flat003_original, block031_data_flat006_original]
def block031_data_flat008 : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7247, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7262, Int.ofNat (nat_lit 11813892552000)), (nat_lit 7263, Int.ofNat (nat_lit 20555375702400)), (nat_lit 7264, Int.ofNat (nat_lit 25700864112000))]
theorem block031_data_flat008_step : block031_data_flat008 = (CoefficientMerge.fastMerge block031_data_flat002 block031_data_flat007) := by decide +kernel
theorem block031_data_flat008_original : block031_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded)))) := by
  rw [block031_data_flat008_step, block031_data_flat002_original, block031_data_flat007_original]
def block031_data_flat009 : CoefficientMerge.Poly := [(nat_lit 7265, Int.ofNat (nat_lit 30846352521600))]
theorem block031_data_flat009_step : block031_data_flat009 = (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) := by decide +kernel
theorem block031_data_flat009_original : block031_data_flat009 = (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) := by
  rw [block031_data_flat009_step]
def block031_data_flat010 : CoefficientMerge.Poly := [(nat_lit 7266, Int.ofNat (nat_lit 63030033376992))]
theorem block031_data_flat010_step : block031_data_flat010 = (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded) := by decide +kernel
theorem block031_data_flat010_original : block031_data_flat010 = (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded) := by
  rw [block031_data_flat010_step]
def block031_data_flat011 : CoefficientMerge.Poly := [(nat_lit 7265, Int.ofNat (nat_lit 30846352521600)), (nat_lit 7266, Int.ofNat (nat_lit 63030033376992))]
theorem block031_data_flat011_step : block031_data_flat011 = (CoefficientMerge.fastMerge block031_data_flat009 block031_data_flat010) := by decide +kernel
theorem block031_data_flat011_original : block031_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded)) := by
  rw [block031_data_flat011_step, block031_data_flat009_original, block031_data_flat010_original]
def block031_data_flat012 : CoefficientMerge.Poly := [(nat_lit 7268, Int.ofNat (nat_lit 147325511250720))]
theorem block031_data_flat012_step : block031_data_flat012 = (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) := by decide +kernel
theorem block031_data_flat012_original : block031_data_flat012 = (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) := by
  rw [block031_data_flat012_step]
def block031_data_flat013 : CoefficientMerge.Poly := [(nat_lit 7269, Int.ofNat (nat_lit 90760107715200))]
theorem block031_data_flat013_step : block031_data_flat013 = (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) := by decide +kernel
theorem block031_data_flat013_original : block031_data_flat013 = (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) := by
  rw [block031_data_flat013_step]
def block031_data_flat014 : CoefficientMerge.Poly := [(nat_lit 7270, Int.ofNat (nat_lit 158618185165440))]
theorem block031_data_flat014_step : block031_data_flat014 = (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded) := by decide +kernel
theorem block031_data_flat014_original : block031_data_flat014 = (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded) := by
  rw [block031_data_flat014_step]
def block031_data_flat015 : CoefficientMerge.Poly := [(nat_lit 7269, Int.ofNat (nat_lit 90760107715200)), (nat_lit 7270, Int.ofNat (nat_lit 158618185165440))]
theorem block031_data_flat015_step : block031_data_flat015 = (CoefficientMerge.fastMerge block031_data_flat013 block031_data_flat014) := by decide +kernel
theorem block031_data_flat015_original : block031_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded)) := by
  rw [block031_data_flat015_step, block031_data_flat013_original, block031_data_flat014_original]
def block031_data_flat016 : CoefficientMerge.Poly := [(nat_lit 7268, Int.ofNat (nat_lit 147325511250720)), (nat_lit 7269, Int.ofNat (nat_lit 90760107715200)), (nat_lit 7270, Int.ofNat (nat_lit 158618185165440))]
theorem block031_data_flat016_step : block031_data_flat016 = (CoefficientMerge.fastMerge block031_data_flat012 block031_data_flat015) := by decide +kernel
theorem block031_data_flat016_original : block031_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded))) := by
  rw [block031_data_flat016_step, block031_data_flat012_original, block031_data_flat015_original]
def block031_data_flat017 : CoefficientMerge.Poly := [(nat_lit 7265, Int.ofNat (nat_lit 30846352521600)), (nat_lit 7266, Int.ofNat (nat_lit 63030033376992)), (nat_lit 7268, Int.ofNat (nat_lit 147325511250720)), (nat_lit 7269, Int.ofNat (nat_lit 90760107715200)), (nat_lit 7270, Int.ofNat (nat_lit 158618185165440))]
theorem block031_data_flat017_step : block031_data_flat017 = (CoefficientMerge.fastMerge block031_data_flat011 block031_data_flat016) := by decide +kernel
theorem block031_data_flat017_original : block031_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded)))) := by
  rw [block031_data_flat017_step, block031_data_flat011_original, block031_data_flat016_original]
def block031_data_flat018 : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7247, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7262, Int.ofNat (nat_lit 11813892552000)), (nat_lit 7263, Int.ofNat (nat_lit 20555375702400)), (nat_lit 7264, Int.ofNat (nat_lit 25700864112000)), (nat_lit 7265, Int.ofNat (nat_lit 30846352521600)), (nat_lit 7266, Int.ofNat (nat_lit 63030033376992)), (nat_lit 7268, Int.ofNat (nat_lit 147325511250720)), (nat_lit 7269, Int.ofNat (nat_lit 90760107715200)), (nat_lit 7270, Int.ofNat (nat_lit 158618185165440))]
theorem block031_data_flat018_step : block031_data_flat018 = (CoefficientMerge.fastMerge block031_data_flat008 block031_data_flat017) := by decide +kernel
theorem block031_data_flat018_original : block031_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded))))) := by
  rw [block031_data_flat018_step, block031_data_flat008_original, block031_data_flat017_original]
def block031_data_flat019 : CoefficientMerge.Poly := [(nat_lit 7271, Int.ofNat (nat_lit 254072443640400))]
theorem block031_data_flat019_step : block031_data_flat019 = (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) := by decide +kernel
theorem block031_data_flat019_original : block031_data_flat019 = (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) := by
  rw [block031_data_flat019_step]
def block031_data_flat020 : CoefficientMerge.Poly := [(nat_lit 7287, Int.ofNat (nat_lit 28260319348800))]
theorem block031_data_flat020_step : block031_data_flat020 = (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded) := by decide +kernel
theorem block031_data_flat020_original : block031_data_flat020 = (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded) := by
  rw [block031_data_flat020_step]
def block031_data_flat021 : CoefficientMerge.Poly := [(nat_lit 7271, Int.ofNat (nat_lit 254072443640400)), (nat_lit 7287, Int.ofNat (nat_lit 28260319348800))]
theorem block031_data_flat021_step : block031_data_flat021 = (CoefficientMerge.fastMerge block031_data_flat019 block031_data_flat020) := by decide +kernel
theorem block031_data_flat021_original : block031_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded)) := by
  rw [block031_data_flat021_step, block031_data_flat019_original, block031_data_flat020_original]
def block031_data_flat022 : CoefficientMerge.Poly := [(nat_lit 7288, Int.ofNat (nat_lit 49355227152000))]
theorem block031_data_flat022_step : block031_data_flat022 = (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) := by decide +kernel
theorem block031_data_flat022_original : block031_data_flat022 = (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) := by
  rw [block031_data_flat022_step]
def block031_data_flat023 : CoefficientMerge.Poly := [(nat_lit 7289, Int.ofNat (nat_lit 55542570652800))]
theorem block031_data_flat023_step : block031_data_flat023 = (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) := by decide +kernel
theorem block031_data_flat023_original : block031_data_flat023 = (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) := by
  rw [block031_data_flat023_step]
def block031_data_flat024 : CoefficientMerge.Poly := [(nat_lit 7290, Int.ofNat (nat_lit 108801504755136))]
theorem block031_data_flat024_step : block031_data_flat024 = (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded) := by decide +kernel
theorem block031_data_flat024_original : block031_data_flat024 = (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded) := by
  rw [block031_data_flat024_step]
def block031_data_flat025 : CoefficientMerge.Poly := [(nat_lit 7289, Int.ofNat (nat_lit 55542570652800)), (nat_lit 7290, Int.ofNat (nat_lit 108801504755136))]
theorem block031_data_flat025_step : block031_data_flat025 = (CoefficientMerge.fastMerge block031_data_flat023 block031_data_flat024) := by decide +kernel
theorem block031_data_flat025_original : block031_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded)) := by
  rw [block031_data_flat025_step, block031_data_flat023_original, block031_data_flat024_original]
def block031_data_flat026 : CoefficientMerge.Poly := [(nat_lit 7288, Int.ofNat (nat_lit 49355227152000)), (nat_lit 7289, Int.ofNat (nat_lit 55542570652800)), (nat_lit 7290, Int.ofNat (nat_lit 108801504755136))]
theorem block031_data_flat026_step : block031_data_flat026 = (CoefficientMerge.fastMerge block031_data_flat022 block031_data_flat025) := by decide +kernel
theorem block031_data_flat026_original : block031_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded))) := by
  rw [block031_data_flat026_step, block031_data_flat022_original, block031_data_flat025_original]
def block031_data_flat027 : CoefficientMerge.Poly := [(nat_lit 7271, Int.ofNat (nat_lit 254072443640400)), (nat_lit 7287, Int.ofNat (nat_lit 28260319348800)), (nat_lit 7288, Int.ofNat (nat_lit 49355227152000)), (nat_lit 7289, Int.ofNat (nat_lit 55542570652800)), (nat_lit 7290, Int.ofNat (nat_lit 108801504755136))]
theorem block031_data_flat027_step : block031_data_flat027 = (CoefficientMerge.fastMerge block031_data_flat021 block031_data_flat026) := by decide +kernel
theorem block031_data_flat027_original : block031_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded)))) := by
  rw [block031_data_flat027_step, block031_data_flat021_original, block031_data_flat026_original]
def block031_data_flat028 : CoefficientMerge.Poly := [(nat_lit 7291, Int.ofNat (nat_lit 58637029386240))]
theorem block031_data_flat028_step : block031_data_flat028 = (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) := by decide +kernel
theorem block031_data_flat028_original : block031_data_flat028 = (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) := by
  rw [block031_data_flat028_step]
def block031_data_flat029 : CoefficientMerge.Poly := [(nat_lit 7292, Int.ofNat (nat_lit 259360392663360))]
theorem block031_data_flat029_step : block031_data_flat029 = (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded) := by decide +kernel
theorem block031_data_flat029_original : block031_data_flat029 = (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded) := by
  rw [block031_data_flat029_step]
def block031_data_flat030 : CoefficientMerge.Poly := [(nat_lit 7291, Int.ofNat (nat_lit 58637029386240)), (nat_lit 7292, Int.ofNat (nat_lit 259360392663360))]
theorem block031_data_flat030_step : block031_data_flat030 = (CoefficientMerge.fastMerge block031_data_flat028 block031_data_flat029) := by decide +kernel
theorem block031_data_flat030_original : block031_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded)) := by
  rw [block031_data_flat030_step, block031_data_flat028_original, block031_data_flat029_original]
def block031_data_flat031 : CoefficientMerge.Poly := [(nat_lit 7293, Int.ofNat (nat_lit 226557274695840))]
theorem block031_data_flat031_step : block031_data_flat031 = (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) := by decide +kernel
theorem block031_data_flat031_original : block031_data_flat031 = (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) := by
  rw [block031_data_flat031_step]
def block031_data_flat032 : CoefficientMerge.Poly := [(nat_lit 7294, Int.ofNat (nat_lit 249624699571584))]
theorem block031_data_flat032_step : block031_data_flat032 = (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) := by decide +kernel
theorem block031_data_flat032_original : block031_data_flat032 = (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) := by
  rw [block031_data_flat032_step]
def block031_data_flat033 : CoefficientMerge.Poly := [(nat_lit 7295, Int.ofNat (nat_lit 353960904553200))]
theorem block031_data_flat033_step : block031_data_flat033 = (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded) := by decide +kernel
theorem block031_data_flat033_original : block031_data_flat033 = (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded) := by
  rw [block031_data_flat033_step]
def block031_data_flat034 : CoefficientMerge.Poly := [(nat_lit 7294, Int.ofNat (nat_lit 249624699571584)), (nat_lit 7295, Int.ofNat (nat_lit 353960904553200))]
theorem block031_data_flat034_step : block031_data_flat034 = (CoefficientMerge.fastMerge block031_data_flat032 block031_data_flat033) := by decide +kernel
theorem block031_data_flat034_original : block031_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded)) := by
  rw [block031_data_flat034_step, block031_data_flat032_original, block031_data_flat033_original]
def block031_data_flat035 : CoefficientMerge.Poly := [(nat_lit 7293, Int.ofNat (nat_lit 226557274695840)), (nat_lit 7294, Int.ofNat (nat_lit 249624699571584)), (nat_lit 7295, Int.ofNat (nat_lit 353960904553200))]
theorem block031_data_flat035_step : block031_data_flat035 = (CoefficientMerge.fastMerge block031_data_flat031 block031_data_flat034) := by decide +kernel
theorem block031_data_flat035_original : block031_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded))) := by
  rw [block031_data_flat035_step, block031_data_flat031_original, block031_data_flat034_original]
def block031_data_flat036 : CoefficientMerge.Poly := [(nat_lit 7291, Int.ofNat (nat_lit 58637029386240)), (nat_lit 7292, Int.ofNat (nat_lit 259360392663360)), (nat_lit 7293, Int.ofNat (nat_lit 226557274695840)), (nat_lit 7294, Int.ofNat (nat_lit 249624699571584)), (nat_lit 7295, Int.ofNat (nat_lit 353960904553200))]
theorem block031_data_flat036_step : block031_data_flat036 = (CoefficientMerge.fastMerge block031_data_flat030 block031_data_flat035) := by decide +kernel
theorem block031_data_flat036_original : block031_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded)))) := by
  rw [block031_data_flat036_step, block031_data_flat030_original, block031_data_flat035_original]
def block031_data_flat037 : CoefficientMerge.Poly := [(nat_lit 7271, Int.ofNat (nat_lit 254072443640400)), (nat_lit 7287, Int.ofNat (nat_lit 28260319348800)), (nat_lit 7288, Int.ofNat (nat_lit 49355227152000)), (nat_lit 7289, Int.ofNat (nat_lit 55542570652800)), (nat_lit 7290, Int.ofNat (nat_lit 108801504755136)), (nat_lit 7291, Int.ofNat (nat_lit 58637029386240)), (nat_lit 7292, Int.ofNat (nat_lit 259360392663360)), (nat_lit 7293, Int.ofNat (nat_lit 226557274695840)), (nat_lit 7294, Int.ofNat (nat_lit 249624699571584)), (nat_lit 7295, Int.ofNat (nat_lit 353960904553200))]
theorem block031_data_flat037_step : block031_data_flat037 = (CoefficientMerge.fastMerge block031_data_flat027 block031_data_flat036) := by decide +kernel
theorem block031_data_flat037_original : block031_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded))))) := by
  rw [block031_data_flat037_step, block031_data_flat027_original, block031_data_flat036_original]
def block031_data_flat038 : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7247, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7262, Int.ofNat (nat_lit 11813892552000)), (nat_lit 7263, Int.ofNat (nat_lit 20555375702400)), (nat_lit 7264, Int.ofNat (nat_lit 25700864112000)), (nat_lit 7265, Int.ofNat (nat_lit 30846352521600)), (nat_lit 7266, Int.ofNat (nat_lit 63030033376992)), (nat_lit 7268, Int.ofNat (nat_lit 147325511250720)), (nat_lit 7269, Int.ofNat (nat_lit 90760107715200)), (nat_lit 7270, Int.ofNat (nat_lit 158618185165440)), (nat_lit 7271, Int.ofNat (nat_lit 254072443640400)), (nat_lit 7287, Int.ofNat (nat_lit 28260319348800)), (nat_lit 7288, Int.ofNat (nat_lit 49355227152000)), (nat_lit 7289, Int.ofNat (nat_lit 55542570652800)), (nat_lit 7290, Int.ofNat (nat_lit 108801504755136)), (nat_lit 7291, Int.ofNat (nat_lit 58637029386240)), (nat_lit 7292, Int.ofNat (nat_lit 259360392663360)), (nat_lit 7293, Int.ofNat (nat_lit 226557274695840)), (nat_lit 7294, Int.ofNat (nat_lit 249624699571584)), (nat_lit 7295, Int.ofNat (nat_lit 353960904553200))]
theorem block031_data_flat038_step : block031_data_flat038 = (CoefficientMerge.fastMerge block031_data_flat018 block031_data_flat037) := by decide +kernel
theorem block031_data_flat038_original : block031_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded)))))) := by
  rw [block031_data_flat038_step, block031_data_flat018_original, block031_data_flat037_original]
def block031_data_flat039 : CoefficientMerge.Poly := [(nat_lit 7312, Int.ofNat (nat_lit 43696784577600))]
theorem block031_data_flat039_step : block031_data_flat039 = (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) := by decide +kernel
theorem block031_data_flat039_original : block031_data_flat039 = (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) := by
  rw [block031_data_flat039_step]
def block031_data_flat040 : CoefficientMerge.Poly := [(nat_lit 7313, Int.ofNat (nat_lit 90519134428800))]
theorem block031_data_flat040_step : block031_data_flat040 = (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded) := by decide +kernel
theorem block031_data_flat040_original : block031_data_flat040 = (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded) := by
  rw [block031_data_flat040_step]
def block031_data_flat041 : CoefficientMerge.Poly := [(nat_lit 7312, Int.ofNat (nat_lit 43696784577600)), (nat_lit 7313, Int.ofNat (nat_lit 90519134428800))]
theorem block031_data_flat041_step : block031_data_flat041 = (CoefficientMerge.fastMerge block031_data_flat039 block031_data_flat040) := by decide +kernel
theorem block031_data_flat041_original : block031_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded)) := by
  rw [block031_data_flat041_step, block031_data_flat039_original, block031_data_flat040_original]
def block031_data_flat042 : CoefficientMerge.Poly := [(nat_lit 7314, Int.ofNat (nat_lit 140214692166336))]
theorem block031_data_flat042_step : block031_data_flat042 = (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) := by decide +kernel
theorem block031_data_flat042_original : block031_data_flat042 = (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) := by
  rw [block031_data_flat042_step]
def block031_data_flat043 : CoefficientMerge.Poly := [(nat_lit 7315, Int.ofNat (nat_lit 118395827159040))]
theorem block031_data_flat043_step : block031_data_flat043 = (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) := by decide +kernel
theorem block031_data_flat043_original : block031_data_flat043 = (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) := by
  rw [block031_data_flat043_step]
def block031_data_flat044 : CoefficientMerge.Poly := [(nat_lit 7316, Int.ofNat (nat_lit 347464800797760))]
theorem block031_data_flat044_step : block031_data_flat044 = (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded) := by decide +kernel
theorem block031_data_flat044_original : block031_data_flat044 = (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded) := by
  rw [block031_data_flat044_step]
def block031_data_flat045 : CoefficientMerge.Poly := [(nat_lit 7315, Int.ofNat (nat_lit 118395827159040)), (nat_lit 7316, Int.ofNat (nat_lit 347464800797760))]
theorem block031_data_flat045_step : block031_data_flat045 = (CoefficientMerge.fastMerge block031_data_flat043 block031_data_flat044) := by decide +kernel
theorem block031_data_flat045_original : block031_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded)) := by
  rw [block031_data_flat045_step, block031_data_flat043_original, block031_data_flat044_original]
def block031_data_flat046 : CoefficientMerge.Poly := [(nat_lit 7314, Int.ofNat (nat_lit 140214692166336)), (nat_lit 7315, Int.ofNat (nat_lit 118395827159040)), (nat_lit 7316, Int.ofNat (nat_lit 347464800797760))]
theorem block031_data_flat046_step : block031_data_flat046 = (CoefficientMerge.fastMerge block031_data_flat042 block031_data_flat045) := by decide +kernel
theorem block031_data_flat046_original : block031_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded))) := by
  rw [block031_data_flat046_step, block031_data_flat042_original, block031_data_flat045_original]
def block031_data_flat047 : CoefficientMerge.Poly := [(nat_lit 7312, Int.ofNat (nat_lit 43696784577600)), (nat_lit 7313, Int.ofNat (nat_lit 90519134428800)), (nat_lit 7314, Int.ofNat (nat_lit 140214692166336)), (nat_lit 7315, Int.ofNat (nat_lit 118395827159040)), (nat_lit 7316, Int.ofNat (nat_lit 347464800797760))]
theorem block031_data_flat047_step : block031_data_flat047 = (CoefficientMerge.fastMerge block031_data_flat041 block031_data_flat046) := by decide +kernel
theorem block031_data_flat047_original : block031_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded)))) := by
  rw [block031_data_flat047_step, block031_data_flat041_original, block031_data_flat046_original]
def block031_data_flat048 : CoefficientMerge.Poly := [(nat_lit 7317, Int.ofNat (nat_lit 335468340836640))]
theorem block031_data_flat048_step : block031_data_flat048 = (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) := by decide +kernel
theorem block031_data_flat048_original : block031_data_flat048 = (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) := by
  rw [block031_data_flat048_step]
def block031_data_flat049 : CoefficientMerge.Poly := [(nat_lit 7318, Int.ofNat (nat_lit 321549426739584))]
theorem block031_data_flat049_step : block031_data_flat049 = (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded) := by decide +kernel
theorem block031_data_flat049_original : block031_data_flat049 = (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded) := by
  rw [block031_data_flat049_step]
def block031_data_flat050 : CoefficientMerge.Poly := [(nat_lit 7317, Int.ofNat (nat_lit 335468340836640)), (nat_lit 7318, Int.ofNat (nat_lit 321549426739584))]
theorem block031_data_flat050_step : block031_data_flat050 = (CoefficientMerge.fastMerge block031_data_flat048 block031_data_flat049) := by decide +kernel
theorem block031_data_flat050_original : block031_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded)) := by
  rw [block031_data_flat050_step, block031_data_flat048_original, block031_data_flat049_original]
def block031_data_flat051 : CoefficientMerge.Poly := [(nat_lit 7319, Int.ofNat (nat_lit 519457604526000))]
theorem block031_data_flat051_step : block031_data_flat051 = (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) := by decide +kernel
theorem block031_data_flat051_original : block031_data_flat051 = (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) := by
  rw [block031_data_flat051_step]
def block031_data_flat052 : CoefficientMerge.Poly := [(nat_lit 7337, Int.ofNat (nat_lit 64633110696000))]
theorem block031_data_flat052_step : block031_data_flat052 = (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) := by decide +kernel
theorem block031_data_flat052_original : block031_data_flat052 = (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) := by
  rw [block031_data_flat052_step]
def block031_data_flat053 : CoefficientMerge.Poly := [(nat_lit 7338, Int.ofNat (nat_lit 186526987263936))]
theorem block031_data_flat053_step : block031_data_flat053 = (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded) := by decide +kernel
theorem block031_data_flat053_original : block031_data_flat053 = (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded) := by
  rw [block031_data_flat053_step]
def block031_data_flat054 : CoefficientMerge.Poly := [(nat_lit 7337, Int.ofNat (nat_lit 64633110696000)), (nat_lit 7338, Int.ofNat (nat_lit 186526987263936))]
theorem block031_data_flat054_step : block031_data_flat054 = (CoefficientMerge.fastMerge block031_data_flat052 block031_data_flat053) := by decide +kernel
theorem block031_data_flat054_original : block031_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded)) := by
  rw [block031_data_flat054_step, block031_data_flat052_original, block031_data_flat053_original]
def block031_data_flat055 : CoefficientMerge.Poly := [(nat_lit 7319, Int.ofNat (nat_lit 519457604526000)), (nat_lit 7337, Int.ofNat (nat_lit 64633110696000)), (nat_lit 7338, Int.ofNat (nat_lit 186526987263936))]
theorem block031_data_flat055_step : block031_data_flat055 = (CoefficientMerge.fastMerge block031_data_flat051 block031_data_flat054) := by decide +kernel
theorem block031_data_flat055_original : block031_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded))) := by
  rw [block031_data_flat055_step, block031_data_flat051_original, block031_data_flat054_original]
def block031_data_flat056 : CoefficientMerge.Poly := [(nat_lit 7317, Int.ofNat (nat_lit 335468340836640)), (nat_lit 7318, Int.ofNat (nat_lit 321549426739584)), (nat_lit 7319, Int.ofNat (nat_lit 519457604526000)), (nat_lit 7337, Int.ofNat (nat_lit 64633110696000)), (nat_lit 7338, Int.ofNat (nat_lit 186526987263936))]
theorem block031_data_flat056_step : block031_data_flat056 = (CoefficientMerge.fastMerge block031_data_flat050 block031_data_flat055) := by decide +kernel
theorem block031_data_flat056_original : block031_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded)))) := by
  rw [block031_data_flat056_step, block031_data_flat050_original, block031_data_flat055_original]
def block031_data_flat057 : CoefficientMerge.Poly := [(nat_lit 7312, Int.ofNat (nat_lit 43696784577600)), (nat_lit 7313, Int.ofNat (nat_lit 90519134428800)), (nat_lit 7314, Int.ofNat (nat_lit 140214692166336)), (nat_lit 7315, Int.ofNat (nat_lit 118395827159040)), (nat_lit 7316, Int.ofNat (nat_lit 347464800797760)), (nat_lit 7317, Int.ofNat (nat_lit 335468340836640)), (nat_lit 7318, Int.ofNat (nat_lit 321549426739584)), (nat_lit 7319, Int.ofNat (nat_lit 519457604526000)), (nat_lit 7337, Int.ofNat (nat_lit 64633110696000)), (nat_lit 7338, Int.ofNat (nat_lit 186526987263936))]
theorem block031_data_flat057_step : block031_data_flat057 = (CoefficientMerge.fastMerge block031_data_flat047 block031_data_flat056) := by decide +kernel
theorem block031_data_flat057_original : block031_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded))))) := by
  rw [block031_data_flat057_step, block031_data_flat047_original, block031_data_flat056_original]
def block031_data_flat058 : CoefficientMerge.Poly := [(nat_lit 7339, Int.ofNat (nat_lit 198020101847040))]
theorem block031_data_flat058_step : block031_data_flat058 = (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) := by decide +kernel
theorem block031_data_flat058_original : block031_data_flat058 = (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) := by
  rw [block031_data_flat058_step]
def block031_data_flat059 : CoefficientMerge.Poly := [(nat_lit 7340, Int.ofNat (nat_lit 460401055076160))]
theorem block031_data_flat059_step : block031_data_flat059 = (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded) := by decide +kernel
theorem block031_data_flat059_original : block031_data_flat059 = (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded) := by
  rw [block031_data_flat059_step]
def block031_data_flat060 : CoefficientMerge.Poly := [(nat_lit 7339, Int.ofNat (nat_lit 198020101847040)), (nat_lit 7340, Int.ofNat (nat_lit 460401055076160))]
theorem block031_data_flat060_step : block031_data_flat060 = (CoefficientMerge.fastMerge block031_data_flat058 block031_data_flat059) := by decide +kernel
theorem block031_data_flat060_original : block031_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded)) := by
  rw [block031_data_flat060_step, block031_data_flat058_original, block031_data_flat059_original]
def block031_data_flat061 : CoefficientMerge.Poly := [(nat_lit 7341, Int.ofNat (nat_lit 471694437735840))]
theorem block031_data_flat061_step : block031_data_flat061 = (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) := by decide +kernel
theorem block031_data_flat061_original : block031_data_flat061 = (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) := by
  rw [block031_data_flat061_step]
def block031_data_flat062 : CoefficientMerge.Poly := [(nat_lit 7342, Int.ofNat (nat_lit 479941683341184))]
theorem block031_data_flat062_step : block031_data_flat062 = (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) := by decide +kernel
theorem block031_data_flat062_original : block031_data_flat062 = (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) := by
  rw [block031_data_flat062_step]
def block031_data_flat063 : CoefficientMerge.Poly := [(nat_lit 7343, Int.ofNat (nat_lit 696128635263600))]
theorem block031_data_flat063_step : block031_data_flat063 = (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded) := by decide +kernel
theorem block031_data_flat063_original : block031_data_flat063 = (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded) := by
  rw [block031_data_flat063_step]
def block031_data_flat064 : CoefficientMerge.Poly := [(nat_lit 7342, Int.ofNat (nat_lit 479941683341184)), (nat_lit 7343, Int.ofNat (nat_lit 696128635263600))]
theorem block031_data_flat064_step : block031_data_flat064 = (CoefficientMerge.fastMerge block031_data_flat062 block031_data_flat063) := by decide +kernel
theorem block031_data_flat064_original : block031_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded)) := by
  rw [block031_data_flat064_step, block031_data_flat062_original, block031_data_flat063_original]
def block031_data_flat065 : CoefficientMerge.Poly := [(nat_lit 7341, Int.ofNat (nat_lit 471694437735840)), (nat_lit 7342, Int.ofNat (nat_lit 479941683341184)), (nat_lit 7343, Int.ofNat (nat_lit 696128635263600))]
theorem block031_data_flat065_step : block031_data_flat065 = (CoefficientMerge.fastMerge block031_data_flat061 block031_data_flat064) := by decide +kernel
theorem block031_data_flat065_original : block031_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded))) := by
  rw [block031_data_flat065_step, block031_data_flat061_original, block031_data_flat064_original]
def block031_data_flat066 : CoefficientMerge.Poly := [(nat_lit 7339, Int.ofNat (nat_lit 198020101847040)), (nat_lit 7340, Int.ofNat (nat_lit 460401055076160)), (nat_lit 7341, Int.ofNat (nat_lit 471694437735840)), (nat_lit 7342, Int.ofNat (nat_lit 479941683341184)), (nat_lit 7343, Int.ofNat (nat_lit 696128635263600))]
theorem block031_data_flat066_step : block031_data_flat066 = (CoefficientMerge.fastMerge block031_data_flat060 block031_data_flat065) := by decide +kernel
theorem block031_data_flat066_original : block031_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded)))) := by
  rw [block031_data_flat066_step, block031_data_flat060_original, block031_data_flat065_original]
def block031_data_flat067 : CoefficientMerge.Poly := [(nat_lit 7362, Int.ofNat (nat_lit 151845018393024))]
theorem block031_data_flat067_step : block031_data_flat067 = (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) := by decide +kernel
theorem block031_data_flat067_original : block031_data_flat067 = (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) := by
  rw [block031_data_flat067_step]
def block031_data_flat068 : CoefficientMerge.Poly := [(nat_lit 7363, Int.ofNat (nat_lit 329206824644544))]
theorem block031_data_flat068_step : block031_data_flat068 = (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded) := by decide +kernel
theorem block031_data_flat068_original : block031_data_flat068 = (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded) := by
  rw [block031_data_flat068_step]
def block031_data_flat069 : CoefficientMerge.Poly := [(nat_lit 7362, Int.ofNat (nat_lit 151845018393024)), (nat_lit 7363, Int.ofNat (nat_lit 329206824644544))]
theorem block031_data_flat069_step : block031_data_flat069 = (CoefficientMerge.fastMerge block031_data_flat067 block031_data_flat068) := by decide +kernel
theorem block031_data_flat069_original : block031_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded)) := by
  rw [block031_data_flat069_step, block031_data_flat067_original, block031_data_flat068_original]
def block031_data_flat070 : CoefficientMerge.Poly := [(nat_lit 7364, Int.ofNat (nat_lit 621009330277248))]
theorem block031_data_flat070_step : block031_data_flat070 = (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) := by decide +kernel
theorem block031_data_flat070_original : block031_data_flat070 = (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) := by
  rw [block031_data_flat070_step]
def block031_data_flat071 : CoefficientMerge.Poly := [(nat_lit 7365, Int.ofNat (nat_lit 644312525376960))]
theorem block031_data_flat071_step : block031_data_flat071 = (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) := by decide +kernel
theorem block031_data_flat071_original : block031_data_flat071 = (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) := by
  rw [block031_data_flat071_step]
def block031_data_flat072 : CoefficientMerge.Poly := [(nat_lit 7366, Int.ofNat (nat_lit 505633160724480))]
theorem block031_data_flat072_step : block031_data_flat072 = (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded) := by decide +kernel
theorem block031_data_flat072_original : block031_data_flat072 = (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded) := by
  rw [block031_data_flat072_step]
def block031_data_flat073 : CoefficientMerge.Poly := [(nat_lit 7365, Int.ofNat (nat_lit 644312525376960)), (nat_lit 7366, Int.ofNat (nat_lit 505633160724480))]
theorem block031_data_flat073_step : block031_data_flat073 = (CoefficientMerge.fastMerge block031_data_flat071 block031_data_flat072) := by decide +kernel
theorem block031_data_flat073_original : block031_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded)) := by
  rw [block031_data_flat073_step, block031_data_flat071_original, block031_data_flat072_original]
def block031_data_flat074 : CoefficientMerge.Poly := [(nat_lit 7364, Int.ofNat (nat_lit 621009330277248)), (nat_lit 7365, Int.ofNat (nat_lit 644312525376960)), (nat_lit 7366, Int.ofNat (nat_lit 505633160724480))]
theorem block031_data_flat074_step : block031_data_flat074 = (CoefficientMerge.fastMerge block031_data_flat070 block031_data_flat073) := by decide +kernel
theorem block031_data_flat074_original : block031_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded))) := by
  rw [block031_data_flat074_step, block031_data_flat070_original, block031_data_flat073_original]
def block031_data_flat075 : CoefficientMerge.Poly := [(nat_lit 7362, Int.ofNat (nat_lit 151845018393024)), (nat_lit 7363, Int.ofNat (nat_lit 329206824644544)), (nat_lit 7364, Int.ofNat (nat_lit 621009330277248)), (nat_lit 7365, Int.ofNat (nat_lit 644312525376960)), (nat_lit 7366, Int.ofNat (nat_lit 505633160724480))]
theorem block031_data_flat075_step : block031_data_flat075 = (CoefficientMerge.fastMerge block031_data_flat069 block031_data_flat074) := by decide +kernel
theorem block031_data_flat075_original : block031_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded)))) := by
  rw [block031_data_flat075_step, block031_data_flat069_original, block031_data_flat074_original]
def block031_data_flat076 : CoefficientMerge.Poly := [(nat_lit 7339, Int.ofNat (nat_lit 198020101847040)), (nat_lit 7340, Int.ofNat (nat_lit 460401055076160)), (nat_lit 7341, Int.ofNat (nat_lit 471694437735840)), (nat_lit 7342, Int.ofNat (nat_lit 479941683341184)), (nat_lit 7343, Int.ofNat (nat_lit 696128635263600)), (nat_lit 7362, Int.ofNat (nat_lit 151845018393024)), (nat_lit 7363, Int.ofNat (nat_lit 329206824644544)), (nat_lit 7364, Int.ofNat (nat_lit 621009330277248)), (nat_lit 7365, Int.ofNat (nat_lit 644312525376960)), (nat_lit 7366, Int.ofNat (nat_lit 505633160724480))]
theorem block031_data_flat076_step : block031_data_flat076 = (CoefficientMerge.fastMerge block031_data_flat066 block031_data_flat075) := by decide +kernel
theorem block031_data_flat076_original : block031_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded))))) := by
  rw [block031_data_flat076_step, block031_data_flat066_original, block031_data_flat075_original]
def block031_data_flat077 : CoefficientMerge.Poly := [(nat_lit 7312, Int.ofNat (nat_lit 43696784577600)), (nat_lit 7313, Int.ofNat (nat_lit 90519134428800)), (nat_lit 7314, Int.ofNat (nat_lit 140214692166336)), (nat_lit 7315, Int.ofNat (nat_lit 118395827159040)), (nat_lit 7316, Int.ofNat (nat_lit 347464800797760)), (nat_lit 7317, Int.ofNat (nat_lit 335468340836640)), (nat_lit 7318, Int.ofNat (nat_lit 321549426739584)), (nat_lit 7319, Int.ofNat (nat_lit 519457604526000)), (nat_lit 7337, Int.ofNat (nat_lit 64633110696000)), (nat_lit 7338, Int.ofNat (nat_lit 186526987263936)), (nat_lit 7339, Int.ofNat (nat_lit 198020101847040)), (nat_lit 7340, Int.ofNat (nat_lit 460401055076160)), (nat_lit 7341, Int.ofNat (nat_lit 471694437735840)), (nat_lit 7342, Int.ofNat (nat_lit 479941683341184)), (nat_lit 7343, Int.ofNat (nat_lit 696128635263600)), (nat_lit 7362, Int.ofNat (nat_lit 151845018393024)), (nat_lit 7363, Int.ofNat (nat_lit 329206824644544)), (nat_lit 7364, Int.ofNat (nat_lit 621009330277248)), (nat_lit 7365, Int.ofNat (nat_lit 644312525376960)), (nat_lit 7366, Int.ofNat (nat_lit 505633160724480))]
theorem block031_data_flat077_step : block031_data_flat077 = (CoefficientMerge.fastMerge block031_data_flat057 block031_data_flat076) := by decide +kernel
theorem block031_data_flat077_original : block031_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded)))))) := by
  rw [block031_data_flat077_step, block031_data_flat057_original, block031_data_flat076_original]
def block031_data_flat078 : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7247, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7262, Int.ofNat (nat_lit 11813892552000)), (nat_lit 7263, Int.ofNat (nat_lit 20555375702400)), (nat_lit 7264, Int.ofNat (nat_lit 25700864112000)), (nat_lit 7265, Int.ofNat (nat_lit 30846352521600)), (nat_lit 7266, Int.ofNat (nat_lit 63030033376992)), (nat_lit 7268, Int.ofNat (nat_lit 147325511250720)), (nat_lit 7269, Int.ofNat (nat_lit 90760107715200)), (nat_lit 7270, Int.ofNat (nat_lit 158618185165440)), (nat_lit 7271, Int.ofNat (nat_lit 254072443640400)), (nat_lit 7287, Int.ofNat (nat_lit 28260319348800)), (nat_lit 7288, Int.ofNat (nat_lit 49355227152000)), (nat_lit 7289, Int.ofNat (nat_lit 55542570652800)), (nat_lit 7290, Int.ofNat (nat_lit 108801504755136)), (nat_lit 7291, Int.ofNat (nat_lit 58637029386240)), (nat_lit 7292, Int.ofNat (nat_lit 259360392663360)), (nat_lit 7293, Int.ofNat (nat_lit 226557274695840)), (nat_lit 7294, Int.ofNat (nat_lit 249624699571584)), (nat_lit 7295, Int.ofNat (nat_lit 353960904553200)), (nat_lit 7312, Int.ofNat (nat_lit 43696784577600)), (nat_lit 7313, Int.ofNat (nat_lit 90519134428800)), (nat_lit 7314, Int.ofNat (nat_lit 140214692166336)), (nat_lit 7315, Int.ofNat (nat_lit 118395827159040)), (nat_lit 7316, Int.ofNat (nat_lit 347464800797760)), (nat_lit 7317, Int.ofNat (nat_lit 335468340836640)), (nat_lit 7318, Int.ofNat (nat_lit 321549426739584)), (nat_lit 7319, Int.ofNat (nat_lit 519457604526000)), (nat_lit 7337, Int.ofNat (nat_lit 64633110696000)), (nat_lit 7338, Int.ofNat (nat_lit 186526987263936)), (nat_lit 7339, Int.ofNat (nat_lit 198020101847040)), (nat_lit 7340, Int.ofNat (nat_lit 460401055076160)), (nat_lit 7341, Int.ofNat (nat_lit 471694437735840)), (nat_lit 7342, Int.ofNat (nat_lit 479941683341184)), (nat_lit 7343, Int.ofNat (nat_lit 696128635263600)), (nat_lit 7362, Int.ofNat (nat_lit 151845018393024)), (nat_lit 7363, Int.ofNat (nat_lit 329206824644544)), (nat_lit 7364, Int.ofNat (nat_lit 621009330277248)), (nat_lit 7365, Int.ofNat (nat_lit 644312525376960)), (nat_lit 7366, Int.ofNat (nat_lit 505633160724480))]
theorem block031_data_flat078_step : block031_data_flat078 = (CoefficientMerge.fastMerge block031_data_flat038 block031_data_flat077) := by decide +kernel
theorem block031_data_flat078_original : block031_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded))))))) := by
  rw [block031_data_flat078_step, block031_data_flat038_original, block031_data_flat077_original]
def block031_data_flat079 : CoefficientMerge.Poly := [(nat_lit 7367, Int.ofNat (nat_lit 763431802113024))]
theorem block031_data_flat079_step : block031_data_flat079 = (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) := by decide +kernel
theorem block031_data_flat079_original : block031_data_flat079 = (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) := by
  rw [block031_data_flat079_step]
def block031_data_flat080 : CoefficientMerge.Poly := [(nat_lit 7387, Int.ofNat (nat_lit 139381029526464))]
theorem block031_data_flat080_step : block031_data_flat080 = (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded) := by decide +kernel
theorem block031_data_flat080_original : block031_data_flat080 = (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded) := by
  rw [block031_data_flat080_step]
def block031_data_flat081 : CoefficientMerge.Poly := [(nat_lit 7367, Int.ofNat (nat_lit 763431802113024)), (nat_lit 7387, Int.ofNat (nat_lit 139381029526464))]
theorem block031_data_flat081_step : block031_data_flat081 = (CoefficientMerge.fastMerge block031_data_flat079 block031_data_flat080) := by decide +kernel
theorem block031_data_flat081_original : block031_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded)) := by
  rw [block031_data_flat081_step, block031_data_flat079_original, block031_data_flat080_original]
def block031_data_flat082 : CoefficientMerge.Poly := [(nat_lit 7388, Int.ofNat (nat_lit 564236889682752))]
theorem block031_data_flat082_step : block031_data_flat082 = (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) := by decide +kernel
theorem block031_data_flat082_original : block031_data_flat082 = (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) := by
  rw [block031_data_flat082_step]
def block031_data_flat083 : CoefficientMerge.Poly := [(nat_lit 7389, Int.ofNat (nat_lit 661893873071904))]
theorem block031_data_flat083_step : block031_data_flat083 = (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) := by decide +kernel
theorem block031_data_flat083_original : block031_data_flat083 = (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) := by
  rw [block031_data_flat083_step]
def block031_data_flat084 : CoefficientMerge.Poly := [(nat_lit 7390, Int.ofNat (nat_lit 499016944603008))]
theorem block031_data_flat084_step : block031_data_flat084 = (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded) := by decide +kernel
theorem block031_data_flat084_original : block031_data_flat084 = (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded) := by
  rw [block031_data_flat084_step]
def block031_data_flat085 : CoefficientMerge.Poly := [(nat_lit 7389, Int.ofNat (nat_lit 661893873071904)), (nat_lit 7390, Int.ofNat (nat_lit 499016944603008))]
theorem block031_data_flat085_step : block031_data_flat085 = (CoefficientMerge.fastMerge block031_data_flat083 block031_data_flat084) := by decide +kernel
theorem block031_data_flat085_original : block031_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded)) := by
  rw [block031_data_flat085_step, block031_data_flat083_original, block031_data_flat084_original]
def block031_data_flat086 : CoefficientMerge.Poly := [(nat_lit 7388, Int.ofNat (nat_lit 564236889682752)), (nat_lit 7389, Int.ofNat (nat_lit 661893873071904)), (nat_lit 7390, Int.ofNat (nat_lit 499016944603008))]
theorem block031_data_flat086_step : block031_data_flat086 = (CoefficientMerge.fastMerge block031_data_flat082 block031_data_flat085) := by decide +kernel
theorem block031_data_flat086_original : block031_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded))) := by
  rw [block031_data_flat086_step, block031_data_flat082_original, block031_data_flat085_original]
def block031_data_flat087 : CoefficientMerge.Poly := [(nat_lit 7367, Int.ofNat (nat_lit 763431802113024)), (nat_lit 7387, Int.ofNat (nat_lit 139381029526464)), (nat_lit 7388, Int.ofNat (nat_lit 564236889682752)), (nat_lit 7389, Int.ofNat (nat_lit 661893873071904)), (nat_lit 7390, Int.ofNat (nat_lit 499016944603008))]
theorem block031_data_flat087_step : block031_data_flat087 = (CoefficientMerge.fastMerge block031_data_flat081 block031_data_flat086) := by decide +kernel
theorem block031_data_flat087_original : block031_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded)))) := by
  rw [block031_data_flat087_step, block031_data_flat081_original, block031_data_flat086_original]
def block031_data_flat088 : CoefficientMerge.Poly := [(nat_lit 7391, Int.ofNat (nat_lit 653547015318384))]
theorem block031_data_flat088_step : block031_data_flat088 = (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) := by decide +kernel
theorem block031_data_flat088_original : block031_data_flat088 = (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) := by
  rw [block031_data_flat088_step]
def block031_data_flat089 : CoefficientMerge.Poly := [(nat_lit 7412, Int.ofNat (nat_lit 402272962559424))]
theorem block031_data_flat089_step : block031_data_flat089 = (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded) := by decide +kernel
theorem block031_data_flat089_original : block031_data_flat089 = (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded) := by
  rw [block031_data_flat089_step]
def block031_data_flat090 : CoefficientMerge.Poly := [(nat_lit 7391, Int.ofNat (nat_lit 653547015318384)), (nat_lit 7412, Int.ofNat (nat_lit 402272962559424))]
theorem block031_data_flat090_step : block031_data_flat090 = (CoefficientMerge.fastMerge block031_data_flat088 block031_data_flat089) := by decide +kernel
theorem block031_data_flat090_original : block031_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded)) := by
  rw [block031_data_flat090_step, block031_data_flat088_original, block031_data_flat089_original]
def block031_data_flat091 : CoefficientMerge.Poly := [(nat_lit 7413, Int.ofNat (nat_lit 772992938684736))]
theorem block031_data_flat091_step : block031_data_flat091 = (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) := by decide +kernel
theorem block031_data_flat091_original : block031_data_flat091 = (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) := by
  rw [block031_data_flat091_step]
def block031_data_flat092 : CoefficientMerge.Poly := [(nat_lit 7414, Int.ofNat (nat_lit 523075355781120))]
theorem block031_data_flat092_step : block031_data_flat092 = (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) := by decide +kernel
theorem block031_data_flat092_original : block031_data_flat092 = (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) := by
  rw [block031_data_flat092_step]
def block031_data_flat093 : CoefficientMerge.Poly := [(nat_lit 7415, Int.ofNat (nat_lit 448819934618880))]
theorem block031_data_flat093_step : block031_data_flat093 = (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded) := by decide +kernel
theorem block031_data_flat093_original : block031_data_flat093 = (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded) := by
  rw [block031_data_flat093_step]
def block031_data_flat094 : CoefficientMerge.Poly := [(nat_lit 7414, Int.ofNat (nat_lit 523075355781120)), (nat_lit 7415, Int.ofNat (nat_lit 448819934618880))]
theorem block031_data_flat094_step : block031_data_flat094 = (CoefficientMerge.fastMerge block031_data_flat092 block031_data_flat093) := by decide +kernel
theorem block031_data_flat094_original : block031_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded)) := by
  rw [block031_data_flat094_step, block031_data_flat092_original, block031_data_flat093_original]
def block031_data_flat095 : CoefficientMerge.Poly := [(nat_lit 7413, Int.ofNat (nat_lit 772992938684736)), (nat_lit 7414, Int.ofNat (nat_lit 523075355781120)), (nat_lit 7415, Int.ofNat (nat_lit 448819934618880))]
theorem block031_data_flat095_step : block031_data_flat095 = (CoefficientMerge.fastMerge block031_data_flat091 block031_data_flat094) := by decide +kernel
theorem block031_data_flat095_original : block031_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded))) := by
  rw [block031_data_flat095_step, block031_data_flat091_original, block031_data_flat094_original]
def block031_data_flat096 : CoefficientMerge.Poly := [(nat_lit 7391, Int.ofNat (nat_lit 653547015318384)), (nat_lit 7412, Int.ofNat (nat_lit 402272962559424)), (nat_lit 7413, Int.ofNat (nat_lit 772992938684736)), (nat_lit 7414, Int.ofNat (nat_lit 523075355781120)), (nat_lit 7415, Int.ofNat (nat_lit 448819934618880))]
theorem block031_data_flat096_step : block031_data_flat096 = (CoefficientMerge.fastMerge block031_data_flat090 block031_data_flat095) := by decide +kernel
theorem block031_data_flat096_original : block031_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded)))) := by
  rw [block031_data_flat096_step, block031_data_flat090_original, block031_data_flat095_original]
def block031_data_flat097 : CoefficientMerge.Poly := [(nat_lit 7367, Int.ofNat (nat_lit 763431802113024)), (nat_lit 7387, Int.ofNat (nat_lit 139381029526464)), (nat_lit 7388, Int.ofNat (nat_lit 564236889682752)), (nat_lit 7389, Int.ofNat (nat_lit 661893873071904)), (nat_lit 7390, Int.ofNat (nat_lit 499016944603008)), (nat_lit 7391, Int.ofNat (nat_lit 653547015318384)), (nat_lit 7412, Int.ofNat (nat_lit 402272962559424)), (nat_lit 7413, Int.ofNat (nat_lit 772992938684736)), (nat_lit 7414, Int.ofNat (nat_lit 523075355781120)), (nat_lit 7415, Int.ofNat (nat_lit 448819934618880))]
theorem block031_data_flat097_step : block031_data_flat097 = (CoefficientMerge.fastMerge block031_data_flat087 block031_data_flat096) := by decide +kernel
theorem block031_data_flat097_original : block031_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded))))) := by
  rw [block031_data_flat097_step, block031_data_flat087_original, block031_data_flat096_original]
def block031_data_flat098 : CoefficientMerge.Poly := [(nat_lit 7437, Int.ofNat (nat_lit 327897775234656))]
theorem block031_data_flat098_step : block031_data_flat098 = (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) := by decide +kernel
theorem block031_data_flat098_original : block031_data_flat098 = (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) := by
  rw [block031_data_flat098_step]
def block031_data_flat099 : CoefficientMerge.Poly := [(nat_lit 7438, Int.ofNat (nat_lit 434805549584256))]
theorem block031_data_flat099_step : block031_data_flat099 = (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded) := by decide +kernel
theorem block031_data_flat099_original : block031_data_flat099 = (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded) := by
  rw [block031_data_flat099_step]
def block031_data_flat100 : CoefficientMerge.Poly := [(nat_lit 7437, Int.ofNat (nat_lit 327897775234656)), (nat_lit 7438, Int.ofNat (nat_lit 434805549584256))]
theorem block031_data_flat100_step : block031_data_flat100 = (CoefficientMerge.fastMerge block031_data_flat098 block031_data_flat099) := by decide +kernel
theorem block031_data_flat100_original : block031_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded)) := by
  rw [block031_data_flat100_step, block031_data_flat098_original, block031_data_flat099_original]
def block031_data_flat101 : CoefficientMerge.Poly := [(nat_lit 7439, Int.ofNat (nat_lit 385561625880816))]
theorem block031_data_flat101_step : block031_data_flat101 = (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) := by decide +kernel
theorem block031_data_flat101_original : block031_data_flat101 = (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) := by
  rw [block031_data_flat101_step]
def block031_data_flat102 : CoefficientMerge.Poly := [(nat_lit 7462, Int.ofNat (nat_lit 68278699175040))]
theorem block031_data_flat102_step : block031_data_flat102 = (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) := by decide +kernel
theorem block031_data_flat102_original : block031_data_flat102 = (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) := by
  rw [block031_data_flat102_step]
def block031_data_flat103 : CoefficientMerge.Poly := [(nat_lit 7463, Int.ofNat (nat_lit 100562774904576))]
theorem block031_data_flat103_step : block031_data_flat103 = (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded) := by decide +kernel
theorem block031_data_flat103_original : block031_data_flat103 = (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded) := by
  rw [block031_data_flat103_step]
def block031_data_flat104 : CoefficientMerge.Poly := [(nat_lit 7462, Int.ofNat (nat_lit 68278699175040)), (nat_lit 7463, Int.ofNat (nat_lit 100562774904576))]
theorem block031_data_flat104_step : block031_data_flat104 = (CoefficientMerge.fastMerge block031_data_flat102 block031_data_flat103) := by decide +kernel
theorem block031_data_flat104_original : block031_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded)) := by
  rw [block031_data_flat104_step, block031_data_flat102_original, block031_data_flat103_original]
def block031_data_flat105 : CoefficientMerge.Poly := [(nat_lit 7439, Int.ofNat (nat_lit 385561625880816)), (nat_lit 7462, Int.ofNat (nat_lit 68278699175040)), (nat_lit 7463, Int.ofNat (nat_lit 100562774904576))]
theorem block031_data_flat105_step : block031_data_flat105 = (CoefficientMerge.fastMerge block031_data_flat101 block031_data_flat104) := by decide +kernel
theorem block031_data_flat105_original : block031_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded))) := by
  rw [block031_data_flat105_step, block031_data_flat101_original, block031_data_flat104_original]
def block031_data_flat106 : CoefficientMerge.Poly := [(nat_lit 7437, Int.ofNat (nat_lit 327897775234656)), (nat_lit 7438, Int.ofNat (nat_lit 434805549584256)), (nat_lit 7439, Int.ofNat (nat_lit 385561625880816)), (nat_lit 7462, Int.ofNat (nat_lit 68278699175040)), (nat_lit 7463, Int.ofNat (nat_lit 100562774904576))]
theorem block031_data_flat106_step : block031_data_flat106 = (CoefficientMerge.fastMerge block031_data_flat100 block031_data_flat105) := by decide +kernel
theorem block031_data_flat106_original : block031_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded)))) := by
  rw [block031_data_flat106_step, block031_data_flat100_original, block031_data_flat105_original]
def block031_data_flat107 : CoefficientMerge.Poly := [(nat_lit 7813, Int.ofNat (nat_lit 5136629097600))]
theorem block031_data_flat107_step : block031_data_flat107 = (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) := by decide +kernel
theorem block031_data_flat107_original : block031_data_flat107 = (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) := by
  rw [block031_data_flat107_step]
def block031_data_flat108 : CoefficientMerge.Poly := [(nat_lit 7814, Int.ofNat (nat_lit 3083040576000))]
theorem block031_data_flat108_step : block031_data_flat108 = (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded) := by decide +kernel
theorem block031_data_flat108_original : block031_data_flat108 = (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded) := by
  rw [block031_data_flat108_step]
def block031_data_flat109 : CoefficientMerge.Poly := [(nat_lit 7813, Int.ofNat (nat_lit 5136629097600)), (nat_lit 7814, Int.ofNat (nat_lit 3083040576000))]
theorem block031_data_flat109_step : block031_data_flat109 = (CoefficientMerge.fastMerge block031_data_flat107 block031_data_flat108) := by decide +kernel
theorem block031_data_flat109_original : block031_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded)) := by
  rw [block031_data_flat109_step, block031_data_flat107_original, block031_data_flat108_original]
def block031_data_flat110 : CoefficientMerge.Poly := [(nat_lit 7818, Int.ofNat (nat_lit 34624275840000))]
theorem block031_data_flat110_step : block031_data_flat110 = (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) := by decide +kernel
theorem block031_data_flat110_original : block031_data_flat110 = (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) := by
  rw [block031_data_flat110_step]
def block031_data_flat111 : CoefficientMerge.Poly := [(nat_lit 7820, Int.ofNat (nat_lit 49043900505600))]
theorem block031_data_flat111_step : block031_data_flat111 = (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) := by decide +kernel
theorem block031_data_flat111_original : block031_data_flat111 = (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) := by
  rw [block031_data_flat111_step]
def block031_data_flat112 : CoefficientMerge.Poly := [(nat_lit 7838, Int.ofNat (nat_lit 4108948905600))]
theorem block031_data_flat112_step : block031_data_flat112 = (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded) := by decide +kernel
theorem block031_data_flat112_original : block031_data_flat112 = (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded) := by
  rw [block031_data_flat112_step]
def block031_data_flat113 : CoefficientMerge.Poly := [(nat_lit 7820, Int.ofNat (nat_lit 49043900505600)), (nat_lit 7838, Int.ofNat (nat_lit 4108948905600))]
theorem block031_data_flat113_step : block031_data_flat113 = (CoefficientMerge.fastMerge block031_data_flat111 block031_data_flat112) := by decide +kernel
theorem block031_data_flat113_original : block031_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded)) := by
  rw [block031_data_flat113_step, block031_data_flat111_original, block031_data_flat112_original]
def block031_data_flat114 : CoefficientMerge.Poly := [(nat_lit 7818, Int.ofNat (nat_lit 34624275840000)), (nat_lit 7820, Int.ofNat (nat_lit 49043900505600)), (nat_lit 7838, Int.ofNat (nat_lit 4108948905600))]
theorem block031_data_flat114_step : block031_data_flat114 = (CoefficientMerge.fastMerge block031_data_flat110 block031_data_flat113) := by decide +kernel
theorem block031_data_flat114_original : block031_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded))) := by
  rw [block031_data_flat114_step, block031_data_flat110_original, block031_data_flat113_original]
def block031_data_flat115 : CoefficientMerge.Poly := [(nat_lit 7813, Int.ofNat (nat_lit 5136629097600)), (nat_lit 7814, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7818, Int.ofNat (nat_lit 34624275840000)), (nat_lit 7820, Int.ofNat (nat_lit 49043900505600)), (nat_lit 7838, Int.ofNat (nat_lit 4108948905600))]
theorem block031_data_flat115_step : block031_data_flat115 = (CoefficientMerge.fastMerge block031_data_flat109 block031_data_flat114) := by decide +kernel
theorem block031_data_flat115_original : block031_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded)))) := by
  rw [block031_data_flat115_step, block031_data_flat109_original, block031_data_flat114_original]
def block031_data_flat116 : CoefficientMerge.Poly := [(nat_lit 7437, Int.ofNat (nat_lit 327897775234656)), (nat_lit 7438, Int.ofNat (nat_lit 434805549584256)), (nat_lit 7439, Int.ofNat (nat_lit 385561625880816)), (nat_lit 7462, Int.ofNat (nat_lit 68278699175040)), (nat_lit 7463, Int.ofNat (nat_lit 100562774904576)), (nat_lit 7813, Int.ofNat (nat_lit 5136629097600)), (nat_lit 7814, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7818, Int.ofNat (nat_lit 34624275840000)), (nat_lit 7820, Int.ofNat (nat_lit 49043900505600)), (nat_lit 7838, Int.ofNat (nat_lit 4108948905600))]
theorem block031_data_flat116_step : block031_data_flat116 = (CoefficientMerge.fastMerge block031_data_flat106 block031_data_flat115) := by decide +kernel
theorem block031_data_flat116_original : block031_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded))))) := by
  rw [block031_data_flat116_step, block031_data_flat106_original, block031_data_flat115_original]
def block031_data_flat117 : CoefficientMerge.Poly := [(nat_lit 7367, Int.ofNat (nat_lit 763431802113024)), (nat_lit 7387, Int.ofNat (nat_lit 139381029526464)), (nat_lit 7388, Int.ofNat (nat_lit 564236889682752)), (nat_lit 7389, Int.ofNat (nat_lit 661893873071904)), (nat_lit 7390, Int.ofNat (nat_lit 499016944603008)), (nat_lit 7391, Int.ofNat (nat_lit 653547015318384)), (nat_lit 7412, Int.ofNat (nat_lit 402272962559424)), (nat_lit 7413, Int.ofNat (nat_lit 772992938684736)), (nat_lit 7414, Int.ofNat (nat_lit 523075355781120)), (nat_lit 7415, Int.ofNat (nat_lit 448819934618880)), (nat_lit 7437, Int.ofNat (nat_lit 327897775234656)), (nat_lit 7438, Int.ofNat (nat_lit 434805549584256)), (nat_lit 7439, Int.ofNat (nat_lit 385561625880816)), (nat_lit 7462, Int.ofNat (nat_lit 68278699175040)), (nat_lit 7463, Int.ofNat (nat_lit 100562774904576)), (nat_lit 7813, Int.ofNat (nat_lit 5136629097600)), (nat_lit 7814, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7818, Int.ofNat (nat_lit 34624275840000)), (nat_lit 7820, Int.ofNat (nat_lit 49043900505600)), (nat_lit 7838, Int.ofNat (nat_lit 4108948905600))]
theorem block031_data_flat117_step : block031_data_flat117 = (CoefficientMerge.fastMerge block031_data_flat097 block031_data_flat116) := by decide +kernel
theorem block031_data_flat117_original : block031_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded)))))) := by
  rw [block031_data_flat117_step, block031_data_flat097_original, block031_data_flat116_original]
def block031_data_flat118 : CoefficientMerge.Poly := [(nat_lit 7840, Int.ofNat (nat_lit 3083040576000))]
theorem block031_data_flat118_step : block031_data_flat118 = (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) := by decide +kernel
theorem block031_data_flat118_original : block031_data_flat118 = (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) := by
  rw [block031_data_flat118_step]
def block031_data_flat119 : CoefficientMerge.Poly := [(nat_lit 7841, Int.ofNat (nat_lit 6166081152000))]
theorem block031_data_flat119_step : block031_data_flat119 = (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded) := by decide +kernel
theorem block031_data_flat119_original : block031_data_flat119 = (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded) := by
  rw [block031_data_flat119_step]
def block031_data_flat120 : CoefficientMerge.Poly := [(nat_lit 7840, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7841, Int.ofNat (nat_lit 6166081152000))]
theorem block031_data_flat120_step : block031_data_flat120 = (CoefficientMerge.fastMerge block031_data_flat118 block031_data_flat119) := by decide +kernel
theorem block031_data_flat120_original : block031_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded)) := by
  rw [block031_data_flat120_step, block031_data_flat118_original, block031_data_flat119_original]
def block031_data_flat121 : CoefficientMerge.Poly := [(nat_lit 7842, Int.ofNat (nat_lit 51223348582560))]
theorem block031_data_flat121_step : block031_data_flat121 = (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) := by decide +kernel
theorem block031_data_flat121_original : block031_data_flat121 = (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) := by
  rw [block031_data_flat121_step]
def block031_data_flat122 : CoefficientMerge.Poly := [(nat_lit 7844, Int.ofNat (nat_lit 132506149960800))]
theorem block031_data_flat122_step : block031_data_flat122 = (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) := by decide +kernel
theorem block031_data_flat122_original : block031_data_flat122 = (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) := by
  rw [block031_data_flat122_step]
def block031_data_flat123 : CoefficientMerge.Poly := [(nat_lit 7845, Int.ofNat (nat_lit 61132353559200))]
theorem block031_data_flat123_step : block031_data_flat123 = (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded) := by decide +kernel
theorem block031_data_flat123_original : block031_data_flat123 = (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded) := by
  rw [block031_data_flat123_step]
def block031_data_flat124 : CoefficientMerge.Poly := [(nat_lit 7844, Int.ofNat (nat_lit 132506149960800)), (nat_lit 7845, Int.ofNat (nat_lit 61132353559200))]
theorem block031_data_flat124_step : block031_data_flat124 = (CoefficientMerge.fastMerge block031_data_flat122 block031_data_flat123) := by decide +kernel
theorem block031_data_flat124_original : block031_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded)) := by
  rw [block031_data_flat124_step, block031_data_flat122_original, block031_data_flat123_original]
def block031_data_flat125 : CoefficientMerge.Poly := [(nat_lit 7842, Int.ofNat (nat_lit 51223348582560)), (nat_lit 7844, Int.ofNat (nat_lit 132506149960800)), (nat_lit 7845, Int.ofNat (nat_lit 61132353559200))]
theorem block031_data_flat125_step : block031_data_flat125 = (CoefficientMerge.fastMerge block031_data_flat121 block031_data_flat124) := by decide +kernel
theorem block031_data_flat125_original : block031_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded))) := by
  rw [block031_data_flat125_step, block031_data_flat121_original, block031_data_flat124_original]
def block031_data_flat126 : CoefficientMerge.Poly := [(nat_lit 7840, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7841, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7842, Int.ofNat (nat_lit 51223348582560)), (nat_lit 7844, Int.ofNat (nat_lit 132506149960800)), (nat_lit 7845, Int.ofNat (nat_lit 61132353559200))]
theorem block031_data_flat126_step : block031_data_flat126 = (CoefficientMerge.fastMerge block031_data_flat120 block031_data_flat125) := by decide +kernel
theorem block031_data_flat126_original : block031_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded)))) := by
  rw [block031_data_flat126_step, block031_data_flat120_original, block031_data_flat125_original]
def block031_data_flat127 : CoefficientMerge.Poly := [(nat_lit 7846, Int.ofNat (nat_lit 93303439004160))]
theorem block031_data_flat127_step : block031_data_flat127 = (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) := by decide +kernel
theorem block031_data_flat127_original : block031_data_flat127 = (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) := by
  rw [block031_data_flat127_step]
def block031_data_flat128 : CoefficientMerge.Poly := [(nat_lit 7847, Int.ofNat (nat_lit 144759386217600))]
theorem block031_data_flat128_step : block031_data_flat128 = (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded) := by decide +kernel
theorem block031_data_flat128_original : block031_data_flat128 = (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded) := by
  rw [block031_data_flat128_step]
def block031_data_flat129 : CoefficientMerge.Poly := [(nat_lit 7846, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7847, Int.ofNat (nat_lit 144759386217600))]
theorem block031_data_flat129_step : block031_data_flat129 = (CoefficientMerge.fastMerge block031_data_flat127 block031_data_flat128) := by decide +kernel
theorem block031_data_flat129_original : block031_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded)) := by
  rw [block031_data_flat129_step, block031_data_flat127_original, block031_data_flat128_original]
def block031_data_flat130 : CoefficientMerge.Poly := [(nat_lit 7863, Int.ofNat (nat_lit 12326846716800))]
theorem block031_data_flat130_step : block031_data_flat130 = (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) := by decide +kernel
theorem block031_data_flat130_original : block031_data_flat130 = (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) := by
  rw [block031_data_flat130_step]
def block031_data_flat131 : CoefficientMerge.Poly := [(nat_lit 7864, Int.ofNat (nat_lit 16446426796800))]
theorem block031_data_flat131_step : block031_data_flat131 = (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) := by decide +kernel
theorem block031_data_flat131_original : block031_data_flat131 = (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) := by
  rw [block031_data_flat131_step]
def block031_data_flat132 : CoefficientMerge.Poly := [(nat_lit 7865, Int.ofNat (nat_lit 21591915206400))]
theorem block031_data_flat132_step : block031_data_flat132 = (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded) := by decide +kernel
theorem block031_data_flat132_original : block031_data_flat132 = (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded) := by
  rw [block031_data_flat132_step]
def block031_data_flat133 : CoefficientMerge.Poly := [(nat_lit 7864, Int.ofNat (nat_lit 16446426796800)), (nat_lit 7865, Int.ofNat (nat_lit 21591915206400))]
theorem block031_data_flat133_step : block031_data_flat133 = (CoefficientMerge.fastMerge block031_data_flat131 block031_data_flat132) := by decide +kernel
theorem block031_data_flat133_original : block031_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded)) := by
  rw [block031_data_flat133_step, block031_data_flat131_original, block031_data_flat132_original]
def block031_data_flat134 : CoefficientMerge.Poly := [(nat_lit 7863, Int.ofNat (nat_lit 12326846716800)), (nat_lit 7864, Int.ofNat (nat_lit 16446426796800)), (nat_lit 7865, Int.ofNat (nat_lit 21591915206400))]
theorem block031_data_flat134_step : block031_data_flat134 = (CoefficientMerge.fastMerge block031_data_flat130 block031_data_flat133) := by decide +kernel
theorem block031_data_flat134_original : block031_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded))) := by
  rw [block031_data_flat134_step, block031_data_flat130_original, block031_data_flat133_original]
def block031_data_flat135 : CoefficientMerge.Poly := [(nat_lit 7846, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7847, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7863, Int.ofNat (nat_lit 12326846716800)), (nat_lit 7864, Int.ofNat (nat_lit 16446426796800)), (nat_lit 7865, Int.ofNat (nat_lit 21591915206400))]
theorem block031_data_flat135_step : block031_data_flat135 = (CoefficientMerge.fastMerge block031_data_flat129 block031_data_flat134) := by decide +kernel
theorem block031_data_flat135_original : block031_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded)))) := by
  rw [block031_data_flat135_step, block031_data_flat129_original, block031_data_flat134_original]
def block031_data_flat136 : CoefficientMerge.Poly := [(nat_lit 7840, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7841, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7842, Int.ofNat (nat_lit 51223348582560)), (nat_lit 7844, Int.ofNat (nat_lit 132506149960800)), (nat_lit 7845, Int.ofNat (nat_lit 61132353559200)), (nat_lit 7846, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7847, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7863, Int.ofNat (nat_lit 12326846716800)), (nat_lit 7864, Int.ofNat (nat_lit 16446426796800)), (nat_lit 7865, Int.ofNat (nat_lit 21591915206400))]
theorem block031_data_flat136_step : block031_data_flat136 = (CoefficientMerge.fastMerge block031_data_flat126 block031_data_flat135) := by decide +kernel
theorem block031_data_flat136_original : block031_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded))))) := by
  rw [block031_data_flat136_step, block031_data_flat126_original, block031_data_flat135_original]
def block031_data_flat137 : CoefficientMerge.Poly := [(nat_lit 7866, Int.ofNat (nat_lit 56573559584640))]
theorem block031_data_flat137_step : block031_data_flat137 = (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) := by decide +kernel
theorem block031_data_flat137_original : block031_data_flat137 = (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) := by
  rw [block031_data_flat137_step]
def block031_data_flat138 : CoefficientMerge.Poly := [(nat_lit 7868, Int.ofNat (nat_lit 193558447555200))]
theorem block031_data_flat138_step : block031_data_flat138 = (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded) := by decide +kernel
theorem block031_data_flat138_original : block031_data_flat138 = (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded) := by
  rw [block031_data_flat138_step]
def block031_data_flat139 : CoefficientMerge.Poly := [(nat_lit 7866, Int.ofNat (nat_lit 56573559584640)), (nat_lit 7868, Int.ofNat (nat_lit 193558447555200))]
theorem block031_data_flat139_step : block031_data_flat139 = (CoefficientMerge.fastMerge block031_data_flat137 block031_data_flat138) := by decide +kernel
theorem block031_data_flat139_original : block031_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded)) := by
  rw [block031_data_flat139_step, block031_data_flat137_original, block031_data_flat138_original]
def block031_data_flat140 : CoefficientMerge.Poly := [(nat_lit 7869, Int.ofNat (nat_lit 150284455876800))]
theorem block031_data_flat140_step : block031_data_flat140 = (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) := by decide +kernel
theorem block031_data_flat140_original : block031_data_flat140 = (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) := by
  rw [block031_data_flat140_step]
def block031_data_flat141 : CoefficientMerge.Poly := [(nat_lit 7870, Int.ofNat (nat_lit 167872622480640))]
theorem block031_data_flat141_step : block031_data_flat141 = (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) := by decide +kernel
theorem block031_data_flat141_original : block031_data_flat141 = (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) := by
  rw [block031_data_flat141_step]
def block031_data_flat142 : CoefficientMerge.Poly := [(nat_lit 7871, Int.ofNat (nat_lit 269694894016800))]
theorem block031_data_flat142_step : block031_data_flat142 = (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded) := by decide +kernel
theorem block031_data_flat142_original : block031_data_flat142 = (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded) := by
  rw [block031_data_flat142_step]
def block031_data_flat143 : CoefficientMerge.Poly := [(nat_lit 7870, Int.ofNat (nat_lit 167872622480640)), (nat_lit 7871, Int.ofNat (nat_lit 269694894016800))]
theorem block031_data_flat143_step : block031_data_flat143 = (CoefficientMerge.fastMerge block031_data_flat141 block031_data_flat142) := by decide +kernel
theorem block031_data_flat143_original : block031_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded)) := by
  rw [block031_data_flat143_step, block031_data_flat141_original, block031_data_flat142_original]
def block031_data_flat144 : CoefficientMerge.Poly := [(nat_lit 7869, Int.ofNat (nat_lit 150284455876800)), (nat_lit 7870, Int.ofNat (nat_lit 167872622480640)), (nat_lit 7871, Int.ofNat (nat_lit 269694894016800))]
theorem block031_data_flat144_step : block031_data_flat144 = (CoefficientMerge.fastMerge block031_data_flat140 block031_data_flat143) := by decide +kernel
theorem block031_data_flat144_original : block031_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded))) := by
  rw [block031_data_flat144_step, block031_data_flat140_original, block031_data_flat143_original]
def block031_data_flat145 : CoefficientMerge.Poly := [(nat_lit 7866, Int.ofNat (nat_lit 56573559584640)), (nat_lit 7868, Int.ofNat (nat_lit 193558447555200)), (nat_lit 7869, Int.ofNat (nat_lit 150284455876800)), (nat_lit 7870, Int.ofNat (nat_lit 167872622480640)), (nat_lit 7871, Int.ofNat (nat_lit 269694894016800))]
theorem block031_data_flat145_step : block031_data_flat145 = (CoefficientMerge.fastMerge block031_data_flat139 block031_data_flat144) := by decide +kernel
theorem block031_data_flat145_original : block031_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded)))) := by
  rw [block031_data_flat145_step, block031_data_flat139_original, block031_data_flat144_original]
def block031_data_flat146 : CoefficientMerge.Poly := [(nat_lit 7888, Int.ofNat (nat_lit 23638416278400))]
theorem block031_data_flat146_step : block031_data_flat146 = (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) := by decide +kernel
theorem block031_data_flat146_original : block031_data_flat146 = (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) := by
  rw [block031_data_flat146_step]
def block031_data_flat147 : CoefficientMerge.Poly := [(nat_lit 7889, Int.ofNat (nat_lit 50381135481600))]
theorem block031_data_flat147_step : block031_data_flat147 = (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded) := by decide +kernel
theorem block031_data_flat147_original : block031_data_flat147 = (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded) := by
  rw [block031_data_flat147_step]
def block031_data_flat148 : CoefficientMerge.Poly := [(nat_lit 7888, Int.ofNat (nat_lit 23638416278400)), (nat_lit 7889, Int.ofNat (nat_lit 50381135481600))]
theorem block031_data_flat148_step : block031_data_flat148 = (CoefficientMerge.fastMerge block031_data_flat146 block031_data_flat147) := by decide +kernel
theorem block031_data_flat148_original : block031_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded)) := by
  rw [block031_data_flat148_step, block031_data_flat146_original, block031_data_flat147_original]
def block031_data_flat149 : CoefficientMerge.Poly := [(nat_lit 7890, Int.ofNat (nat_lit 83843818128000))]
theorem block031_data_flat149_step : block031_data_flat149 = (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) := by decide +kernel
theorem block031_data_flat149_original : block031_data_flat149 = (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) := by
  rw [block031_data_flat149_step]
def block031_data_flat150 : CoefficientMerge.Poly := [(nat_lit 7891, Int.ofNat (nat_lit 59016453753600))]
theorem block031_data_flat150_step : block031_data_flat150 = (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) := by decide +kernel
theorem block031_data_flat150_original : block031_data_flat150 = (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) := by
  rw [block031_data_flat150_step]
def block031_data_flat151 : CoefficientMerge.Poly := [(nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
theorem block031_data_flat151_step : block031_data_flat151 = (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded) := by decide +kernel
theorem block031_data_flat151_original : block031_data_flat151 = (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded) := by
  rw [block031_data_flat151_step]
def block031_data_flat152 : CoefficientMerge.Poly := [(nat_lit 7891, Int.ofNat (nat_lit 59016453753600)), (nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
theorem block031_data_flat152_step : block031_data_flat152 = (CoefficientMerge.fastMerge block031_data_flat150 block031_data_flat151) := by decide +kernel
theorem block031_data_flat152_original : block031_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded)) := by
  rw [block031_data_flat152_step, block031_data_flat150_original, block031_data_flat151_original]
def block031_data_flat153 : CoefficientMerge.Poly := [(nat_lit 7890, Int.ofNat (nat_lit 83843818128000)), (nat_lit 7891, Int.ofNat (nat_lit 59016453753600)), (nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
theorem block031_data_flat153_step : block031_data_flat153 = (CoefficientMerge.fastMerge block031_data_flat149 block031_data_flat152) := by decide +kernel
theorem block031_data_flat153_original : block031_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded))) := by
  rw [block031_data_flat153_step, block031_data_flat149_original, block031_data_flat152_original]
def block031_data_flat154 : CoefficientMerge.Poly := [(nat_lit 7888, Int.ofNat (nat_lit 23638416278400)), (nat_lit 7889, Int.ofNat (nat_lit 50381135481600)), (nat_lit 7890, Int.ofNat (nat_lit 83843818128000)), (nat_lit 7891, Int.ofNat (nat_lit 59016453753600)), (nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
theorem block031_data_flat154_step : block031_data_flat154 = (CoefficientMerge.fastMerge block031_data_flat148 block031_data_flat153) := by decide +kernel
theorem block031_data_flat154_original : block031_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded)))) := by
  rw [block031_data_flat154_step, block031_data_flat148_original, block031_data_flat153_original]
def block031_data_flat155 : CoefficientMerge.Poly := [(nat_lit 7866, Int.ofNat (nat_lit 56573559584640)), (nat_lit 7868, Int.ofNat (nat_lit 193558447555200)), (nat_lit 7869, Int.ofNat (nat_lit 150284455876800)), (nat_lit 7870, Int.ofNat (nat_lit 167872622480640)), (nat_lit 7871, Int.ofNat (nat_lit 269694894016800)), (nat_lit 7888, Int.ofNat (nat_lit 23638416278400)), (nat_lit 7889, Int.ofNat (nat_lit 50381135481600)), (nat_lit 7890, Int.ofNat (nat_lit 83843818128000)), (nat_lit 7891, Int.ofNat (nat_lit 59016453753600)), (nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
theorem block031_data_flat155_step : block031_data_flat155 = (CoefficientMerge.fastMerge block031_data_flat145 block031_data_flat154) := by decide +kernel
theorem block031_data_flat155_original : block031_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded))))) := by
  rw [block031_data_flat155_step, block031_data_flat145_original, block031_data_flat154_original]
def block031_data_flat156 : CoefficientMerge.Poly := [(nat_lit 7840, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7841, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7842, Int.ofNat (nat_lit 51223348582560)), (nat_lit 7844, Int.ofNat (nat_lit 132506149960800)), (nat_lit 7845, Int.ofNat (nat_lit 61132353559200)), (nat_lit 7846, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7847, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7863, Int.ofNat (nat_lit 12326846716800)), (nat_lit 7864, Int.ofNat (nat_lit 16446426796800)), (nat_lit 7865, Int.ofNat (nat_lit 21591915206400)), (nat_lit 7866, Int.ofNat (nat_lit 56573559584640)), (nat_lit 7868, Int.ofNat (nat_lit 193558447555200)), (nat_lit 7869, Int.ofNat (nat_lit 150284455876800)), (nat_lit 7870, Int.ofNat (nat_lit 167872622480640)), (nat_lit 7871, Int.ofNat (nat_lit 269694894016800)), (nat_lit 7888, Int.ofNat (nat_lit 23638416278400)), (nat_lit 7889, Int.ofNat (nat_lit 50381135481600)), (nat_lit 7890, Int.ofNat (nat_lit 83843818128000)), (nat_lit 7891, Int.ofNat (nat_lit 59016453753600)), (nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
theorem block031_data_flat156_step : block031_data_flat156 = (CoefficientMerge.fastMerge block031_data_flat136 block031_data_flat155) := by decide +kernel
theorem block031_data_flat156_original : block031_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded)))))) := by
  rw [block031_data_flat156_step, block031_data_flat136_original, block031_data_flat155_original]
def block031_data_flat157 : CoefficientMerge.Poly := [(nat_lit 7367, Int.ofNat (nat_lit 763431802113024)), (nat_lit 7387, Int.ofNat (nat_lit 139381029526464)), (nat_lit 7388, Int.ofNat (nat_lit 564236889682752)), (nat_lit 7389, Int.ofNat (nat_lit 661893873071904)), (nat_lit 7390, Int.ofNat (nat_lit 499016944603008)), (nat_lit 7391, Int.ofNat (nat_lit 653547015318384)), (nat_lit 7412, Int.ofNat (nat_lit 402272962559424)), (nat_lit 7413, Int.ofNat (nat_lit 772992938684736)), (nat_lit 7414, Int.ofNat (nat_lit 523075355781120)), (nat_lit 7415, Int.ofNat (nat_lit 448819934618880)), (nat_lit 7437, Int.ofNat (nat_lit 327897775234656)), (nat_lit 7438, Int.ofNat (nat_lit 434805549584256)), (nat_lit 7439, Int.ofNat (nat_lit 385561625880816)), (nat_lit 7462, Int.ofNat (nat_lit 68278699175040)), (nat_lit 7463, Int.ofNat (nat_lit 100562774904576)), (nat_lit 7813, Int.ofNat (nat_lit 5136629097600)), (nat_lit 7814, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7818, Int.ofNat (nat_lit 34624275840000)), (nat_lit 7820, Int.ofNat (nat_lit 49043900505600)), (nat_lit 7838, Int.ofNat (nat_lit 4108948905600)), (nat_lit 7840, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7841, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7842, Int.ofNat (nat_lit 51223348582560)), (nat_lit 7844, Int.ofNat (nat_lit 132506149960800)), (nat_lit 7845, Int.ofNat (nat_lit 61132353559200)), (nat_lit 7846, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7847, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7863, Int.ofNat (nat_lit 12326846716800)), (nat_lit 7864, Int.ofNat (nat_lit 16446426796800)), (nat_lit 7865, Int.ofNat (nat_lit 21591915206400)), (nat_lit 7866, Int.ofNat (nat_lit 56573559584640)), (nat_lit 7868, Int.ofNat (nat_lit 193558447555200)), (nat_lit 7869, Int.ofNat (nat_lit 150284455876800)), (nat_lit 7870, Int.ofNat (nat_lit 167872622480640)), (nat_lit 7871, Int.ofNat (nat_lit 269694894016800)), (nat_lit 7888, Int.ofNat (nat_lit 23638416278400)), (nat_lit 7889, Int.ofNat (nat_lit 50381135481600)), (nat_lit 7890, Int.ofNat (nat_lit 83843818128000)), (nat_lit 7891, Int.ofNat (nat_lit 59016453753600)), (nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
theorem block031_data_flat157_step : block031_data_flat157 = (CoefficientMerge.fastMerge block031_data_flat117 block031_data_flat156) := by decide +kernel
theorem block031_data_flat157_original : block031_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded))))))) := by
  rw [block031_data_flat157_step, block031_data_flat117_original, block031_data_flat156_original]
def block031_data_flat158 : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7247, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7262, Int.ofNat (nat_lit 11813892552000)), (nat_lit 7263, Int.ofNat (nat_lit 20555375702400)), (nat_lit 7264, Int.ofNat (nat_lit 25700864112000)), (nat_lit 7265, Int.ofNat (nat_lit 30846352521600)), (nat_lit 7266, Int.ofNat (nat_lit 63030033376992)), (nat_lit 7268, Int.ofNat (nat_lit 147325511250720)), (nat_lit 7269, Int.ofNat (nat_lit 90760107715200)), (nat_lit 7270, Int.ofNat (nat_lit 158618185165440)), (nat_lit 7271, Int.ofNat (nat_lit 254072443640400)), (nat_lit 7287, Int.ofNat (nat_lit 28260319348800)), (nat_lit 7288, Int.ofNat (nat_lit 49355227152000)), (nat_lit 7289, Int.ofNat (nat_lit 55542570652800)), (nat_lit 7290, Int.ofNat (nat_lit 108801504755136)), (nat_lit 7291, Int.ofNat (nat_lit 58637029386240)), (nat_lit 7292, Int.ofNat (nat_lit 259360392663360)), (nat_lit 7293, Int.ofNat (nat_lit 226557274695840)), (nat_lit 7294, Int.ofNat (nat_lit 249624699571584)), (nat_lit 7295, Int.ofNat (nat_lit 353960904553200)), (nat_lit 7312, Int.ofNat (nat_lit 43696784577600)), (nat_lit 7313, Int.ofNat (nat_lit 90519134428800)), (nat_lit 7314, Int.ofNat (nat_lit 140214692166336)), (nat_lit 7315, Int.ofNat (nat_lit 118395827159040)), (nat_lit 7316, Int.ofNat (nat_lit 347464800797760)), (nat_lit 7317, Int.ofNat (nat_lit 335468340836640)), (nat_lit 7318, Int.ofNat (nat_lit 321549426739584)), (nat_lit 7319, Int.ofNat (nat_lit 519457604526000)), (nat_lit 7337, Int.ofNat (nat_lit 64633110696000)), (nat_lit 7338, Int.ofNat (nat_lit 186526987263936)), (nat_lit 7339, Int.ofNat (nat_lit 198020101847040)), (nat_lit 7340, Int.ofNat (nat_lit 460401055076160)), (nat_lit 7341, Int.ofNat (nat_lit 471694437735840)), (nat_lit 7342, Int.ofNat (nat_lit 479941683341184)), (nat_lit 7343, Int.ofNat (nat_lit 696128635263600)), (nat_lit 7362, Int.ofNat (nat_lit 151845018393024)), (nat_lit 7363, Int.ofNat (nat_lit 329206824644544)), (nat_lit 7364, Int.ofNat (nat_lit 621009330277248)), (nat_lit 7365, Int.ofNat (nat_lit 644312525376960)), (nat_lit 7366, Int.ofNat (nat_lit 505633160724480)), (nat_lit 7367, Int.ofNat (nat_lit 763431802113024)), (nat_lit 7387, Int.ofNat (nat_lit 139381029526464)), (nat_lit 7388, Int.ofNat (nat_lit 564236889682752)), (nat_lit 7389, Int.ofNat (nat_lit 661893873071904)), (nat_lit 7390, Int.ofNat (nat_lit 499016944603008)), (nat_lit 7391, Int.ofNat (nat_lit 653547015318384)), (nat_lit 7412, Int.ofNat (nat_lit 402272962559424)), (nat_lit 7413, Int.ofNat (nat_lit 772992938684736)), (nat_lit 7414, Int.ofNat (nat_lit 523075355781120)), (nat_lit 7415, Int.ofNat (nat_lit 448819934618880)), (nat_lit 7437, Int.ofNat (nat_lit 327897775234656)), (nat_lit 7438, Int.ofNat (nat_lit 434805549584256)), (nat_lit 7439, Int.ofNat (nat_lit 385561625880816)), (nat_lit 7462, Int.ofNat (nat_lit 68278699175040)), (nat_lit 7463, Int.ofNat (nat_lit 100562774904576)), (nat_lit 7813, Int.ofNat (nat_lit 5136629097600)), (nat_lit 7814, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7818, Int.ofNat (nat_lit 34624275840000)), (nat_lit 7820, Int.ofNat (nat_lit 49043900505600)), (nat_lit 7838, Int.ofNat (nat_lit 4108948905600)), (nat_lit 7840, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7841, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7842, Int.ofNat (nat_lit 51223348582560)), (nat_lit 7844, Int.ofNat (nat_lit 132506149960800)), (nat_lit 7845, Int.ofNat (nat_lit 61132353559200)), (nat_lit 7846, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7847, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7863, Int.ofNat (nat_lit 12326846716800)), (nat_lit 7864, Int.ofNat (nat_lit 16446426796800)), (nat_lit 7865, Int.ofNat (nat_lit 21591915206400)), (nat_lit 7866, Int.ofNat (nat_lit 56573559584640)), (nat_lit 7868, Int.ofNat (nat_lit 193558447555200)), (nat_lit 7869, Int.ofNat (nat_lit 150284455876800)), (nat_lit 7870, Int.ofNat (nat_lit 167872622480640)), (nat_lit 7871, Int.ofNat (nat_lit 269694894016800)), (nat_lit 7888, Int.ofNat (nat_lit 23638416278400)), (nat_lit 7889, Int.ofNat (nat_lit 50381135481600)), (nat_lit 7890, Int.ofNat (nat_lit 83843818128000)), (nat_lit 7891, Int.ofNat (nat_lit 59016453753600)), (nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
theorem block031_data_flat158_step : block031_data_flat158 = (CoefficientMerge.fastMerge block031_data_flat078 block031_data_flat157) := by decide +kernel
theorem block031_data_flat158_original : block031_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded)))))))) := by
  rw [block031_data_flat158_step, block031_data_flat078_original, block031_data_flat157_original]
def block031_data_flat159 : CoefficientMerge.Poly := [(nat_lit 7246, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7247, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7262, Int.ofNat (nat_lit 11813892552000)), (nat_lit 7263, Int.ofNat (nat_lit 20555375702400)), (nat_lit 7264, Int.ofNat (nat_lit 25700864112000)), (nat_lit 7265, Int.ofNat (nat_lit 30846352521600)), (nat_lit 7266, Int.ofNat (nat_lit 63030033376992)), (nat_lit 7268, Int.ofNat (nat_lit 147325511250720)), (nat_lit 7269, Int.ofNat (nat_lit 90760107715200)), (nat_lit 7270, Int.ofNat (nat_lit 158618185165440)), (nat_lit 7271, Int.ofNat (nat_lit 254072443640400)), (nat_lit 7287, Int.ofNat (nat_lit 28260319348800)), (nat_lit 7288, Int.ofNat (nat_lit 49355227152000)), (nat_lit 7289, Int.ofNat (nat_lit 55542570652800)), (nat_lit 7290, Int.ofNat (nat_lit 108801504755136)), (nat_lit 7291, Int.ofNat (nat_lit 58637029386240)), (nat_lit 7292, Int.ofNat (nat_lit 259360392663360)), (nat_lit 7293, Int.ofNat (nat_lit 226557274695840)), (nat_lit 7294, Int.ofNat (nat_lit 249624699571584)), (nat_lit 7295, Int.ofNat (nat_lit 353960904553200)), (nat_lit 7312, Int.ofNat (nat_lit 43696784577600)), (nat_lit 7313, Int.ofNat (nat_lit 90519134428800)), (nat_lit 7314, Int.ofNat (nat_lit 140214692166336)), (nat_lit 7315, Int.ofNat (nat_lit 118395827159040)), (nat_lit 7316, Int.ofNat (nat_lit 347464800797760)), (nat_lit 7317, Int.ofNat (nat_lit 335468340836640)), (nat_lit 7318, Int.ofNat (nat_lit 321549426739584)), (nat_lit 7319, Int.ofNat (nat_lit 519457604526000)), (nat_lit 7337, Int.ofNat (nat_lit 64633110696000)), (nat_lit 7338, Int.ofNat (nat_lit 186526987263936)), (nat_lit 7339, Int.ofNat (nat_lit 198020101847040)), (nat_lit 7340, Int.ofNat (nat_lit 460401055076160)), (nat_lit 7341, Int.ofNat (nat_lit 471694437735840)), (nat_lit 7342, Int.ofNat (nat_lit 479941683341184)), (nat_lit 7343, Int.ofNat (nat_lit 696128635263600)), (nat_lit 7362, Int.ofNat (nat_lit 151845018393024)), (nat_lit 7363, Int.ofNat (nat_lit 329206824644544)), (nat_lit 7364, Int.ofNat (nat_lit 621009330277248)), (nat_lit 7365, Int.ofNat (nat_lit 644312525376960)), (nat_lit 7366, Int.ofNat (nat_lit 505633160724480)), (nat_lit 7367, Int.ofNat (nat_lit 763431802113024)), (nat_lit 7387, Int.ofNat (nat_lit 139381029526464)), (nat_lit 7388, Int.ofNat (nat_lit 564236889682752)), (nat_lit 7389, Int.ofNat (nat_lit 661893873071904)), (nat_lit 7390, Int.ofNat (nat_lit 499016944603008)), (nat_lit 7391, Int.ofNat (nat_lit 653547015318384)), (nat_lit 7412, Int.ofNat (nat_lit 402272962559424)), (nat_lit 7413, Int.ofNat (nat_lit 772992938684736)), (nat_lit 7414, Int.ofNat (nat_lit 523075355781120)), (nat_lit 7415, Int.ofNat (nat_lit 448819934618880)), (nat_lit 7437, Int.ofNat (nat_lit 327897775234656)), (nat_lit 7438, Int.ofNat (nat_lit 434805549584256)), (nat_lit 7439, Int.ofNat (nat_lit 385561625880816)), (nat_lit 7462, Int.ofNat (nat_lit 68278699175040)), (nat_lit 7463, Int.ofNat (nat_lit 100562774904576)), (nat_lit 7813, Int.ofNat (nat_lit 5136629097600)), (nat_lit 7814, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7818, Int.ofNat (nat_lit 34624275840000)), (nat_lit 7820, Int.ofNat (nat_lit 49043900505600)), (nat_lit 7838, Int.ofNat (nat_lit 4108948905600)), (nat_lit 7840, Int.ofNat (nat_lit 3083040576000)), (nat_lit 7841, Int.ofNat (nat_lit 6166081152000)), (nat_lit 7842, Int.ofNat (nat_lit 51223348582560)), (nat_lit 7844, Int.ofNat (nat_lit 132506149960800)), (nat_lit 7845, Int.ofNat (nat_lit 61132353559200)), (nat_lit 7846, Int.ofNat (nat_lit 93303439004160)), (nat_lit 7847, Int.ofNat (nat_lit 144759386217600)), (nat_lit 7863, Int.ofNat (nat_lit 12326846716800)), (nat_lit 7864, Int.ofNat (nat_lit 16446426796800)), (nat_lit 7865, Int.ofNat (nat_lit 21591915206400)), (nat_lit 7866, Int.ofNat (nat_lit 56573559584640)), (nat_lit 7868, Int.ofNat (nat_lit 193558447555200)), (nat_lit 7869, Int.ofNat (nat_lit 150284455876800)), (nat_lit 7870, Int.ofNat (nat_lit 167872622480640)), (nat_lit 7871, Int.ofNat (nat_lit 269694894016800)), (nat_lit 7888, Int.ofNat (nat_lit 23638416278400)), (nat_lit 7889, Int.ofNat (nat_lit 50381135481600)), (nat_lit 7890, Int.ofNat (nat_lit 83843818128000)), (nat_lit 7891, Int.ofNat (nat_lit 59016453753600)), (nat_lit 7892, Int.ofNat (nat_lit 287033436950400))]
theorem block031_data_flat159_step : block031_data_flat159 = (CoefficientMerge.trim block031_data_flat158) := by decide +kernel
theorem block031_data_flat159_original : block031_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded))))))))) := by
  rw [block031_data_flat159_step, block031_data_flat158_original]
theorem block031_data : block031 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2289Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11813892552000 : Int) atom2291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20555375702400 : Int) atom2292Coded) (CoefficientMerge.scale (25700864112000 : Int) atom2293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30846352521600 : Int) atom2294Coded) (CoefficientMerge.scale (63030033376992 : Int) atom2295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147325511250720 : Int) atom2296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90760107715200 : Int) atom2297Coded) (CoefficientMerge.scale (158618185165440 : Int) atom2298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254072443640400 : Int) atom2299Coded) (CoefficientMerge.scale (28260319348800 : Int) atom2300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49355227152000 : Int) atom2301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55542570652800 : Int) atom2302Coded) (CoefficientMerge.scale (108801504755136 : Int) atom2303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58637029386240 : Int) atom2304Coded) (CoefficientMerge.scale (259360392663360 : Int) atom2305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226557274695840 : Int) atom2306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (249624699571584 : Int) atom2307Coded) (CoefficientMerge.scale (353960904553200 : Int) atom2308Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43696784577600 : Int) atom2309Coded) (CoefficientMerge.scale (90519134428800 : Int) atom2310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140214692166336 : Int) atom2311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118395827159040 : Int) atom2312Coded) (CoefficientMerge.scale (347464800797760 : Int) atom2313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (335468340836640 : Int) atom2314Coded) (CoefficientMerge.scale (321549426739584 : Int) atom2315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519457604526000 : Int) atom2316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64633110696000 : Int) atom2317Coded) (CoefficientMerge.scale (186526987263936 : Int) atom2318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (198020101847040 : Int) atom2319Coded) (CoefficientMerge.scale (460401055076160 : Int) atom2320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471694437735840 : Int) atom2321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (479941683341184 : Int) atom2322Coded) (CoefficientMerge.scale (696128635263600 : Int) atom2323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (151845018393024 : Int) atom2324Coded) (CoefficientMerge.scale (329206824644544 : Int) atom2325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (621009330277248 : Int) atom2326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (644312525376960 : Int) atom2327Coded) (CoefficientMerge.scale (505633160724480 : Int) atom2328Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (763431802113024 : Int) atom2329Coded) (CoefficientMerge.scale (139381029526464 : Int) atom2330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564236889682752 : Int) atom2331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (661893873071904 : Int) atom2332Coded) (CoefficientMerge.scale (499016944603008 : Int) atom2333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (653547015318384 : Int) atom2334Coded) (CoefficientMerge.scale (402272962559424 : Int) atom2335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (772992938684736 : Int) atom2336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (523075355781120 : Int) atom2337Coded) (CoefficientMerge.scale (448819934618880 : Int) atom2338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327897775234656 : Int) atom2339Coded) (CoefficientMerge.scale (434805549584256 : Int) atom2340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (385561625880816 : Int) atom2341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68278699175040 : Int) atom2342Coded) (CoefficientMerge.scale (100562774904576 : Int) atom2343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5136629097600 : Int) atom2344Coded) (CoefficientMerge.scale (3083040576000 : Int) atom2345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34624275840000 : Int) atom2346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49043900505600 : Int) atom2347Coded) (CoefficientMerge.scale (4108948905600 : Int) atom2348Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom2349Coded) (CoefficientMerge.scale (6166081152000 : Int) atom2350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51223348582560 : Int) atom2351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (132506149960800 : Int) atom2352Coded) (CoefficientMerge.scale (61132353559200 : Int) atom2353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (93303439004160 : Int) atom2354Coded) (CoefficientMerge.scale (144759386217600 : Int) atom2355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12326846716800 : Int) atom2356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16446426796800 : Int) atom2357Coded) (CoefficientMerge.scale (21591915206400 : Int) atom2358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56573559584640 : Int) atom2359Coded) (CoefficientMerge.scale (193558447555200 : Int) atom2360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (150284455876800 : Int) atom2361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167872622480640 : Int) atom2362Coded) (CoefficientMerge.scale (269694894016800 : Int) atom2363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23638416278400 : Int) atom2364Coded) (CoefficientMerge.scale (50381135481600 : Int) atom2365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83843818128000 : Int) atom2366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59016453753600 : Int) atom2367Coded) (CoefficientMerge.scale (287033436950400 : Int) atom2368Coded)))))))) := by
  have h : block031 = block031_data_flat159 := by decide +kernel
  exact h.trans block031_data_flat159_original
theorem block031_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block031 := by
  rw [block031_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2289Coded_nonneg g hg hA hB) (atom2290Coded_nonneg g hg hA hB)) (add_nonneg (atom2291Coded_nonneg g hg hA hB) (add_nonneg (atom2292Coded_nonneg g hg hA hB) (atom2293Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2294Coded_nonneg g hg hA hB) (atom2295Coded_nonneg g hg hA hB)) (add_nonneg (atom2296Coded_nonneg g hg hA hB) (add_nonneg (atom2297Coded_nonneg g hg hA hB) (atom2298Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2299Coded_nonneg g hg hA hB) (atom2300Coded_nonneg g hg hA hB)) (add_nonneg (atom2301Coded_nonneg g hg hA hB) (add_nonneg (atom2302Coded_nonneg g hg hA hB) (atom2303Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2304Coded_nonneg g hg hA hB) (atom2305Coded_nonneg g hg hA hB)) (add_nonneg (atom2306Coded_nonneg g hg hA hB) (add_nonneg (atom2307Coded_nonneg g hg hA hB) (atom2308Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2309Coded_nonneg g hg hA hB) (atom2310Coded_nonneg g hg hA hB)) (add_nonneg (atom2311Coded_nonneg g hg hA hB) (add_nonneg (atom2312Coded_nonneg g hg hA hB) (atom2313Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2314Coded_nonneg g hg hA hB) (atom2315Coded_nonneg g hg hA hB)) (add_nonneg (atom2316Coded_nonneg g hg hA hB) (add_nonneg (atom2317Coded_nonneg g hg hA hB) (atom2318Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2319Coded_nonneg g hg hA hB) (atom2320Coded_nonneg g hg hA hB)) (add_nonneg (atom2321Coded_nonneg g hg hA hB) (add_nonneg (atom2322Coded_nonneg g hg hA hB) (atom2323Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2324Coded_nonneg g hg hA hB) (atom2325Coded_nonneg g hg hA hB)) (add_nonneg (atom2326Coded_nonneg g hg hA hB) (add_nonneg (atom2327Coded_nonneg g hg hA hB) (atom2328Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2329Coded_nonneg g hg hA hB) (atom2330Coded_nonneg g hg hA hB)) (add_nonneg (atom2331Coded_nonneg g hg hA hB) (add_nonneg (atom2332Coded_nonneg g hg hA hB) (atom2333Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2334Coded_nonneg g hg hA hB) (atom2335Coded_nonneg g hg hA hB)) (add_nonneg (atom2336Coded_nonneg g hg hA hB) (add_nonneg (atom2337Coded_nonneg g hg hA hB) (atom2338Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2339Coded_nonneg g hg hA hB) (atom2340Coded_nonneg g hg hA hB)) (add_nonneg (atom2341Coded_nonneg g hg hA hB) (add_nonneg (atom2342Coded_nonneg g hg hA hB) (atom2343Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2344Coded_nonneg g hg hA hB) (atom2345Coded_nonneg g hg hA hB)) (add_nonneg (atom2346Coded_nonneg g hg hA hB) (add_nonneg (atom2347Coded_nonneg g hg hA hB) (atom2348Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2349Coded_nonneg g hg hA hB) (atom2350Coded_nonneg g hg hA hB)) (add_nonneg (atom2351Coded_nonneg g hg hA hB) (add_nonneg (atom2352Coded_nonneg g hg hA hB) (atom2353Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2354Coded_nonneg g hg hA hB) (atom2355Coded_nonneg g hg hA hB)) (add_nonneg (atom2356Coded_nonneg g hg hA hB) (add_nonneg (atom2357Coded_nonneg g hg hA hB) (atom2358Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2359Coded_nonneg g hg hA hB) (atom2360Coded_nonneg g hg hA hB)) (add_nonneg (atom2361Coded_nonneg g hg hA hB) (add_nonneg (atom2362Coded_nonneg g hg hA hB) (atom2363Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2364Coded_nonneg g hg hA hB) (atom2365Coded_nonneg g hg hA hB)) (add_nonneg (atom2366Coded_nonneg g hg hA hB) (add_nonneg (atom2367Coded_nonneg g hg hA hB) (atom2368Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
