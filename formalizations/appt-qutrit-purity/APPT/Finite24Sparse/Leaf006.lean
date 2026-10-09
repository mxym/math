-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0289 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0289 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0289 = ((g 0) * (g 3) * (g 14)) := by
  norm_num [atom0289, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0289_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (162146671948800 : Int) atom0289) := by
  rw [SparsePolynomial.eval_scale, eval_atom0289]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0289Coded : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 1))]
theorem atom0289Coded_decode : atom0289 = SparsePolynomial.decodeCubic 24 atom0289Coded := by decide +kernel
theorem atom0289Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) := by
  have h := atom0289_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0289Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0290 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0290 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0290 = ((g 0) * (g 3) * (g 15)) := by
  norm_num [atom0290, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0290_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165208450176000 : Int) atom0290) := by
  rw [SparsePolynomial.eval_scale, eval_atom0290]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0290Coded : CoefficientMerge.Poly := [(nat_lit 87, Int.ofNat (nat_lit 1))]
theorem atom0290Coded_decode : atom0290 = SparsePolynomial.decodeCubic 24 atom0290Coded := by decide +kernel
theorem atom0290Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded) := by
  have h := atom0290_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0290Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0291 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0291 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0291 = ((g 0) * (g 3) * (g 16)) := by
  norm_num [atom0291, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0291_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168270228403200 : Int) atom0291) := by
  rw [SparsePolynomial.eval_scale, eval_atom0291]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0291Coded : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 1))]
theorem atom0291Coded_decode : atom0291 = SparsePolynomial.decodeCubic 24 atom0291Coded := by decide +kernel
theorem atom0291Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) := by
  have h := atom0291_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0291Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0292 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0292 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0292 = ((g 0) * (g 3) * (g 17)) := by
  norm_num [atom0292, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0292_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171332006630400 : Int) atom0292) := by
  rw [SparsePolynomial.eval_scale, eval_atom0292]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0292Coded : CoefficientMerge.Poly := [(nat_lit 89, Int.ofNat (nat_lit 1))]
theorem atom0292Coded_decode : atom0292 = SparsePolynomial.decodeCubic 24 atom0292Coded := by decide +kernel
theorem atom0292Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) := by
  have h := atom0292_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0292Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0293 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0293 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0293 = ((g 0) * (g 3) * (g 18)) := by
  norm_num [atom0293, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0293_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (194231556288000 : Int) atom0293) := by
  rw [SparsePolynomial.eval_scale, eval_atom0293]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0293Coded : CoefficientMerge.Poly := [(nat_lit 90, Int.ofNat (nat_lit 1))]
theorem atom0293Coded_decode : atom0293 = SparsePolynomial.decodeCubic 24 atom0293Coded := by decide +kernel
theorem atom0293Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded) := by
  have h := atom0293_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0293Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0294 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0294 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0294 = ((g 0) * (g 3) * (g 19)) := by
  norm_num [atom0294, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0294_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121344224601600 : Int) atom0294) := by
  rw [SparsePolynomial.eval_scale, eval_atom0294]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0294Coded : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 1))]
theorem atom0294Coded_decode : atom0294 = SparsePolynomial.decodeCubic 24 atom0294Coded := by decide +kernel
theorem atom0294Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) := by
  have h := atom0294_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0294Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0295 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0295 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0295 = ((g 0) * (g 3) * (g 20)) := by
  norm_num [atom0295, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0295_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98593511385600 : Int) atom0295) := by
  rw [SparsePolynomial.eval_scale, eval_atom0295]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0295Coded : CoefficientMerge.Poly := [(nat_lit 92, Int.ofNat (nat_lit 1))]
theorem atom0295Coded_decode : atom0295 = SparsePolynomial.decodeCubic 24 atom0295Coded := by decide +kernel
theorem atom0295Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded) := by
  have h := atom0295_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0295Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0296 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0296 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0296 = ((g 0) * (g 3) * (g 21)) := by
  norm_num [atom0296, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0296_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28810482624000 : Int) atom0296) := by
  rw [SparsePolynomial.eval_scale, eval_atom0296]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 3) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0296Coded : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 1))]
theorem atom0296Coded_decode : atom0296 = SparsePolynomial.decodeCubic 24 atom0296Coded := by decide +kernel
theorem atom0296Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) := by
  have h := atom0296_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0296Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0297 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0297 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0297 = ((g 0) * (g 3) * (g 22)) := by
  norm_num [atom0297, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0297_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38762067254400 : Int) atom0297) := by
  rw [SparsePolynomial.eval_scale, eval_atom0297]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 3) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0297Coded : CoefficientMerge.Poly := [(nat_lit 94, Int.ofNat (nat_lit 1))]
theorem atom0297Coded_decode : atom0297 = SparsePolynomial.decodeCubic 24 atom0297Coded := by decide +kernel
theorem atom0297Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) := by
  have h := atom0297_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0297Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0298 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0298 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0298 = ((g 0) * (g 3) * (g 23)) := by
  norm_num [atom0298, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0298_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4273732108800 : Int) atom0298) := by
  rw [SparsePolynomial.eval_scale, eval_atom0298]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 3) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0298Coded : CoefficientMerge.Poly := [(nat_lit 95, Int.ofNat (nat_lit 1))]
theorem atom0298Coded_decode : atom0298 = SparsePolynomial.decodeCubic 24 atom0298Coded := by decide +kernel
theorem atom0298Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded) := by
  have h := atom0298_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0298Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0299 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0299 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0299 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0299, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0299_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72859948358400 : Int) atom0299) := by
  rw [SparsePolynomial.eval_scale, eval_atom0299]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0299Coded : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 1))]
theorem atom0299Coded_decode : atom0299 = SparsePolynomial.decodeCubic 24 atom0299Coded := by decide +kernel
theorem atom0299Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) := by
  have h := atom0299_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0299Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0300 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0300 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0300 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0300, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0300_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134698516442424 : Int) atom0300) := by
  rw [SparsePolynomial.eval_scale, eval_atom0300]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0300Coded : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 1))]
theorem atom0300Coded_decode : atom0300 = SparsePolynomial.decodeCubic 24 atom0300Coded := by decide +kernel
theorem atom0300Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded) := by
  have h := atom0300_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0300Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0301 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0301 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0301 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0301, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0301_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136589328691200 : Int) atom0301) := by
  rw [SparsePolynomial.eval_scale, eval_atom0301]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0301Coded : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 1))]
theorem atom0301Coded_decode : atom0301 = SparsePolynomial.decodeCubic 24 atom0301Coded := by decide +kernel
theorem atom0301Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) := by
  have h := atom0301_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0301Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0302 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0302 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0302 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0302, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0302_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140671699660800 : Int) atom0302) := by
  rw [SparsePolynomial.eval_scale, eval_atom0302]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0302Coded : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 1))]
theorem atom0302Coded_decode : atom0302 = SparsePolynomial.decodeCubic 24 atom0302Coded := by decide +kernel
theorem atom0302Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) := by
  have h := atom0302_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0302Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0303 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0303 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0303 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0303, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0303_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (144754070630400 : Int) atom0303) := by
  rw [SparsePolynomial.eval_scale, eval_atom0303]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0303Coded : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 1))]
theorem atom0303Coded_decode : atom0303 = SparsePolynomial.decodeCubic 24 atom0303Coded := by decide +kernel
theorem atom0303Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded) := by
  have h := atom0303_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0303Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0304 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0304 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0304 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0304, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0304_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (148836441600000 : Int) atom0304) := by
  rw [SparsePolynomial.eval_scale, eval_atom0304]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0304Coded : CoefficientMerge.Poly := [(nat_lit 105, Int.ofNat (nat_lit 1))]
theorem atom0304Coded_decode : atom0304 = SparsePolynomial.decodeCubic 24 atom0304Coded := by decide +kernel
theorem atom0304Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) := by
  have h := atom0304_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0304Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0305 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0305 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0305 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0305, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0305_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152918812569600 : Int) atom0305) := by
  rw [SparsePolynomial.eval_scale, eval_atom0305]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0305Coded : CoefficientMerge.Poly := [(nat_lit 106, Int.ofNat (nat_lit 1))]
theorem atom0305Coded_decode : atom0305 = SparsePolynomial.decodeCubic 24 atom0305Coded := by decide +kernel
theorem atom0305Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded) := by
  have h := atom0305_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0305Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0306 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0306 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0306 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0306, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0306_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161648510303808 : Int) atom0306) := by
  rw [SparsePolynomial.eval_scale, eval_atom0306]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0306Coded : CoefficientMerge.Poly := [(nat_lit 107, Int.ofNat (nat_lit 1))]
theorem atom0306Coded_decode : atom0306 = SparsePolynomial.decodeCubic 24 atom0306Coded := by decide +kernel
theorem atom0306Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) := by
  have h := atom0306_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0306Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0307 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0307 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0307 = ((g 0) * (g 4) * (g 12)) := by
  norm_num [atom0307, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0307_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215408764568448 : Int) atom0307) := by
  rw [SparsePolynomial.eval_scale, eval_atom0307]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0307Coded : CoefficientMerge.Poly := [(nat_lit 108, Int.ofNat (nat_lit 1))]
theorem atom0307Coded_decode : atom0307 = SparsePolynomial.decodeCubic 24 atom0307Coded := by decide +kernel
theorem atom0307Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) := by
  have h := atom0307_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0307Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0308 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0308 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0308 = ((g 0) * (g 4) * (g 13)) := by
  norm_num [atom0308, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0308_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (196002793324800 : Int) atom0308) := by
  rw [SparsePolynomial.eval_scale, eval_atom0308]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0308Coded : CoefficientMerge.Poly := [(nat_lit 109, Int.ofNat (nat_lit 1))]
theorem atom0308Coded_decode : atom0308 = SparsePolynomial.decodeCubic 24 atom0308Coded := by decide +kernel
theorem atom0308Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded) := by
  have h := atom0308_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0308Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0309 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0309 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0309 = ((g 0) * (g 4) * (g 14)) := by
  norm_num [atom0309, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0309_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (169248296448000 : Int) atom0309) := by
  rw [SparsePolynomial.eval_scale, eval_atom0309]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0309Coded : CoefficientMerge.Poly := [(nat_lit 110, Int.ofNat (nat_lit 1))]
theorem atom0309Coded_decode : atom0309 = SparsePolynomial.decodeCubic 24 atom0309Coded := by decide +kernel
theorem atom0309Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) := by
  have h := atom0309_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0309Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0310 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0310 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0310 = ((g 0) * (g 4) * (g 15)) := by
  norm_num [atom0310, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0310_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (173330667417600 : Int) atom0310) := by
  rw [SparsePolynomial.eval_scale, eval_atom0310]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0310Coded : CoefficientMerge.Poly := [(nat_lit 111, Int.ofNat (nat_lit 1))]
theorem atom0310Coded_decode : atom0310 = SparsePolynomial.decodeCubic 24 atom0310Coded := by decide +kernel
theorem atom0310Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded) := by
  have h := atom0310_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0310Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0311 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0311 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0311 = ((g 0) * (g 4) * (g 16)) := by
  norm_num [atom0311, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0311_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177413038387200 : Int) atom0311) := by
  rw [SparsePolynomial.eval_scale, eval_atom0311]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0311Coded : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 1))]
theorem atom0311Coded_decode : atom0311 = SparsePolynomial.decodeCubic 24 atom0311Coded := by decide +kernel
theorem atom0311Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) := by
  have h := atom0311_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0311Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0312 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0312 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0312 = ((g 0) * (g 4) * (g 17)) := by
  norm_num [atom0312, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0312_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182657267856000 : Int) atom0312) := by
  rw [SparsePolynomial.eval_scale, eval_atom0312]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0312Coded : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 1))]
theorem atom0312Coded_decode : atom0312 = SparsePolynomial.decodeCubic 24 atom0312Coded := by decide +kernel
theorem atom0312Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) := by
  have h := atom0312_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0312Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0313 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0313 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0313 = ((g 0) * (g 4) * (g 18)) := by
  norm_num [atom0313, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0313_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (204644791612800 : Int) atom0313) := by
  rw [SparsePolynomial.eval_scale, eval_atom0313]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0313Coded : CoefficientMerge.Poly := [(nat_lit 114, Int.ofNat (nat_lit 1))]
theorem atom0313Coded_decode : atom0313 = SparsePolynomial.decodeCubic 24 atom0313Coded := by decide +kernel
theorem atom0313Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded) := by
  have h := atom0313_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0313Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0314 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0314 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0314 = ((g 0) * (g 4) * (g 19)) := by
  norm_num [atom0314, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0314_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139707504493200 : Int) atom0314) := by
  rw [SparsePolynomial.eval_scale, eval_atom0314]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0314Coded : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 1))]
theorem atom0314Coded_decode : atom0314 = SparsePolynomial.decodeCubic 24 atom0314Coded := by decide +kernel
theorem atom0314Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) := by
  have h := atom0314_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0314Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0315 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0315 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0315 = ((g 0) * (g 4) * (g 20)) := by
  norm_num [atom0315, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0315_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106646444780400 : Int) atom0315) := by
  rw [SparsePolynomial.eval_scale, eval_atom0315]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0315Coded : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 1))]
theorem atom0315Coded_decode : atom0315 = SparsePolynomial.decodeCubic 24 atom0315Coded := by decide +kernel
theorem atom0315Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded) := by
  have h := atom0315_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0315Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0316 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0316 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0316 = ((g 0) * (g 4) * (g 21)) := by
  norm_num [atom0316, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0316_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47333592558000 : Int) atom0316) := by
  rw [SparsePolynomial.eval_scale, eval_atom0316]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 4) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0316Coded : CoefficientMerge.Poly := [(nat_lit 117, Int.ofNat (nat_lit 1))]
theorem atom0316Coded_decode : atom0316 = SparsePolynomial.decodeCubic 24 atom0316Coded := by decide +kernel
theorem atom0316Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) := by
  have h := atom0316_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0316Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0317 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0317 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0317 = ((g 0) * (g 4) * (g 22)) := by
  norm_num [atom0317, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0317_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57134810502000 : Int) atom0317) := by
  rw [SparsePolynomial.eval_scale, eval_atom0317]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 4) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0317Coded : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 1))]
theorem atom0317Coded_decode : atom0317 = SparsePolynomial.decodeCubic 24 atom0317Coded := by decide +kernel
theorem atom0317Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) := by
  have h := atom0317_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0317Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0318 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0318 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0318 = ((g 0) * (g 4) * (g 23)) := by
  norm_num [atom0318, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0318_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22496108670000 : Int) atom0318) := by
  rw [SparsePolynomial.eval_scale, eval_atom0318]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 4) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0318Coded : CoefficientMerge.Poly := [(nat_lit 119, Int.ofNat (nat_lit 1))]
theorem atom0318Coded_decode : atom0318 = SparsePolynomial.decodeCubic 24 atom0318Coded := by decide +kernel
theorem atom0318Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded) := by
  have h := atom0318_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0318Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0319 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0319 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0319 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0319, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0319_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82684750579200 : Int) atom0319) := by
  rw [SparsePolynomial.eval_scale, eval_atom0319]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0319Coded : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 1))]
theorem atom0319Coded_decode : atom0319 = SparsePolynomial.decodeCubic 24 atom0319Coded := by decide +kernel
theorem atom0319Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) := by
  have h := atom0319_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0319Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0320 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0320 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0320 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0320, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0320_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (148625354906424 : Int) atom0320) := by
  rw [SparsePolynomial.eval_scale, eval_atom0320]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0320Coded : CoefficientMerge.Poly := [(nat_lit 126, Int.ofNat (nat_lit 1))]
theorem atom0320Coded_decode : atom0320 = SparsePolynomial.decodeCubic 24 atom0320Coded := by decide +kernel
theorem atom0320Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded) := by
  have h := atom0320_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0320Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0321 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0321 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0321 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0321, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0321_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (148356622442424 : Int) atom0321) := by
  rw [SparsePolynomial.eval_scale, eval_atom0321]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0321Coded : CoefficientMerge.Poly := [(nat_lit 127, Int.ofNat (nat_lit 1))]
theorem atom0321Coded_decode : atom0321 = SparsePolynomial.decodeCubic 24 atom0321Coded := by decide +kernel
theorem atom0321Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) := by
  have h := atom0321_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0321Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0322 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0322 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0322 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0322_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154227963861576 : Int) atom0322) := by
  rw [SparsePolynomial.eval_scale, eval_atom0322]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0322Coded : CoefficientMerge.Poly := [(nat_lit 128, Int.ofNat (nat_lit 1))]
theorem atom0322Coded_decode : atom0322 = SparsePolynomial.decodeCubic 24 atom0322Coded := by decide +kernel
theorem atom0322Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) := by
  have h := atom0322_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0322Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0323 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0323 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0323 = ((g 0) * (g 5) * (g 9)) := by
  norm_num [atom0323, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0323_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158423328078444 : Int) atom0323) := by
  rw [SparsePolynomial.eval_scale, eval_atom0323]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0323Coded : CoefficientMerge.Poly := [(nat_lit 129, Int.ofNat (nat_lit 1))]
theorem atom0323Coded_decode : atom0323 = SparsePolynomial.decodeCubic 24 atom0323Coded := by decide +kernel
theorem atom0323Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded) := by
  have h := atom0323_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0323Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0324 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0324 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0324 = ((g 0) * (g 5) * (g 10)) := by
  norm_num [atom0324, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0324_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158481345814308 : Int) atom0324) := by
  rw [SparsePolynomial.eval_scale, eval_atom0324]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0324Coded : CoefficientMerge.Poly := [(nat_lit 130, Int.ofNat (nat_lit 1))]
theorem atom0324Coded_decode : atom0324 = SparsePolynomial.decodeCubic 24 atom0324Coded := by decide +kernel
theorem atom0324Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) := by
  have h := atom0324_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0324Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0325 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0325 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0325 = ((g 0) * (g 5) * (g 11)) := by
  norm_num [atom0325, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0325_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165688356575808 : Int) atom0325) := by
  rw [SparsePolynomial.eval_scale, eval_atom0325]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0325Coded : CoefficientMerge.Poly := [(nat_lit 131, Int.ofNat (nat_lit 1))]
theorem atom0325Coded_decode : atom0325 = SparsePolynomial.decodeCubic 24 atom0325Coded := by decide +kernel
theorem atom0325Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded) := by
  have h := atom0325_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0325Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0326 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0326 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0326 = ((g 0) * (g 5) * (g 12)) := by
  norm_num [atom0326, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0326_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220469203582848 : Int) atom0326) := by
  rw [SparsePolynomial.eval_scale, eval_atom0326]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0326Coded : CoefficientMerge.Poly := [(nat_lit 132, Int.ofNat (nat_lit 1))]
theorem atom0326Coded_decode : atom0326 = SparsePolynomial.decodeCubic 24 atom0326Coded := by decide +kernel
theorem atom0326Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) := by
  have h := atom0326_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0326Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0327 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0327 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0327 = ((g 0) * (g 5) * (g 13)) := by
  norm_num [atom0327, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0327_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202083825081600 : Int) atom0327) := by
  rw [SparsePolynomial.eval_scale, eval_atom0327]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0327Coded : CoefficientMerge.Poly := [(nat_lit 133, Int.ofNat (nat_lit 1))]
theorem atom0327Coded_decode : atom0327 = SparsePolynomial.decodeCubic 24 atom0327Coded := by decide +kernel
theorem atom0327Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) := by
  have h := atom0327_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0327Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0328 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0328 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0328 = ((g 0) * (g 5) * (g 14)) := by
  norm_num [atom0328, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0328_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (176349920947200 : Int) atom0328) := by
  rw [SparsePolynomial.eval_scale, eval_atom0328]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0328Coded : CoefficientMerge.Poly := [(nat_lit 134, Int.ofNat (nat_lit 1))]
theorem atom0328Coded_decode : atom0328 = SparsePolynomial.decodeCubic 24 atom0328Coded := by decide +kernel
theorem atom0328Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded) := by
  have h := atom0328_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0328Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0329 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0329 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0329 = ((g 0) * (g 5) * (g 15)) := by
  norm_num [atom0329, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0329_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (181637319427200 : Int) atom0329) := by
  rw [SparsePolynomial.eval_scale, eval_atom0329]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0329Coded : CoefficientMerge.Poly := [(nat_lit 135, Int.ofNat (nat_lit 1))]
theorem atom0329Coded_decode : atom0329 = SparsePolynomial.decodeCubic 24 atom0329Coded := by decide +kernel
theorem atom0329Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) := by
  have h := atom0329_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0329Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0330 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0330 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0330 = ((g 0) * (g 5) * (g 16)) := by
  norm_num [atom0330, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0330_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189880345468800 : Int) atom0330) := by
  rw [SparsePolynomial.eval_scale, eval_atom0330]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0330Coded : CoefficientMerge.Poly := [(nat_lit 136, Int.ofNat (nat_lit 1))]
theorem atom0330Coded_decode : atom0330 = SparsePolynomial.decodeCubic 24 atom0330Coded := by decide +kernel
theorem atom0330Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded) := by
  have h := atom0330_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0330Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0331 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0331 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0331 = ((g 0) * (g 5) * (g 17)) := by
  norm_num [atom0331, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0331_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (195640186896000 : Int) atom0331) := by
  rw [SparsePolynomial.eval_scale, eval_atom0331]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0331Coded : CoefficientMerge.Poly := [(nat_lit 137, Int.ofNat (nat_lit 1))]
theorem atom0331Coded_decode : atom0331 = SparsePolynomial.decodeCubic 24 atom0331Coded := by decide +kernel
theorem atom0331Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) := by
  have h := atom0331_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0331Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0332 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0332 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0332 = ((g 0) * (g 5) * (g 18)) := by
  norm_num [atom0332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0332_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (216778750372800 : Int) atom0332) := by
  rw [SparsePolynomial.eval_scale, eval_atom0332]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0332Coded : CoefficientMerge.Poly := [(nat_lit 138, Int.ofNat (nat_lit 1))]
theorem atom0332Coded_decode : atom0332 = SparsePolynomial.decodeCubic 24 atom0332Coded := by decide +kernel
theorem atom0332Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) := by
  have h := atom0332_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0332Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0333 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0333 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0333 = ((g 0) * (g 5) * (g 19)) := by
  norm_num [atom0333, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0333_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158226313291200 : Int) atom0333) := by
  rw [SparsePolynomial.eval_scale, eval_atom0333]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0333Coded : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 1))]
theorem atom0333Coded_decode : atom0333 = SparsePolynomial.decodeCubic 24 atom0333Coded := by decide +kernel
theorem atom0333Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded) := by
  have h := atom0333_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0333Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0334 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0334 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0334 = ((g 0) * (g 5) * (g 20)) := by
  norm_num [atom0334, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0334_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130583902680000 : Int) atom0334) := by
  rw [SparsePolynomial.eval_scale, eval_atom0334]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0334Coded : CoefficientMerge.Poly := [(nat_lit 140, Int.ofNat (nat_lit 1))]
theorem atom0334Coded_decode : atom0334 = SparsePolynomial.decodeCubic 24 atom0334Coded := by decide +kernel
theorem atom0334Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) := by
  have h := atom0334_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0334Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0335 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0335 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0335 = ((g 0) * (g 5) * (g 21)) := by
  norm_num [atom0335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0335_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75892956955200 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0335Coded : CoefficientMerge.Poly := [(nat_lit 141, Int.ofNat (nat_lit 1))]
theorem atom0335Coded_decode : atom0335 = SparsePolynomial.decodeCubic 24 atom0335Coded := by decide +kernel
theorem atom0335Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded) := by
  have h := atom0335_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0335Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0336 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0336 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0336 = ((g 0) * (g 5) * (g 22)) := by
  norm_num [atom0336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0336_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81891667368000 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0336Coded : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 1))]
theorem atom0336Coded_decode : atom0336 = SparsePolynomial.decodeCubic 24 atom0336Coded := by decide +kernel
theorem atom0336Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) := by
  have h := atom0336_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0336Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0337 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0337 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0337 = ((g 0) * (g 5) * (g 23)) := by
  norm_num [atom0337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0337_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53774798616000 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337Coded : CoefficientMerge.Poly := [(nat_lit 143, Int.ofNat (nat_lit 1))]
theorem atom0337Coded_decode : atom0337 = SparsePolynomial.decodeCubic 24 atom0337Coded := by decide +kernel
theorem atom0337Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) := by
  have h := atom0337_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0337Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0338 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0338 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0338 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0338_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100400811033600 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338Coded : CoefficientMerge.Poly := [(nat_lit 150, Int.ofNat (nat_lit 1))]
theorem atom0338Coded_decode : atom0338 = SparsePolynomial.decodeCubic 24 atom0338Coded := by decide +kernel
theorem atom0338Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded) := by
  have h := atom0338_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0338Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0339 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0339 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0339 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0339_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177142415936640 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339Coded : CoefficientMerge.Poly := [(nat_lit 151, Int.ofNat (nat_lit 1))]
theorem atom0339Coded_decode : atom0339 = SparsePolynomial.decodeCubic 24 atom0339Coded := by decide +kernel
theorem atom0339Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) := by
  have h := atom0339_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0339Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0340 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0340 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0340 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0340_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167536677369600 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340Coded : CoefficientMerge.Poly := [(nat_lit 152, Int.ofNat (nat_lit 1))]
theorem atom0340Coded_decode : atom0340 = SparsePolynomial.decodeCubic 24 atom0340Coded := by decide +kernel
theorem atom0340Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded) := by
  have h := atom0340_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0340Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0341 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0341 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0341 = ((g 0) * (g 6) * (g 9)) := by
  norm_num [atom0341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0341_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171625729842468 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341Coded : CoefficientMerge.Poly := [(nat_lit 153, Int.ofNat (nat_lit 1))]
theorem atom0341Coded_decode : atom0341 = SparsePolynomial.decodeCubic 24 atom0341Coded := by decide +kernel
theorem atom0341Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) := by
  have h := atom0341_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0341Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0342 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0342 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0342 = ((g 0) * (g 6) * (g 10)) := by
  norm_num [atom0342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0342_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (174036270802284 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342Coded : CoefficientMerge.Poly := [(nat_lit 154, Int.ofNat (nat_lit 1))]
theorem atom0342Coded_decode : atom0342 = SparsePolynomial.decodeCubic 24 atom0342Coded := by decide +kernel
theorem atom0342Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) := by
  have h := atom0342_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0342Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0343 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0343 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0343 = ((g 0) * (g 6) * (g 11)) := by
  norm_num [atom0343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0343_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179411685885432 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343Coded : CoefficientMerge.Poly := [(nat_lit 155, Int.ofNat (nat_lit 1))]
theorem atom0343Coded_decode : atom0343 = SparsePolynomial.decodeCubic 24 atom0343Coded := by decide +kernel
theorem atom0343Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded) := by
  have h := atom0343_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0343Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0344 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0344 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0344 = ((g 0) * (g 6) * (g 12)) := by
  norm_num [atom0344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0344_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (227754227230992 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344Coded : CoefficientMerge.Poly := [(nat_lit 156, Int.ofNat (nat_lit 1))]
theorem atom0344Coded_decode : atom0344 = SparsePolynomial.decodeCubic 24 atom0344Coded := by decide +kernel
theorem atom0344Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) := by
  have h := atom0344_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0344Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0345 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0345 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0345 = ((g 0) * (g 6) * (g 13)) := by
  norm_num [atom0345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0345_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (212591933215200 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345Coded : CoefficientMerge.Poly := [(nat_lit 157, Int.ofNat (nat_lit 1))]
theorem atom0345Coded_decode : atom0345 = SparsePolynomial.decodeCubic 24 atom0345Coded := by decide +kernel
theorem atom0345Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded) := by
  have h := atom0345_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0345Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0346 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0346 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0346 = ((g 0) * (g 6) * (g 14)) := by
  norm_num [atom0346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0346_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (190999679270400 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346Coded : CoefficientMerge.Poly := [(nat_lit 158, Int.ofNat (nat_lit 1))]
theorem atom0346Coded_decode : atom0346 = SparsePolynomial.decodeCubic 24 atom0346Coded := by decide +kernel
theorem atom0346Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) := by
  have h := atom0346_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0346Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0347 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0347 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0347 = ((g 0) * (g 6) * (g 15)) := by
  norm_num [atom0347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0347_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (196547541523200 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347Coded : CoefficientMerge.Poly := [(nat_lit 159, Int.ofNat (nat_lit 1))]
theorem atom0347Coded_decode : atom0347 = SparsePolynomial.decodeCubic 24 atom0347Coded := by decide +kernel
theorem atom0347Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) := by
  have h := atom0347_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0347Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0348 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0348 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0348 = ((g 0) * (g 6) * (g 16)) := by
  norm_num [atom0348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0348_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (205051031337600 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348Coded : CoefficientMerge.Poly := [(nat_lit 160, Int.ofNat (nat_lit 1))]
theorem atom0348Coded_decode : atom0348 = SparsePolynomial.decodeCubic 24 atom0348Coded := by decide +kernel
theorem atom0348Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded) := by
  have h := atom0348_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0348Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0349 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0349 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0349 = ((g 0) * (g 6) * (g 17)) := by
  norm_num [atom0349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0349_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (211071336537600 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349Coded : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 1))]
theorem atom0349Coded_decode : atom0349 = SparsePolynomial.decodeCubic 24 atom0349Coded := by decide +kernel
theorem atom0349Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) := by
  have h := atom0349_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0349Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0350 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0350 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0350 = ((g 0) * (g 6) * (g 18)) := by
  norm_num [atom0350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0350_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229282538284800 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350Coded : CoefficientMerge.Poly := [(nat_lit 162, Int.ofNat (nat_lit 1))]
theorem atom0350Coded_decode : atom0350 = SparsePolynomial.decodeCubic 24 atom0350Coded := by decide +kernel
theorem atom0350Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded) := by
  have h := atom0350_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0350Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0351 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0351 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0351 = ((g 0) * (g 6) * (g 19)) := by
  norm_num [atom0351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0351_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (169646965488000 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351Coded : CoefficientMerge.Poly := [(nat_lit 163, Int.ofNat (nat_lit 1))]
theorem atom0351Coded_decode : atom0351 = SparsePolynomial.decodeCubic 24 atom0351Coded := by decide +kernel
theorem atom0351Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) := by
  have h := atom0351_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0351Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0352 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0352 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0352 = ((g 0) * (g 6) * (g 20)) := by
  norm_num [atom0352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0352_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134261101497600 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352Coded : CoefficientMerge.Poly := [(nat_lit 164, Int.ofNat (nat_lit 1))]
theorem atom0352Coded_decode : atom0352 = SparsePolynomial.decodeCubic 24 atom0352Coded := by decide +kernel
theorem atom0352Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) := by
  have h := atom0352_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0352Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0353 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0353 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0353 = ((g 0) * (g 6) * (g 21)) := by
  norm_num [atom0353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0353_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78771686716800 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353Coded : CoefficientMerge.Poly := [(nat_lit 165, Int.ofNat (nat_lit 1))]
theorem atom0353Coded_decode : atom0353 = SparsePolynomial.decodeCubic 24 atom0353Coded := by decide +kernel
theorem atom0353Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded) := by
  have h := atom0353_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0353Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0354 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0354 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0354 = ((g 0) * (g 6) * (g 22)) := by
  norm_num [atom0354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0354_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89313301526400 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354Coded : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 1))]
theorem atom0354Coded_decode : atom0354 = SparsePolynomial.decodeCubic 24 atom0354Coded := by decide +kernel
theorem atom0354Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) := by
  have h := atom0354_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0354Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0355 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0355 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0355 = ((g 0) * (g 6) * (g 23)) := by
  norm_num [atom0355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0355_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55414996560000 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355Coded : CoefficientMerge.Poly := [(nat_lit 167, Int.ofNat (nat_lit 1))]
theorem atom0355Coded_decode : atom0355 = SparsePolynomial.decodeCubic 24 atom0355Coded := by decide +kernel
theorem atom0355Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded) := by
  have h := atom0355_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0355Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0356 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0356 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0356 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0356_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (112758960652800 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356Coded : CoefficientMerge.Poly := [(nat_lit 175, Int.ofNat (nat_lit 1))]
theorem atom0356Coded_decode : atom0356 = SparsePolynomial.decodeCubic 24 atom0356Coded := by decide +kernel
theorem atom0356Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) := by
  have h := atom0356_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0356Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0357 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0357 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0357 = ((g 0) * (g 7) * (g 8)) := by
  norm_num [atom0357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0357_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207122327744640 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357Coded : CoefficientMerge.Poly := [(nat_lit 176, Int.ofNat (nat_lit 1))]
theorem atom0357Coded_decode : atom0357 = SparsePolynomial.decodeCubic 24 atom0357Coded := by decide +kernel
theorem atom0357Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) := by
  have h := atom0357_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0357Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0358 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0358 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0358 = ((g 0) * (g 7) * (g 9)) := by
  norm_num [atom0358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0358_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (186386366252196 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358Coded : CoefficientMerge.Poly := [(nat_lit 177, Int.ofNat (nat_lit 1))]
theorem atom0358Coded_decode : atom0358 = SparsePolynomial.decodeCubic 24 atom0358Coded := by decide +kernel
theorem atom0358Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded) := by
  have h := atom0358_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0358Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0359 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0359 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0359 = ((g 0) * (g 7) * (g 10)) := by
  norm_num [atom0359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0359_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (187147461941484 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359Coded : CoefficientMerge.Poly := [(nat_lit 178, Int.ofNat (nat_lit 1))]
theorem atom0359Coded_decode : atom0359 = SparsePolynomial.decodeCubic 24 atom0359Coded := by decide +kernel
theorem atom0359Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) := by
  have h := atom0359_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0359Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0360 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0360 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0360 = ((g 0) * (g 7) * (g 11)) := by
  norm_num [atom0360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0360_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193043804570232 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360Coded : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 1))]
theorem atom0360Coded_decode : atom0360 = SparsePolynomial.decodeCubic 24 atom0360Coded := by decide +kernel
theorem atom0360Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded) := by
  have h := atom0360_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0360Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0361 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0361 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0361 = ((g 0) * (g 7) * (g 12)) := by
  norm_num [atom0361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0361_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241907273461392 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361Coded : CoefficientMerge.Poly := [(nat_lit 180, Int.ofNat (nat_lit 1))]
theorem atom0361Coded_decode : atom0361 = SparsePolynomial.decodeCubic 24 atom0361Coded := by decide +kernel
theorem atom0361Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) := by
  have h := atom0361_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0361Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0362 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0362 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0362 = ((g 0) * (g 7) * (g 13)) := by
  norm_num [atom0362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0362_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226750295032800 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362Coded : CoefficientMerge.Poly := [(nat_lit 181, Int.ofNat (nat_lit 1))]
theorem atom0362Coded_decode : atom0362 = SparsePolynomial.decodeCubic 24 atom0362Coded := by decide +kernel
theorem atom0362Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) := by
  have h := atom0362_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0362Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0363 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0363 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0363 = ((g 0) * (g 7) * (g 14)) := by
  norm_num [atom0363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0363_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (205163356675200 : Int) atom0363) := by
  rw [SparsePolynomial.eval_scale, eval_atom0363]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0363Coded : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 1))]
theorem atom0363Coded_decode : atom0363 = SparsePolynomial.decodeCubic 24 atom0363Coded := by decide +kernel
theorem atom0363Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded) := by
  have h := atom0363_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0363Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0364 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0364 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0364 = ((g 0) * (g 7) * (g 15)) := by
  norm_num [atom0364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0364_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210716534515200 : Int) atom0364) := by
  rw [SparsePolynomial.eval_scale, eval_atom0364]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0364Coded : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 1))]
theorem atom0364Coded_decode : atom0364 = SparsePolynomial.decodeCubic 24 atom0364Coded := by decide +kernel
theorem atom0364Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) := by
  have h := atom0364_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0364Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0365 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0365 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0365 = ((g 0) * (g 7) * (g 16)) := by
  norm_num [atom0365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0365_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (219225339916800 : Int) atom0365) := by
  rw [SparsePolynomial.eval_scale, eval_atom0365]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0365Coded : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 1))]
theorem atom0365Coded_decode : atom0365 = SparsePolynomial.decodeCubic 24 atom0365Coded := by decide +kernel
theorem atom0365Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded) := by
  have h := atom0365_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0365Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0366 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0366 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0366 = ((g 0) * (g 7) * (g 17)) := by
  norm_num [atom0366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0366_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225250960704000 : Int) atom0366) := by
  rw [SparsePolynomial.eval_scale, eval_atom0366]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0366Coded : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 1))]
theorem atom0366Coded_decode : atom0366 = SparsePolynomial.decodeCubic 24 atom0366Coded := by decide +kernel
theorem atom0366Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) := by
  have h := atom0366_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0366Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0367 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0367 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0367 = ((g 0) * (g 7) * (g 18)) := by
  norm_num [atom0367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0367_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (243279070003200 : Int) atom0367) := by
  rw [SparsePolynomial.eval_scale, eval_atom0367]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0367Coded : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 1))]
theorem atom0367Coded_decode : atom0367 = SparsePolynomial.decodeCubic 24 atom0367Coded := by decide +kernel
theorem atom0367Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) := by
  have h := atom0367_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0367Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0368 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0368 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0368 = ((g 0) * (g 7) * (g 19)) := by
  norm_num [atom0368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0368_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183271996723200 : Int) atom0368) := by
  rw [SparsePolynomial.eval_scale, eval_atom0368]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0368Coded : CoefficientMerge.Poly := [(nat_lit 187, Int.ofNat (nat_lit 1))]
theorem atom0368Coded_decode : atom0368 = SparsePolynomial.decodeCubic 24 atom0368Coded := by decide +kernel
theorem atom0368Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded) := by
  have h := atom0368_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0368Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block006 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 162146671948800)), (nat_lit 87, Int.ofNat (nat_lit 165208450176000)), (nat_lit 88, Int.ofNat (nat_lit 168270228403200)), (nat_lit 89, Int.ofNat (nat_lit 171332006630400)), (nat_lit 90, Int.ofNat (nat_lit 194231556288000)), (nat_lit 91, Int.ofNat (nat_lit 121344224601600)), (nat_lit 92, Int.ofNat (nat_lit 98593511385600)), (nat_lit 93, Int.ofNat (nat_lit 28810482624000)), (nat_lit 94, Int.ofNat (nat_lit 38762067254400)), (nat_lit 95, Int.ofNat (nat_lit 4273732108800)), (nat_lit 100, Int.ofNat (nat_lit 72859948358400)), (nat_lit 101, Int.ofNat (nat_lit 134698516442424)), (nat_lit 102, Int.ofNat (nat_lit 136589328691200)), (nat_lit 103, Int.ofNat (nat_lit 140671699660800)), (nat_lit 104, Int.ofNat (nat_lit 144754070630400)), (nat_lit 105, Int.ofNat (nat_lit 148836441600000)), (nat_lit 106, Int.ofNat (nat_lit 152918812569600)), (nat_lit 107, Int.ofNat (nat_lit 161648510303808)), (nat_lit 108, Int.ofNat (nat_lit 215408764568448)), (nat_lit 109, Int.ofNat (nat_lit 196002793324800)), (nat_lit 110, Int.ofNat (nat_lit 169248296448000)), (nat_lit 111, Int.ofNat (nat_lit 173330667417600)), (nat_lit 112, Int.ofNat (nat_lit 177413038387200)), (nat_lit 113, Int.ofNat (nat_lit 182657267856000)), (nat_lit 114, Int.ofNat (nat_lit 204644791612800)), (nat_lit 115, Int.ofNat (nat_lit 139707504493200)), (nat_lit 116, Int.ofNat (nat_lit 106646444780400)), (nat_lit 117, Int.ofNat (nat_lit 47333592558000)), (nat_lit 118, Int.ofNat (nat_lit 57134810502000)), (nat_lit 119, Int.ofNat (nat_lit 22496108670000)), (nat_lit 125, Int.ofNat (nat_lit 82684750579200)), (nat_lit 126, Int.ofNat (nat_lit 148625354906424)), (nat_lit 127, Int.ofNat (nat_lit 148356622442424)), (nat_lit 128, Int.ofNat (nat_lit 154227963861576)), (nat_lit 129, Int.ofNat (nat_lit 158423328078444)), (nat_lit 130, Int.ofNat (nat_lit 158481345814308)), (nat_lit 131, Int.ofNat (nat_lit 165688356575808)), (nat_lit 132, Int.ofNat (nat_lit 220469203582848)), (nat_lit 133, Int.ofNat (nat_lit 202083825081600)), (nat_lit 134, Int.ofNat (nat_lit 176349920947200)), (nat_lit 135, Int.ofNat (nat_lit 181637319427200)), (nat_lit 136, Int.ofNat (nat_lit 189880345468800)), (nat_lit 137, Int.ofNat (nat_lit 195640186896000)), (nat_lit 138, Int.ofNat (nat_lit 216778750372800)), (nat_lit 139, Int.ofNat (nat_lit 158226313291200)), (nat_lit 140, Int.ofNat (nat_lit 130583902680000)), (nat_lit 141, Int.ofNat (nat_lit 75892956955200)), (nat_lit 142, Int.ofNat (nat_lit 81891667368000)), (nat_lit 143, Int.ofNat (nat_lit 53774798616000)), (nat_lit 150, Int.ofNat (nat_lit 100400811033600)), (nat_lit 151, Int.ofNat (nat_lit 177142415936640)), (nat_lit 152, Int.ofNat (nat_lit 167536677369600)), (nat_lit 153, Int.ofNat (nat_lit 171625729842468)), (nat_lit 154, Int.ofNat (nat_lit 174036270802284)), (nat_lit 155, Int.ofNat (nat_lit 179411685885432)), (nat_lit 156, Int.ofNat (nat_lit 227754227230992)), (nat_lit 157, Int.ofNat (nat_lit 212591933215200)), (nat_lit 158, Int.ofNat (nat_lit 190999679270400)), (nat_lit 159, Int.ofNat (nat_lit 196547541523200)), (nat_lit 160, Int.ofNat (nat_lit 205051031337600)), (nat_lit 161, Int.ofNat (nat_lit 211071336537600)), (nat_lit 162, Int.ofNat (nat_lit 229282538284800)), (nat_lit 163, Int.ofNat (nat_lit 169646965488000)), (nat_lit 164, Int.ofNat (nat_lit 134261101497600)), (nat_lit 165, Int.ofNat (nat_lit 78771686716800)), (nat_lit 166, Int.ofNat (nat_lit 89313301526400)), (nat_lit 167, Int.ofNat (nat_lit 55414996560000)), (nat_lit 175, Int.ofNat (nat_lit 112758960652800)), (nat_lit 176, Int.ofNat (nat_lit 207122327744640)), (nat_lit 177, Int.ofNat (nat_lit 186386366252196)), (nat_lit 178, Int.ofNat (nat_lit 187147461941484)), (nat_lit 179, Int.ofNat (nat_lit 193043804570232)), (nat_lit 180, Int.ofNat (nat_lit 241907273461392)), (nat_lit 181, Int.ofNat (nat_lit 226750295032800)), (nat_lit 182, Int.ofNat (nat_lit 205163356675200)), (nat_lit 183, Int.ofNat (nat_lit 210716534515200)), (nat_lit 184, Int.ofNat (nat_lit 219225339916800)), (nat_lit 185, Int.ofNat (nat_lit 225250960704000)), (nat_lit 186, Int.ofNat (nat_lit 243279070003200)), (nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
def block006_data_flat000 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 162146671948800))]
theorem block006_data_flat000_step : block006_data_flat000 = (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) := by decide +kernel
theorem block006_data_flat000_original : block006_data_flat000 = (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) := by
  rw [block006_data_flat000_step]
def block006_data_flat001 : CoefficientMerge.Poly := [(nat_lit 87, Int.ofNat (nat_lit 165208450176000))]
theorem block006_data_flat001_step : block006_data_flat001 = (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded) := by decide +kernel
theorem block006_data_flat001_original : block006_data_flat001 = (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded) := by
  rw [block006_data_flat001_step]
def block006_data_flat002 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 162146671948800)), (nat_lit 87, Int.ofNat (nat_lit 165208450176000))]
theorem block006_data_flat002_step : block006_data_flat002 = (CoefficientMerge.fastMerge block006_data_flat000 block006_data_flat001) := by decide +kernel
theorem block006_data_flat002_original : block006_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded)) := by
  rw [block006_data_flat002_step, block006_data_flat000_original, block006_data_flat001_original]
def block006_data_flat003 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 168270228403200))]
theorem block006_data_flat003_step : block006_data_flat003 = (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) := by decide +kernel
theorem block006_data_flat003_original : block006_data_flat003 = (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) := by
  rw [block006_data_flat003_step]
def block006_data_flat004 : CoefficientMerge.Poly := [(nat_lit 89, Int.ofNat (nat_lit 171332006630400))]
theorem block006_data_flat004_step : block006_data_flat004 = (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) := by decide +kernel
theorem block006_data_flat004_original : block006_data_flat004 = (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) := by
  rw [block006_data_flat004_step]
def block006_data_flat005 : CoefficientMerge.Poly := [(nat_lit 90, Int.ofNat (nat_lit 194231556288000))]
theorem block006_data_flat005_step : block006_data_flat005 = (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded) := by decide +kernel
theorem block006_data_flat005_original : block006_data_flat005 = (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded) := by
  rw [block006_data_flat005_step]
def block006_data_flat006 : CoefficientMerge.Poly := [(nat_lit 89, Int.ofNat (nat_lit 171332006630400)), (nat_lit 90, Int.ofNat (nat_lit 194231556288000))]
theorem block006_data_flat006_step : block006_data_flat006 = (CoefficientMerge.fastMerge block006_data_flat004 block006_data_flat005) := by decide +kernel
theorem block006_data_flat006_original : block006_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded)) := by
  rw [block006_data_flat006_step, block006_data_flat004_original, block006_data_flat005_original]
def block006_data_flat007 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 168270228403200)), (nat_lit 89, Int.ofNat (nat_lit 171332006630400)), (nat_lit 90, Int.ofNat (nat_lit 194231556288000))]
theorem block006_data_flat007_step : block006_data_flat007 = (CoefficientMerge.fastMerge block006_data_flat003 block006_data_flat006) := by decide +kernel
theorem block006_data_flat007_original : block006_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded))) := by
  rw [block006_data_flat007_step, block006_data_flat003_original, block006_data_flat006_original]
def block006_data_flat008 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 162146671948800)), (nat_lit 87, Int.ofNat (nat_lit 165208450176000)), (nat_lit 88, Int.ofNat (nat_lit 168270228403200)), (nat_lit 89, Int.ofNat (nat_lit 171332006630400)), (nat_lit 90, Int.ofNat (nat_lit 194231556288000))]
theorem block006_data_flat008_step : block006_data_flat008 = (CoefficientMerge.fastMerge block006_data_flat002 block006_data_flat007) := by decide +kernel
theorem block006_data_flat008_original : block006_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded)))) := by
  rw [block006_data_flat008_step, block006_data_flat002_original, block006_data_flat007_original]
def block006_data_flat009 : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 121344224601600))]
theorem block006_data_flat009_step : block006_data_flat009 = (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) := by decide +kernel
theorem block006_data_flat009_original : block006_data_flat009 = (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) := by
  rw [block006_data_flat009_step]
def block006_data_flat010 : CoefficientMerge.Poly := [(nat_lit 92, Int.ofNat (nat_lit 98593511385600))]
theorem block006_data_flat010_step : block006_data_flat010 = (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded) := by decide +kernel
theorem block006_data_flat010_original : block006_data_flat010 = (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded) := by
  rw [block006_data_flat010_step]
def block006_data_flat011 : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 121344224601600)), (nat_lit 92, Int.ofNat (nat_lit 98593511385600))]
theorem block006_data_flat011_step : block006_data_flat011 = (CoefficientMerge.fastMerge block006_data_flat009 block006_data_flat010) := by decide +kernel
theorem block006_data_flat011_original : block006_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded)) := by
  rw [block006_data_flat011_step, block006_data_flat009_original, block006_data_flat010_original]
def block006_data_flat012 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 28810482624000))]
theorem block006_data_flat012_step : block006_data_flat012 = (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) := by decide +kernel
theorem block006_data_flat012_original : block006_data_flat012 = (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) := by
  rw [block006_data_flat012_step]
def block006_data_flat013 : CoefficientMerge.Poly := [(nat_lit 94, Int.ofNat (nat_lit 38762067254400))]
theorem block006_data_flat013_step : block006_data_flat013 = (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) := by decide +kernel
theorem block006_data_flat013_original : block006_data_flat013 = (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) := by
  rw [block006_data_flat013_step]
def block006_data_flat014 : CoefficientMerge.Poly := [(nat_lit 95, Int.ofNat (nat_lit 4273732108800))]
theorem block006_data_flat014_step : block006_data_flat014 = (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded) := by decide +kernel
theorem block006_data_flat014_original : block006_data_flat014 = (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded) := by
  rw [block006_data_flat014_step]
def block006_data_flat015 : CoefficientMerge.Poly := [(nat_lit 94, Int.ofNat (nat_lit 38762067254400)), (nat_lit 95, Int.ofNat (nat_lit 4273732108800))]
theorem block006_data_flat015_step : block006_data_flat015 = (CoefficientMerge.fastMerge block006_data_flat013 block006_data_flat014) := by decide +kernel
theorem block006_data_flat015_original : block006_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded)) := by
  rw [block006_data_flat015_step, block006_data_flat013_original, block006_data_flat014_original]
def block006_data_flat016 : CoefficientMerge.Poly := [(nat_lit 93, Int.ofNat (nat_lit 28810482624000)), (nat_lit 94, Int.ofNat (nat_lit 38762067254400)), (nat_lit 95, Int.ofNat (nat_lit 4273732108800))]
theorem block006_data_flat016_step : block006_data_flat016 = (CoefficientMerge.fastMerge block006_data_flat012 block006_data_flat015) := by decide +kernel
theorem block006_data_flat016_original : block006_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded))) := by
  rw [block006_data_flat016_step, block006_data_flat012_original, block006_data_flat015_original]
def block006_data_flat017 : CoefficientMerge.Poly := [(nat_lit 91, Int.ofNat (nat_lit 121344224601600)), (nat_lit 92, Int.ofNat (nat_lit 98593511385600)), (nat_lit 93, Int.ofNat (nat_lit 28810482624000)), (nat_lit 94, Int.ofNat (nat_lit 38762067254400)), (nat_lit 95, Int.ofNat (nat_lit 4273732108800))]
theorem block006_data_flat017_step : block006_data_flat017 = (CoefficientMerge.fastMerge block006_data_flat011 block006_data_flat016) := by decide +kernel
theorem block006_data_flat017_original : block006_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded)))) := by
  rw [block006_data_flat017_step, block006_data_flat011_original, block006_data_flat016_original]
def block006_data_flat018 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 162146671948800)), (nat_lit 87, Int.ofNat (nat_lit 165208450176000)), (nat_lit 88, Int.ofNat (nat_lit 168270228403200)), (nat_lit 89, Int.ofNat (nat_lit 171332006630400)), (nat_lit 90, Int.ofNat (nat_lit 194231556288000)), (nat_lit 91, Int.ofNat (nat_lit 121344224601600)), (nat_lit 92, Int.ofNat (nat_lit 98593511385600)), (nat_lit 93, Int.ofNat (nat_lit 28810482624000)), (nat_lit 94, Int.ofNat (nat_lit 38762067254400)), (nat_lit 95, Int.ofNat (nat_lit 4273732108800))]
theorem block006_data_flat018_step : block006_data_flat018 = (CoefficientMerge.fastMerge block006_data_flat008 block006_data_flat017) := by decide +kernel
theorem block006_data_flat018_original : block006_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded))))) := by
  rw [block006_data_flat018_step, block006_data_flat008_original, block006_data_flat017_original]
def block006_data_flat019 : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 72859948358400))]
theorem block006_data_flat019_step : block006_data_flat019 = (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) := by decide +kernel
theorem block006_data_flat019_original : block006_data_flat019 = (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) := by
  rw [block006_data_flat019_step]
def block006_data_flat020 : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 134698516442424))]
theorem block006_data_flat020_step : block006_data_flat020 = (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded) := by decide +kernel
theorem block006_data_flat020_original : block006_data_flat020 = (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded) := by
  rw [block006_data_flat020_step]
def block006_data_flat021 : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 72859948358400)), (nat_lit 101, Int.ofNat (nat_lit 134698516442424))]
theorem block006_data_flat021_step : block006_data_flat021 = (CoefficientMerge.fastMerge block006_data_flat019 block006_data_flat020) := by decide +kernel
theorem block006_data_flat021_original : block006_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded)) := by
  rw [block006_data_flat021_step, block006_data_flat019_original, block006_data_flat020_original]
def block006_data_flat022 : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 136589328691200))]
theorem block006_data_flat022_step : block006_data_flat022 = (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) := by decide +kernel
theorem block006_data_flat022_original : block006_data_flat022 = (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) := by
  rw [block006_data_flat022_step]
def block006_data_flat023 : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 140671699660800))]
theorem block006_data_flat023_step : block006_data_flat023 = (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) := by decide +kernel
theorem block006_data_flat023_original : block006_data_flat023 = (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) := by
  rw [block006_data_flat023_step]
def block006_data_flat024 : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 144754070630400))]
theorem block006_data_flat024_step : block006_data_flat024 = (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded) := by decide +kernel
theorem block006_data_flat024_original : block006_data_flat024 = (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded) := by
  rw [block006_data_flat024_step]
def block006_data_flat025 : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 140671699660800)), (nat_lit 104, Int.ofNat (nat_lit 144754070630400))]
theorem block006_data_flat025_step : block006_data_flat025 = (CoefficientMerge.fastMerge block006_data_flat023 block006_data_flat024) := by decide +kernel
theorem block006_data_flat025_original : block006_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded)) := by
  rw [block006_data_flat025_step, block006_data_flat023_original, block006_data_flat024_original]
def block006_data_flat026 : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 136589328691200)), (nat_lit 103, Int.ofNat (nat_lit 140671699660800)), (nat_lit 104, Int.ofNat (nat_lit 144754070630400))]
theorem block006_data_flat026_step : block006_data_flat026 = (CoefficientMerge.fastMerge block006_data_flat022 block006_data_flat025) := by decide +kernel
theorem block006_data_flat026_original : block006_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded))) := by
  rw [block006_data_flat026_step, block006_data_flat022_original, block006_data_flat025_original]
def block006_data_flat027 : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 72859948358400)), (nat_lit 101, Int.ofNat (nat_lit 134698516442424)), (nat_lit 102, Int.ofNat (nat_lit 136589328691200)), (nat_lit 103, Int.ofNat (nat_lit 140671699660800)), (nat_lit 104, Int.ofNat (nat_lit 144754070630400))]
theorem block006_data_flat027_step : block006_data_flat027 = (CoefficientMerge.fastMerge block006_data_flat021 block006_data_flat026) := by decide +kernel
theorem block006_data_flat027_original : block006_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded)))) := by
  rw [block006_data_flat027_step, block006_data_flat021_original, block006_data_flat026_original]
def block006_data_flat028 : CoefficientMerge.Poly := [(nat_lit 105, Int.ofNat (nat_lit 148836441600000))]
theorem block006_data_flat028_step : block006_data_flat028 = (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) := by decide +kernel
theorem block006_data_flat028_original : block006_data_flat028 = (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) := by
  rw [block006_data_flat028_step]
def block006_data_flat029 : CoefficientMerge.Poly := [(nat_lit 106, Int.ofNat (nat_lit 152918812569600))]
theorem block006_data_flat029_step : block006_data_flat029 = (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded) := by decide +kernel
theorem block006_data_flat029_original : block006_data_flat029 = (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded) := by
  rw [block006_data_flat029_step]
def block006_data_flat030 : CoefficientMerge.Poly := [(nat_lit 105, Int.ofNat (nat_lit 148836441600000)), (nat_lit 106, Int.ofNat (nat_lit 152918812569600))]
theorem block006_data_flat030_step : block006_data_flat030 = (CoefficientMerge.fastMerge block006_data_flat028 block006_data_flat029) := by decide +kernel
theorem block006_data_flat030_original : block006_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded)) := by
  rw [block006_data_flat030_step, block006_data_flat028_original, block006_data_flat029_original]
def block006_data_flat031 : CoefficientMerge.Poly := [(nat_lit 107, Int.ofNat (nat_lit 161648510303808))]
theorem block006_data_flat031_step : block006_data_flat031 = (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) := by decide +kernel
theorem block006_data_flat031_original : block006_data_flat031 = (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) := by
  rw [block006_data_flat031_step]
def block006_data_flat032 : CoefficientMerge.Poly := [(nat_lit 108, Int.ofNat (nat_lit 215408764568448))]
theorem block006_data_flat032_step : block006_data_flat032 = (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) := by decide +kernel
theorem block006_data_flat032_original : block006_data_flat032 = (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) := by
  rw [block006_data_flat032_step]
def block006_data_flat033 : CoefficientMerge.Poly := [(nat_lit 109, Int.ofNat (nat_lit 196002793324800))]
theorem block006_data_flat033_step : block006_data_flat033 = (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded) := by decide +kernel
theorem block006_data_flat033_original : block006_data_flat033 = (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded) := by
  rw [block006_data_flat033_step]
def block006_data_flat034 : CoefficientMerge.Poly := [(nat_lit 108, Int.ofNat (nat_lit 215408764568448)), (nat_lit 109, Int.ofNat (nat_lit 196002793324800))]
theorem block006_data_flat034_step : block006_data_flat034 = (CoefficientMerge.fastMerge block006_data_flat032 block006_data_flat033) := by decide +kernel
theorem block006_data_flat034_original : block006_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded)) := by
  rw [block006_data_flat034_step, block006_data_flat032_original, block006_data_flat033_original]
def block006_data_flat035 : CoefficientMerge.Poly := [(nat_lit 107, Int.ofNat (nat_lit 161648510303808)), (nat_lit 108, Int.ofNat (nat_lit 215408764568448)), (nat_lit 109, Int.ofNat (nat_lit 196002793324800))]
theorem block006_data_flat035_step : block006_data_flat035 = (CoefficientMerge.fastMerge block006_data_flat031 block006_data_flat034) := by decide +kernel
theorem block006_data_flat035_original : block006_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded))) := by
  rw [block006_data_flat035_step, block006_data_flat031_original, block006_data_flat034_original]
def block006_data_flat036 : CoefficientMerge.Poly := [(nat_lit 105, Int.ofNat (nat_lit 148836441600000)), (nat_lit 106, Int.ofNat (nat_lit 152918812569600)), (nat_lit 107, Int.ofNat (nat_lit 161648510303808)), (nat_lit 108, Int.ofNat (nat_lit 215408764568448)), (nat_lit 109, Int.ofNat (nat_lit 196002793324800))]
theorem block006_data_flat036_step : block006_data_flat036 = (CoefficientMerge.fastMerge block006_data_flat030 block006_data_flat035) := by decide +kernel
theorem block006_data_flat036_original : block006_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded)))) := by
  rw [block006_data_flat036_step, block006_data_flat030_original, block006_data_flat035_original]
def block006_data_flat037 : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 72859948358400)), (nat_lit 101, Int.ofNat (nat_lit 134698516442424)), (nat_lit 102, Int.ofNat (nat_lit 136589328691200)), (nat_lit 103, Int.ofNat (nat_lit 140671699660800)), (nat_lit 104, Int.ofNat (nat_lit 144754070630400)), (nat_lit 105, Int.ofNat (nat_lit 148836441600000)), (nat_lit 106, Int.ofNat (nat_lit 152918812569600)), (nat_lit 107, Int.ofNat (nat_lit 161648510303808)), (nat_lit 108, Int.ofNat (nat_lit 215408764568448)), (nat_lit 109, Int.ofNat (nat_lit 196002793324800))]
theorem block006_data_flat037_step : block006_data_flat037 = (CoefficientMerge.fastMerge block006_data_flat027 block006_data_flat036) := by decide +kernel
theorem block006_data_flat037_original : block006_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded))))) := by
  rw [block006_data_flat037_step, block006_data_flat027_original, block006_data_flat036_original]
def block006_data_flat038 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 162146671948800)), (nat_lit 87, Int.ofNat (nat_lit 165208450176000)), (nat_lit 88, Int.ofNat (nat_lit 168270228403200)), (nat_lit 89, Int.ofNat (nat_lit 171332006630400)), (nat_lit 90, Int.ofNat (nat_lit 194231556288000)), (nat_lit 91, Int.ofNat (nat_lit 121344224601600)), (nat_lit 92, Int.ofNat (nat_lit 98593511385600)), (nat_lit 93, Int.ofNat (nat_lit 28810482624000)), (nat_lit 94, Int.ofNat (nat_lit 38762067254400)), (nat_lit 95, Int.ofNat (nat_lit 4273732108800)), (nat_lit 100, Int.ofNat (nat_lit 72859948358400)), (nat_lit 101, Int.ofNat (nat_lit 134698516442424)), (nat_lit 102, Int.ofNat (nat_lit 136589328691200)), (nat_lit 103, Int.ofNat (nat_lit 140671699660800)), (nat_lit 104, Int.ofNat (nat_lit 144754070630400)), (nat_lit 105, Int.ofNat (nat_lit 148836441600000)), (nat_lit 106, Int.ofNat (nat_lit 152918812569600)), (nat_lit 107, Int.ofNat (nat_lit 161648510303808)), (nat_lit 108, Int.ofNat (nat_lit 215408764568448)), (nat_lit 109, Int.ofNat (nat_lit 196002793324800))]
theorem block006_data_flat038_step : block006_data_flat038 = (CoefficientMerge.fastMerge block006_data_flat018 block006_data_flat037) := by decide +kernel
theorem block006_data_flat038_original : block006_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded)))))) := by
  rw [block006_data_flat038_step, block006_data_flat018_original, block006_data_flat037_original]
def block006_data_flat039 : CoefficientMerge.Poly := [(nat_lit 110, Int.ofNat (nat_lit 169248296448000))]
theorem block006_data_flat039_step : block006_data_flat039 = (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) := by decide +kernel
theorem block006_data_flat039_original : block006_data_flat039 = (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) := by
  rw [block006_data_flat039_step]
def block006_data_flat040 : CoefficientMerge.Poly := [(nat_lit 111, Int.ofNat (nat_lit 173330667417600))]
theorem block006_data_flat040_step : block006_data_flat040 = (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded) := by decide +kernel
theorem block006_data_flat040_original : block006_data_flat040 = (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded) := by
  rw [block006_data_flat040_step]
def block006_data_flat041 : CoefficientMerge.Poly := [(nat_lit 110, Int.ofNat (nat_lit 169248296448000)), (nat_lit 111, Int.ofNat (nat_lit 173330667417600))]
theorem block006_data_flat041_step : block006_data_flat041 = (CoefficientMerge.fastMerge block006_data_flat039 block006_data_flat040) := by decide +kernel
theorem block006_data_flat041_original : block006_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded)) := by
  rw [block006_data_flat041_step, block006_data_flat039_original, block006_data_flat040_original]
def block006_data_flat042 : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 177413038387200))]
theorem block006_data_flat042_step : block006_data_flat042 = (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) := by decide +kernel
theorem block006_data_flat042_original : block006_data_flat042 = (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) := by
  rw [block006_data_flat042_step]
def block006_data_flat043 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 182657267856000))]
theorem block006_data_flat043_step : block006_data_flat043 = (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) := by decide +kernel
theorem block006_data_flat043_original : block006_data_flat043 = (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) := by
  rw [block006_data_flat043_step]
def block006_data_flat044 : CoefficientMerge.Poly := [(nat_lit 114, Int.ofNat (nat_lit 204644791612800))]
theorem block006_data_flat044_step : block006_data_flat044 = (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded) := by decide +kernel
theorem block006_data_flat044_original : block006_data_flat044 = (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded) := by
  rw [block006_data_flat044_step]
def block006_data_flat045 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 182657267856000)), (nat_lit 114, Int.ofNat (nat_lit 204644791612800))]
theorem block006_data_flat045_step : block006_data_flat045 = (CoefficientMerge.fastMerge block006_data_flat043 block006_data_flat044) := by decide +kernel
theorem block006_data_flat045_original : block006_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded)) := by
  rw [block006_data_flat045_step, block006_data_flat043_original, block006_data_flat044_original]
def block006_data_flat046 : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 177413038387200)), (nat_lit 113, Int.ofNat (nat_lit 182657267856000)), (nat_lit 114, Int.ofNat (nat_lit 204644791612800))]
theorem block006_data_flat046_step : block006_data_flat046 = (CoefficientMerge.fastMerge block006_data_flat042 block006_data_flat045) := by decide +kernel
theorem block006_data_flat046_original : block006_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded))) := by
  rw [block006_data_flat046_step, block006_data_flat042_original, block006_data_flat045_original]
def block006_data_flat047 : CoefficientMerge.Poly := [(nat_lit 110, Int.ofNat (nat_lit 169248296448000)), (nat_lit 111, Int.ofNat (nat_lit 173330667417600)), (nat_lit 112, Int.ofNat (nat_lit 177413038387200)), (nat_lit 113, Int.ofNat (nat_lit 182657267856000)), (nat_lit 114, Int.ofNat (nat_lit 204644791612800))]
theorem block006_data_flat047_step : block006_data_flat047 = (CoefficientMerge.fastMerge block006_data_flat041 block006_data_flat046) := by decide +kernel
theorem block006_data_flat047_original : block006_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded)))) := by
  rw [block006_data_flat047_step, block006_data_flat041_original, block006_data_flat046_original]
def block006_data_flat048 : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 139707504493200))]
theorem block006_data_flat048_step : block006_data_flat048 = (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) := by decide +kernel
theorem block006_data_flat048_original : block006_data_flat048 = (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) := by
  rw [block006_data_flat048_step]
def block006_data_flat049 : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 106646444780400))]
theorem block006_data_flat049_step : block006_data_flat049 = (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded) := by decide +kernel
theorem block006_data_flat049_original : block006_data_flat049 = (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded) := by
  rw [block006_data_flat049_step]
def block006_data_flat050 : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 139707504493200)), (nat_lit 116, Int.ofNat (nat_lit 106646444780400))]
theorem block006_data_flat050_step : block006_data_flat050 = (CoefficientMerge.fastMerge block006_data_flat048 block006_data_flat049) := by decide +kernel
theorem block006_data_flat050_original : block006_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded)) := by
  rw [block006_data_flat050_step, block006_data_flat048_original, block006_data_flat049_original]
def block006_data_flat051 : CoefficientMerge.Poly := [(nat_lit 117, Int.ofNat (nat_lit 47333592558000))]
theorem block006_data_flat051_step : block006_data_flat051 = (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) := by decide +kernel
theorem block006_data_flat051_original : block006_data_flat051 = (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) := by
  rw [block006_data_flat051_step]
def block006_data_flat052 : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 57134810502000))]
theorem block006_data_flat052_step : block006_data_flat052 = (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) := by decide +kernel
theorem block006_data_flat052_original : block006_data_flat052 = (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) := by
  rw [block006_data_flat052_step]
def block006_data_flat053 : CoefficientMerge.Poly := [(nat_lit 119, Int.ofNat (nat_lit 22496108670000))]
theorem block006_data_flat053_step : block006_data_flat053 = (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded) := by decide +kernel
theorem block006_data_flat053_original : block006_data_flat053 = (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded) := by
  rw [block006_data_flat053_step]
def block006_data_flat054 : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 57134810502000)), (nat_lit 119, Int.ofNat (nat_lit 22496108670000))]
theorem block006_data_flat054_step : block006_data_flat054 = (CoefficientMerge.fastMerge block006_data_flat052 block006_data_flat053) := by decide +kernel
theorem block006_data_flat054_original : block006_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded)) := by
  rw [block006_data_flat054_step, block006_data_flat052_original, block006_data_flat053_original]
def block006_data_flat055 : CoefficientMerge.Poly := [(nat_lit 117, Int.ofNat (nat_lit 47333592558000)), (nat_lit 118, Int.ofNat (nat_lit 57134810502000)), (nat_lit 119, Int.ofNat (nat_lit 22496108670000))]
theorem block006_data_flat055_step : block006_data_flat055 = (CoefficientMerge.fastMerge block006_data_flat051 block006_data_flat054) := by decide +kernel
theorem block006_data_flat055_original : block006_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded))) := by
  rw [block006_data_flat055_step, block006_data_flat051_original, block006_data_flat054_original]
def block006_data_flat056 : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 139707504493200)), (nat_lit 116, Int.ofNat (nat_lit 106646444780400)), (nat_lit 117, Int.ofNat (nat_lit 47333592558000)), (nat_lit 118, Int.ofNat (nat_lit 57134810502000)), (nat_lit 119, Int.ofNat (nat_lit 22496108670000))]
theorem block006_data_flat056_step : block006_data_flat056 = (CoefficientMerge.fastMerge block006_data_flat050 block006_data_flat055) := by decide +kernel
theorem block006_data_flat056_original : block006_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded)))) := by
  rw [block006_data_flat056_step, block006_data_flat050_original, block006_data_flat055_original]
def block006_data_flat057 : CoefficientMerge.Poly := [(nat_lit 110, Int.ofNat (nat_lit 169248296448000)), (nat_lit 111, Int.ofNat (nat_lit 173330667417600)), (nat_lit 112, Int.ofNat (nat_lit 177413038387200)), (nat_lit 113, Int.ofNat (nat_lit 182657267856000)), (nat_lit 114, Int.ofNat (nat_lit 204644791612800)), (nat_lit 115, Int.ofNat (nat_lit 139707504493200)), (nat_lit 116, Int.ofNat (nat_lit 106646444780400)), (nat_lit 117, Int.ofNat (nat_lit 47333592558000)), (nat_lit 118, Int.ofNat (nat_lit 57134810502000)), (nat_lit 119, Int.ofNat (nat_lit 22496108670000))]
theorem block006_data_flat057_step : block006_data_flat057 = (CoefficientMerge.fastMerge block006_data_flat047 block006_data_flat056) := by decide +kernel
theorem block006_data_flat057_original : block006_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded))))) := by
  rw [block006_data_flat057_step, block006_data_flat047_original, block006_data_flat056_original]
def block006_data_flat058 : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 82684750579200))]
theorem block006_data_flat058_step : block006_data_flat058 = (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) := by decide +kernel
theorem block006_data_flat058_original : block006_data_flat058 = (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) := by
  rw [block006_data_flat058_step]
def block006_data_flat059 : CoefficientMerge.Poly := [(nat_lit 126, Int.ofNat (nat_lit 148625354906424))]
theorem block006_data_flat059_step : block006_data_flat059 = (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded) := by decide +kernel
theorem block006_data_flat059_original : block006_data_flat059 = (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded) := by
  rw [block006_data_flat059_step]
def block006_data_flat060 : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 82684750579200)), (nat_lit 126, Int.ofNat (nat_lit 148625354906424))]
theorem block006_data_flat060_step : block006_data_flat060 = (CoefficientMerge.fastMerge block006_data_flat058 block006_data_flat059) := by decide +kernel
theorem block006_data_flat060_original : block006_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded)) := by
  rw [block006_data_flat060_step, block006_data_flat058_original, block006_data_flat059_original]
def block006_data_flat061 : CoefficientMerge.Poly := [(nat_lit 127, Int.ofNat (nat_lit 148356622442424))]
theorem block006_data_flat061_step : block006_data_flat061 = (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) := by decide +kernel
theorem block006_data_flat061_original : block006_data_flat061 = (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) := by
  rw [block006_data_flat061_step]
def block006_data_flat062 : CoefficientMerge.Poly := [(nat_lit 128, Int.ofNat (nat_lit 154227963861576))]
theorem block006_data_flat062_step : block006_data_flat062 = (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) := by decide +kernel
theorem block006_data_flat062_original : block006_data_flat062 = (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) := by
  rw [block006_data_flat062_step]
def block006_data_flat063 : CoefficientMerge.Poly := [(nat_lit 129, Int.ofNat (nat_lit 158423328078444))]
theorem block006_data_flat063_step : block006_data_flat063 = (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded) := by decide +kernel
theorem block006_data_flat063_original : block006_data_flat063 = (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded) := by
  rw [block006_data_flat063_step]
def block006_data_flat064 : CoefficientMerge.Poly := [(nat_lit 128, Int.ofNat (nat_lit 154227963861576)), (nat_lit 129, Int.ofNat (nat_lit 158423328078444))]
theorem block006_data_flat064_step : block006_data_flat064 = (CoefficientMerge.fastMerge block006_data_flat062 block006_data_flat063) := by decide +kernel
theorem block006_data_flat064_original : block006_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded)) := by
  rw [block006_data_flat064_step, block006_data_flat062_original, block006_data_flat063_original]
def block006_data_flat065 : CoefficientMerge.Poly := [(nat_lit 127, Int.ofNat (nat_lit 148356622442424)), (nat_lit 128, Int.ofNat (nat_lit 154227963861576)), (nat_lit 129, Int.ofNat (nat_lit 158423328078444))]
theorem block006_data_flat065_step : block006_data_flat065 = (CoefficientMerge.fastMerge block006_data_flat061 block006_data_flat064) := by decide +kernel
theorem block006_data_flat065_original : block006_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded))) := by
  rw [block006_data_flat065_step, block006_data_flat061_original, block006_data_flat064_original]
def block006_data_flat066 : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 82684750579200)), (nat_lit 126, Int.ofNat (nat_lit 148625354906424)), (nat_lit 127, Int.ofNat (nat_lit 148356622442424)), (nat_lit 128, Int.ofNat (nat_lit 154227963861576)), (nat_lit 129, Int.ofNat (nat_lit 158423328078444))]
theorem block006_data_flat066_step : block006_data_flat066 = (CoefficientMerge.fastMerge block006_data_flat060 block006_data_flat065) := by decide +kernel
theorem block006_data_flat066_original : block006_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded)))) := by
  rw [block006_data_flat066_step, block006_data_flat060_original, block006_data_flat065_original]
def block006_data_flat067 : CoefficientMerge.Poly := [(nat_lit 130, Int.ofNat (nat_lit 158481345814308))]
theorem block006_data_flat067_step : block006_data_flat067 = (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) := by decide +kernel
theorem block006_data_flat067_original : block006_data_flat067 = (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) := by
  rw [block006_data_flat067_step]
def block006_data_flat068 : CoefficientMerge.Poly := [(nat_lit 131, Int.ofNat (nat_lit 165688356575808))]
theorem block006_data_flat068_step : block006_data_flat068 = (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded) := by decide +kernel
theorem block006_data_flat068_original : block006_data_flat068 = (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded) := by
  rw [block006_data_flat068_step]
def block006_data_flat069 : CoefficientMerge.Poly := [(nat_lit 130, Int.ofNat (nat_lit 158481345814308)), (nat_lit 131, Int.ofNat (nat_lit 165688356575808))]
theorem block006_data_flat069_step : block006_data_flat069 = (CoefficientMerge.fastMerge block006_data_flat067 block006_data_flat068) := by decide +kernel
theorem block006_data_flat069_original : block006_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded)) := by
  rw [block006_data_flat069_step, block006_data_flat067_original, block006_data_flat068_original]
def block006_data_flat070 : CoefficientMerge.Poly := [(nat_lit 132, Int.ofNat (nat_lit 220469203582848))]
theorem block006_data_flat070_step : block006_data_flat070 = (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) := by decide +kernel
theorem block006_data_flat070_original : block006_data_flat070 = (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) := by
  rw [block006_data_flat070_step]
def block006_data_flat071 : CoefficientMerge.Poly := [(nat_lit 133, Int.ofNat (nat_lit 202083825081600))]
theorem block006_data_flat071_step : block006_data_flat071 = (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) := by decide +kernel
theorem block006_data_flat071_original : block006_data_flat071 = (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) := by
  rw [block006_data_flat071_step]
def block006_data_flat072 : CoefficientMerge.Poly := [(nat_lit 134, Int.ofNat (nat_lit 176349920947200))]
theorem block006_data_flat072_step : block006_data_flat072 = (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded) := by decide +kernel
theorem block006_data_flat072_original : block006_data_flat072 = (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded) := by
  rw [block006_data_flat072_step]
def block006_data_flat073 : CoefficientMerge.Poly := [(nat_lit 133, Int.ofNat (nat_lit 202083825081600)), (nat_lit 134, Int.ofNat (nat_lit 176349920947200))]
theorem block006_data_flat073_step : block006_data_flat073 = (CoefficientMerge.fastMerge block006_data_flat071 block006_data_flat072) := by decide +kernel
theorem block006_data_flat073_original : block006_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded)) := by
  rw [block006_data_flat073_step, block006_data_flat071_original, block006_data_flat072_original]
def block006_data_flat074 : CoefficientMerge.Poly := [(nat_lit 132, Int.ofNat (nat_lit 220469203582848)), (nat_lit 133, Int.ofNat (nat_lit 202083825081600)), (nat_lit 134, Int.ofNat (nat_lit 176349920947200))]
theorem block006_data_flat074_step : block006_data_flat074 = (CoefficientMerge.fastMerge block006_data_flat070 block006_data_flat073) := by decide +kernel
theorem block006_data_flat074_original : block006_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded))) := by
  rw [block006_data_flat074_step, block006_data_flat070_original, block006_data_flat073_original]
def block006_data_flat075 : CoefficientMerge.Poly := [(nat_lit 130, Int.ofNat (nat_lit 158481345814308)), (nat_lit 131, Int.ofNat (nat_lit 165688356575808)), (nat_lit 132, Int.ofNat (nat_lit 220469203582848)), (nat_lit 133, Int.ofNat (nat_lit 202083825081600)), (nat_lit 134, Int.ofNat (nat_lit 176349920947200))]
theorem block006_data_flat075_step : block006_data_flat075 = (CoefficientMerge.fastMerge block006_data_flat069 block006_data_flat074) := by decide +kernel
theorem block006_data_flat075_original : block006_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded)))) := by
  rw [block006_data_flat075_step, block006_data_flat069_original, block006_data_flat074_original]
def block006_data_flat076 : CoefficientMerge.Poly := [(nat_lit 125, Int.ofNat (nat_lit 82684750579200)), (nat_lit 126, Int.ofNat (nat_lit 148625354906424)), (nat_lit 127, Int.ofNat (nat_lit 148356622442424)), (nat_lit 128, Int.ofNat (nat_lit 154227963861576)), (nat_lit 129, Int.ofNat (nat_lit 158423328078444)), (nat_lit 130, Int.ofNat (nat_lit 158481345814308)), (nat_lit 131, Int.ofNat (nat_lit 165688356575808)), (nat_lit 132, Int.ofNat (nat_lit 220469203582848)), (nat_lit 133, Int.ofNat (nat_lit 202083825081600)), (nat_lit 134, Int.ofNat (nat_lit 176349920947200))]
theorem block006_data_flat076_step : block006_data_flat076 = (CoefficientMerge.fastMerge block006_data_flat066 block006_data_flat075) := by decide +kernel
theorem block006_data_flat076_original : block006_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded))))) := by
  rw [block006_data_flat076_step, block006_data_flat066_original, block006_data_flat075_original]
def block006_data_flat077 : CoefficientMerge.Poly := [(nat_lit 110, Int.ofNat (nat_lit 169248296448000)), (nat_lit 111, Int.ofNat (nat_lit 173330667417600)), (nat_lit 112, Int.ofNat (nat_lit 177413038387200)), (nat_lit 113, Int.ofNat (nat_lit 182657267856000)), (nat_lit 114, Int.ofNat (nat_lit 204644791612800)), (nat_lit 115, Int.ofNat (nat_lit 139707504493200)), (nat_lit 116, Int.ofNat (nat_lit 106646444780400)), (nat_lit 117, Int.ofNat (nat_lit 47333592558000)), (nat_lit 118, Int.ofNat (nat_lit 57134810502000)), (nat_lit 119, Int.ofNat (nat_lit 22496108670000)), (nat_lit 125, Int.ofNat (nat_lit 82684750579200)), (nat_lit 126, Int.ofNat (nat_lit 148625354906424)), (nat_lit 127, Int.ofNat (nat_lit 148356622442424)), (nat_lit 128, Int.ofNat (nat_lit 154227963861576)), (nat_lit 129, Int.ofNat (nat_lit 158423328078444)), (nat_lit 130, Int.ofNat (nat_lit 158481345814308)), (nat_lit 131, Int.ofNat (nat_lit 165688356575808)), (nat_lit 132, Int.ofNat (nat_lit 220469203582848)), (nat_lit 133, Int.ofNat (nat_lit 202083825081600)), (nat_lit 134, Int.ofNat (nat_lit 176349920947200))]
theorem block006_data_flat077_step : block006_data_flat077 = (CoefficientMerge.fastMerge block006_data_flat057 block006_data_flat076) := by decide +kernel
theorem block006_data_flat077_original : block006_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded)))))) := by
  rw [block006_data_flat077_step, block006_data_flat057_original, block006_data_flat076_original]
def block006_data_flat078 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 162146671948800)), (nat_lit 87, Int.ofNat (nat_lit 165208450176000)), (nat_lit 88, Int.ofNat (nat_lit 168270228403200)), (nat_lit 89, Int.ofNat (nat_lit 171332006630400)), (nat_lit 90, Int.ofNat (nat_lit 194231556288000)), (nat_lit 91, Int.ofNat (nat_lit 121344224601600)), (nat_lit 92, Int.ofNat (nat_lit 98593511385600)), (nat_lit 93, Int.ofNat (nat_lit 28810482624000)), (nat_lit 94, Int.ofNat (nat_lit 38762067254400)), (nat_lit 95, Int.ofNat (nat_lit 4273732108800)), (nat_lit 100, Int.ofNat (nat_lit 72859948358400)), (nat_lit 101, Int.ofNat (nat_lit 134698516442424)), (nat_lit 102, Int.ofNat (nat_lit 136589328691200)), (nat_lit 103, Int.ofNat (nat_lit 140671699660800)), (nat_lit 104, Int.ofNat (nat_lit 144754070630400)), (nat_lit 105, Int.ofNat (nat_lit 148836441600000)), (nat_lit 106, Int.ofNat (nat_lit 152918812569600)), (nat_lit 107, Int.ofNat (nat_lit 161648510303808)), (nat_lit 108, Int.ofNat (nat_lit 215408764568448)), (nat_lit 109, Int.ofNat (nat_lit 196002793324800)), (nat_lit 110, Int.ofNat (nat_lit 169248296448000)), (nat_lit 111, Int.ofNat (nat_lit 173330667417600)), (nat_lit 112, Int.ofNat (nat_lit 177413038387200)), (nat_lit 113, Int.ofNat (nat_lit 182657267856000)), (nat_lit 114, Int.ofNat (nat_lit 204644791612800)), (nat_lit 115, Int.ofNat (nat_lit 139707504493200)), (nat_lit 116, Int.ofNat (nat_lit 106646444780400)), (nat_lit 117, Int.ofNat (nat_lit 47333592558000)), (nat_lit 118, Int.ofNat (nat_lit 57134810502000)), (nat_lit 119, Int.ofNat (nat_lit 22496108670000)), (nat_lit 125, Int.ofNat (nat_lit 82684750579200)), (nat_lit 126, Int.ofNat (nat_lit 148625354906424)), (nat_lit 127, Int.ofNat (nat_lit 148356622442424)), (nat_lit 128, Int.ofNat (nat_lit 154227963861576)), (nat_lit 129, Int.ofNat (nat_lit 158423328078444)), (nat_lit 130, Int.ofNat (nat_lit 158481345814308)), (nat_lit 131, Int.ofNat (nat_lit 165688356575808)), (nat_lit 132, Int.ofNat (nat_lit 220469203582848)), (nat_lit 133, Int.ofNat (nat_lit 202083825081600)), (nat_lit 134, Int.ofNat (nat_lit 176349920947200))]
theorem block006_data_flat078_step : block006_data_flat078 = (CoefficientMerge.fastMerge block006_data_flat038 block006_data_flat077) := by decide +kernel
theorem block006_data_flat078_original : block006_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded))))))) := by
  rw [block006_data_flat078_step, block006_data_flat038_original, block006_data_flat077_original]
def block006_data_flat079 : CoefficientMerge.Poly := [(nat_lit 135, Int.ofNat (nat_lit 181637319427200))]
theorem block006_data_flat079_step : block006_data_flat079 = (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) := by decide +kernel
theorem block006_data_flat079_original : block006_data_flat079 = (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) := by
  rw [block006_data_flat079_step]
def block006_data_flat080 : CoefficientMerge.Poly := [(nat_lit 136, Int.ofNat (nat_lit 189880345468800))]
theorem block006_data_flat080_step : block006_data_flat080 = (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded) := by decide +kernel
theorem block006_data_flat080_original : block006_data_flat080 = (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded) := by
  rw [block006_data_flat080_step]
def block006_data_flat081 : CoefficientMerge.Poly := [(nat_lit 135, Int.ofNat (nat_lit 181637319427200)), (nat_lit 136, Int.ofNat (nat_lit 189880345468800))]
theorem block006_data_flat081_step : block006_data_flat081 = (CoefficientMerge.fastMerge block006_data_flat079 block006_data_flat080) := by decide +kernel
theorem block006_data_flat081_original : block006_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded)) := by
  rw [block006_data_flat081_step, block006_data_flat079_original, block006_data_flat080_original]
def block006_data_flat082 : CoefficientMerge.Poly := [(nat_lit 137, Int.ofNat (nat_lit 195640186896000))]
theorem block006_data_flat082_step : block006_data_flat082 = (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) := by decide +kernel
theorem block006_data_flat082_original : block006_data_flat082 = (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) := by
  rw [block006_data_flat082_step]
def block006_data_flat083 : CoefficientMerge.Poly := [(nat_lit 138, Int.ofNat (nat_lit 216778750372800))]
theorem block006_data_flat083_step : block006_data_flat083 = (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) := by decide +kernel
theorem block006_data_flat083_original : block006_data_flat083 = (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) := by
  rw [block006_data_flat083_step]
def block006_data_flat084 : CoefficientMerge.Poly := [(nat_lit 139, Int.ofNat (nat_lit 158226313291200))]
theorem block006_data_flat084_step : block006_data_flat084 = (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded) := by decide +kernel
theorem block006_data_flat084_original : block006_data_flat084 = (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded) := by
  rw [block006_data_flat084_step]
def block006_data_flat085 : CoefficientMerge.Poly := [(nat_lit 138, Int.ofNat (nat_lit 216778750372800)), (nat_lit 139, Int.ofNat (nat_lit 158226313291200))]
theorem block006_data_flat085_step : block006_data_flat085 = (CoefficientMerge.fastMerge block006_data_flat083 block006_data_flat084) := by decide +kernel
theorem block006_data_flat085_original : block006_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded)) := by
  rw [block006_data_flat085_step, block006_data_flat083_original, block006_data_flat084_original]
def block006_data_flat086 : CoefficientMerge.Poly := [(nat_lit 137, Int.ofNat (nat_lit 195640186896000)), (nat_lit 138, Int.ofNat (nat_lit 216778750372800)), (nat_lit 139, Int.ofNat (nat_lit 158226313291200))]
theorem block006_data_flat086_step : block006_data_flat086 = (CoefficientMerge.fastMerge block006_data_flat082 block006_data_flat085) := by decide +kernel
theorem block006_data_flat086_original : block006_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded))) := by
  rw [block006_data_flat086_step, block006_data_flat082_original, block006_data_flat085_original]
def block006_data_flat087 : CoefficientMerge.Poly := [(nat_lit 135, Int.ofNat (nat_lit 181637319427200)), (nat_lit 136, Int.ofNat (nat_lit 189880345468800)), (nat_lit 137, Int.ofNat (nat_lit 195640186896000)), (nat_lit 138, Int.ofNat (nat_lit 216778750372800)), (nat_lit 139, Int.ofNat (nat_lit 158226313291200))]
theorem block006_data_flat087_step : block006_data_flat087 = (CoefficientMerge.fastMerge block006_data_flat081 block006_data_flat086) := by decide +kernel
theorem block006_data_flat087_original : block006_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded)))) := by
  rw [block006_data_flat087_step, block006_data_flat081_original, block006_data_flat086_original]
def block006_data_flat088 : CoefficientMerge.Poly := [(nat_lit 140, Int.ofNat (nat_lit 130583902680000))]
theorem block006_data_flat088_step : block006_data_flat088 = (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) := by decide +kernel
theorem block006_data_flat088_original : block006_data_flat088 = (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) := by
  rw [block006_data_flat088_step]
def block006_data_flat089 : CoefficientMerge.Poly := [(nat_lit 141, Int.ofNat (nat_lit 75892956955200))]
theorem block006_data_flat089_step : block006_data_flat089 = (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded) := by decide +kernel
theorem block006_data_flat089_original : block006_data_flat089 = (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded) := by
  rw [block006_data_flat089_step]
def block006_data_flat090 : CoefficientMerge.Poly := [(nat_lit 140, Int.ofNat (nat_lit 130583902680000)), (nat_lit 141, Int.ofNat (nat_lit 75892956955200))]
theorem block006_data_flat090_step : block006_data_flat090 = (CoefficientMerge.fastMerge block006_data_flat088 block006_data_flat089) := by decide +kernel
theorem block006_data_flat090_original : block006_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded)) := by
  rw [block006_data_flat090_step, block006_data_flat088_original, block006_data_flat089_original]
def block006_data_flat091 : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 81891667368000))]
theorem block006_data_flat091_step : block006_data_flat091 = (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) := by decide +kernel
theorem block006_data_flat091_original : block006_data_flat091 = (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) := by
  rw [block006_data_flat091_step]
def block006_data_flat092 : CoefficientMerge.Poly := [(nat_lit 143, Int.ofNat (nat_lit 53774798616000))]
theorem block006_data_flat092_step : block006_data_flat092 = (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) := by decide +kernel
theorem block006_data_flat092_original : block006_data_flat092 = (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) := by
  rw [block006_data_flat092_step]
def block006_data_flat093 : CoefficientMerge.Poly := [(nat_lit 150, Int.ofNat (nat_lit 100400811033600))]
theorem block006_data_flat093_step : block006_data_flat093 = (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded) := by decide +kernel
theorem block006_data_flat093_original : block006_data_flat093 = (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded) := by
  rw [block006_data_flat093_step]
def block006_data_flat094 : CoefficientMerge.Poly := [(nat_lit 143, Int.ofNat (nat_lit 53774798616000)), (nat_lit 150, Int.ofNat (nat_lit 100400811033600))]
theorem block006_data_flat094_step : block006_data_flat094 = (CoefficientMerge.fastMerge block006_data_flat092 block006_data_flat093) := by decide +kernel
theorem block006_data_flat094_original : block006_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded)) := by
  rw [block006_data_flat094_step, block006_data_flat092_original, block006_data_flat093_original]
def block006_data_flat095 : CoefficientMerge.Poly := [(nat_lit 142, Int.ofNat (nat_lit 81891667368000)), (nat_lit 143, Int.ofNat (nat_lit 53774798616000)), (nat_lit 150, Int.ofNat (nat_lit 100400811033600))]
theorem block006_data_flat095_step : block006_data_flat095 = (CoefficientMerge.fastMerge block006_data_flat091 block006_data_flat094) := by decide +kernel
theorem block006_data_flat095_original : block006_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded))) := by
  rw [block006_data_flat095_step, block006_data_flat091_original, block006_data_flat094_original]
def block006_data_flat096 : CoefficientMerge.Poly := [(nat_lit 140, Int.ofNat (nat_lit 130583902680000)), (nat_lit 141, Int.ofNat (nat_lit 75892956955200)), (nat_lit 142, Int.ofNat (nat_lit 81891667368000)), (nat_lit 143, Int.ofNat (nat_lit 53774798616000)), (nat_lit 150, Int.ofNat (nat_lit 100400811033600))]
theorem block006_data_flat096_step : block006_data_flat096 = (CoefficientMerge.fastMerge block006_data_flat090 block006_data_flat095) := by decide +kernel
theorem block006_data_flat096_original : block006_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded)))) := by
  rw [block006_data_flat096_step, block006_data_flat090_original, block006_data_flat095_original]
def block006_data_flat097 : CoefficientMerge.Poly := [(nat_lit 135, Int.ofNat (nat_lit 181637319427200)), (nat_lit 136, Int.ofNat (nat_lit 189880345468800)), (nat_lit 137, Int.ofNat (nat_lit 195640186896000)), (nat_lit 138, Int.ofNat (nat_lit 216778750372800)), (nat_lit 139, Int.ofNat (nat_lit 158226313291200)), (nat_lit 140, Int.ofNat (nat_lit 130583902680000)), (nat_lit 141, Int.ofNat (nat_lit 75892956955200)), (nat_lit 142, Int.ofNat (nat_lit 81891667368000)), (nat_lit 143, Int.ofNat (nat_lit 53774798616000)), (nat_lit 150, Int.ofNat (nat_lit 100400811033600))]
theorem block006_data_flat097_step : block006_data_flat097 = (CoefficientMerge.fastMerge block006_data_flat087 block006_data_flat096) := by decide +kernel
theorem block006_data_flat097_original : block006_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded))))) := by
  rw [block006_data_flat097_step, block006_data_flat087_original, block006_data_flat096_original]
def block006_data_flat098 : CoefficientMerge.Poly := [(nat_lit 151, Int.ofNat (nat_lit 177142415936640))]
theorem block006_data_flat098_step : block006_data_flat098 = (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) := by decide +kernel
theorem block006_data_flat098_original : block006_data_flat098 = (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) := by
  rw [block006_data_flat098_step]
def block006_data_flat099 : CoefficientMerge.Poly := [(nat_lit 152, Int.ofNat (nat_lit 167536677369600))]
theorem block006_data_flat099_step : block006_data_flat099 = (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded) := by decide +kernel
theorem block006_data_flat099_original : block006_data_flat099 = (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded) := by
  rw [block006_data_flat099_step]
def block006_data_flat100 : CoefficientMerge.Poly := [(nat_lit 151, Int.ofNat (nat_lit 177142415936640)), (nat_lit 152, Int.ofNat (nat_lit 167536677369600))]
theorem block006_data_flat100_step : block006_data_flat100 = (CoefficientMerge.fastMerge block006_data_flat098 block006_data_flat099) := by decide +kernel
theorem block006_data_flat100_original : block006_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded)) := by
  rw [block006_data_flat100_step, block006_data_flat098_original, block006_data_flat099_original]
def block006_data_flat101 : CoefficientMerge.Poly := [(nat_lit 153, Int.ofNat (nat_lit 171625729842468))]
theorem block006_data_flat101_step : block006_data_flat101 = (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) := by decide +kernel
theorem block006_data_flat101_original : block006_data_flat101 = (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) := by
  rw [block006_data_flat101_step]
def block006_data_flat102 : CoefficientMerge.Poly := [(nat_lit 154, Int.ofNat (nat_lit 174036270802284))]
theorem block006_data_flat102_step : block006_data_flat102 = (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) := by decide +kernel
theorem block006_data_flat102_original : block006_data_flat102 = (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) := by
  rw [block006_data_flat102_step]
def block006_data_flat103 : CoefficientMerge.Poly := [(nat_lit 155, Int.ofNat (nat_lit 179411685885432))]
theorem block006_data_flat103_step : block006_data_flat103 = (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded) := by decide +kernel
theorem block006_data_flat103_original : block006_data_flat103 = (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded) := by
  rw [block006_data_flat103_step]
def block006_data_flat104 : CoefficientMerge.Poly := [(nat_lit 154, Int.ofNat (nat_lit 174036270802284)), (nat_lit 155, Int.ofNat (nat_lit 179411685885432))]
theorem block006_data_flat104_step : block006_data_flat104 = (CoefficientMerge.fastMerge block006_data_flat102 block006_data_flat103) := by decide +kernel
theorem block006_data_flat104_original : block006_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded)) := by
  rw [block006_data_flat104_step, block006_data_flat102_original, block006_data_flat103_original]
def block006_data_flat105 : CoefficientMerge.Poly := [(nat_lit 153, Int.ofNat (nat_lit 171625729842468)), (nat_lit 154, Int.ofNat (nat_lit 174036270802284)), (nat_lit 155, Int.ofNat (nat_lit 179411685885432))]
theorem block006_data_flat105_step : block006_data_flat105 = (CoefficientMerge.fastMerge block006_data_flat101 block006_data_flat104) := by decide +kernel
theorem block006_data_flat105_original : block006_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded))) := by
  rw [block006_data_flat105_step, block006_data_flat101_original, block006_data_flat104_original]
def block006_data_flat106 : CoefficientMerge.Poly := [(nat_lit 151, Int.ofNat (nat_lit 177142415936640)), (nat_lit 152, Int.ofNat (nat_lit 167536677369600)), (nat_lit 153, Int.ofNat (nat_lit 171625729842468)), (nat_lit 154, Int.ofNat (nat_lit 174036270802284)), (nat_lit 155, Int.ofNat (nat_lit 179411685885432))]
theorem block006_data_flat106_step : block006_data_flat106 = (CoefficientMerge.fastMerge block006_data_flat100 block006_data_flat105) := by decide +kernel
theorem block006_data_flat106_original : block006_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded)))) := by
  rw [block006_data_flat106_step, block006_data_flat100_original, block006_data_flat105_original]
def block006_data_flat107 : CoefficientMerge.Poly := [(nat_lit 156, Int.ofNat (nat_lit 227754227230992))]
theorem block006_data_flat107_step : block006_data_flat107 = (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) := by decide +kernel
theorem block006_data_flat107_original : block006_data_flat107 = (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) := by
  rw [block006_data_flat107_step]
def block006_data_flat108 : CoefficientMerge.Poly := [(nat_lit 157, Int.ofNat (nat_lit 212591933215200))]
theorem block006_data_flat108_step : block006_data_flat108 = (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded) := by decide +kernel
theorem block006_data_flat108_original : block006_data_flat108 = (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded) := by
  rw [block006_data_flat108_step]
def block006_data_flat109 : CoefficientMerge.Poly := [(nat_lit 156, Int.ofNat (nat_lit 227754227230992)), (nat_lit 157, Int.ofNat (nat_lit 212591933215200))]
theorem block006_data_flat109_step : block006_data_flat109 = (CoefficientMerge.fastMerge block006_data_flat107 block006_data_flat108) := by decide +kernel
theorem block006_data_flat109_original : block006_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded)) := by
  rw [block006_data_flat109_step, block006_data_flat107_original, block006_data_flat108_original]
def block006_data_flat110 : CoefficientMerge.Poly := [(nat_lit 158, Int.ofNat (nat_lit 190999679270400))]
theorem block006_data_flat110_step : block006_data_flat110 = (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) := by decide +kernel
theorem block006_data_flat110_original : block006_data_flat110 = (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) := by
  rw [block006_data_flat110_step]
def block006_data_flat111 : CoefficientMerge.Poly := [(nat_lit 159, Int.ofNat (nat_lit 196547541523200))]
theorem block006_data_flat111_step : block006_data_flat111 = (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) := by decide +kernel
theorem block006_data_flat111_original : block006_data_flat111 = (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) := by
  rw [block006_data_flat111_step]
def block006_data_flat112 : CoefficientMerge.Poly := [(nat_lit 160, Int.ofNat (nat_lit 205051031337600))]
theorem block006_data_flat112_step : block006_data_flat112 = (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded) := by decide +kernel
theorem block006_data_flat112_original : block006_data_flat112 = (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded) := by
  rw [block006_data_flat112_step]
def block006_data_flat113 : CoefficientMerge.Poly := [(nat_lit 159, Int.ofNat (nat_lit 196547541523200)), (nat_lit 160, Int.ofNat (nat_lit 205051031337600))]
theorem block006_data_flat113_step : block006_data_flat113 = (CoefficientMerge.fastMerge block006_data_flat111 block006_data_flat112) := by decide +kernel
theorem block006_data_flat113_original : block006_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded)) := by
  rw [block006_data_flat113_step, block006_data_flat111_original, block006_data_flat112_original]
def block006_data_flat114 : CoefficientMerge.Poly := [(nat_lit 158, Int.ofNat (nat_lit 190999679270400)), (nat_lit 159, Int.ofNat (nat_lit 196547541523200)), (nat_lit 160, Int.ofNat (nat_lit 205051031337600))]
theorem block006_data_flat114_step : block006_data_flat114 = (CoefficientMerge.fastMerge block006_data_flat110 block006_data_flat113) := by decide +kernel
theorem block006_data_flat114_original : block006_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded))) := by
  rw [block006_data_flat114_step, block006_data_flat110_original, block006_data_flat113_original]
def block006_data_flat115 : CoefficientMerge.Poly := [(nat_lit 156, Int.ofNat (nat_lit 227754227230992)), (nat_lit 157, Int.ofNat (nat_lit 212591933215200)), (nat_lit 158, Int.ofNat (nat_lit 190999679270400)), (nat_lit 159, Int.ofNat (nat_lit 196547541523200)), (nat_lit 160, Int.ofNat (nat_lit 205051031337600))]
theorem block006_data_flat115_step : block006_data_flat115 = (CoefficientMerge.fastMerge block006_data_flat109 block006_data_flat114) := by decide +kernel
theorem block006_data_flat115_original : block006_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded)))) := by
  rw [block006_data_flat115_step, block006_data_flat109_original, block006_data_flat114_original]
def block006_data_flat116 : CoefficientMerge.Poly := [(nat_lit 151, Int.ofNat (nat_lit 177142415936640)), (nat_lit 152, Int.ofNat (nat_lit 167536677369600)), (nat_lit 153, Int.ofNat (nat_lit 171625729842468)), (nat_lit 154, Int.ofNat (nat_lit 174036270802284)), (nat_lit 155, Int.ofNat (nat_lit 179411685885432)), (nat_lit 156, Int.ofNat (nat_lit 227754227230992)), (nat_lit 157, Int.ofNat (nat_lit 212591933215200)), (nat_lit 158, Int.ofNat (nat_lit 190999679270400)), (nat_lit 159, Int.ofNat (nat_lit 196547541523200)), (nat_lit 160, Int.ofNat (nat_lit 205051031337600))]
theorem block006_data_flat116_step : block006_data_flat116 = (CoefficientMerge.fastMerge block006_data_flat106 block006_data_flat115) := by decide +kernel
theorem block006_data_flat116_original : block006_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded))))) := by
  rw [block006_data_flat116_step, block006_data_flat106_original, block006_data_flat115_original]
def block006_data_flat117 : CoefficientMerge.Poly := [(nat_lit 135, Int.ofNat (nat_lit 181637319427200)), (nat_lit 136, Int.ofNat (nat_lit 189880345468800)), (nat_lit 137, Int.ofNat (nat_lit 195640186896000)), (nat_lit 138, Int.ofNat (nat_lit 216778750372800)), (nat_lit 139, Int.ofNat (nat_lit 158226313291200)), (nat_lit 140, Int.ofNat (nat_lit 130583902680000)), (nat_lit 141, Int.ofNat (nat_lit 75892956955200)), (nat_lit 142, Int.ofNat (nat_lit 81891667368000)), (nat_lit 143, Int.ofNat (nat_lit 53774798616000)), (nat_lit 150, Int.ofNat (nat_lit 100400811033600)), (nat_lit 151, Int.ofNat (nat_lit 177142415936640)), (nat_lit 152, Int.ofNat (nat_lit 167536677369600)), (nat_lit 153, Int.ofNat (nat_lit 171625729842468)), (nat_lit 154, Int.ofNat (nat_lit 174036270802284)), (nat_lit 155, Int.ofNat (nat_lit 179411685885432)), (nat_lit 156, Int.ofNat (nat_lit 227754227230992)), (nat_lit 157, Int.ofNat (nat_lit 212591933215200)), (nat_lit 158, Int.ofNat (nat_lit 190999679270400)), (nat_lit 159, Int.ofNat (nat_lit 196547541523200)), (nat_lit 160, Int.ofNat (nat_lit 205051031337600))]
theorem block006_data_flat117_step : block006_data_flat117 = (CoefficientMerge.fastMerge block006_data_flat097 block006_data_flat116) := by decide +kernel
theorem block006_data_flat117_original : block006_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded)))))) := by
  rw [block006_data_flat117_step, block006_data_flat097_original, block006_data_flat116_original]
def block006_data_flat118 : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 211071336537600))]
theorem block006_data_flat118_step : block006_data_flat118 = (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) := by decide +kernel
theorem block006_data_flat118_original : block006_data_flat118 = (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) := by
  rw [block006_data_flat118_step]
def block006_data_flat119 : CoefficientMerge.Poly := [(nat_lit 162, Int.ofNat (nat_lit 229282538284800))]
theorem block006_data_flat119_step : block006_data_flat119 = (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded) := by decide +kernel
theorem block006_data_flat119_original : block006_data_flat119 = (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded) := by
  rw [block006_data_flat119_step]
def block006_data_flat120 : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 211071336537600)), (nat_lit 162, Int.ofNat (nat_lit 229282538284800))]
theorem block006_data_flat120_step : block006_data_flat120 = (CoefficientMerge.fastMerge block006_data_flat118 block006_data_flat119) := by decide +kernel
theorem block006_data_flat120_original : block006_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded)) := by
  rw [block006_data_flat120_step, block006_data_flat118_original, block006_data_flat119_original]
def block006_data_flat121 : CoefficientMerge.Poly := [(nat_lit 163, Int.ofNat (nat_lit 169646965488000))]
theorem block006_data_flat121_step : block006_data_flat121 = (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) := by decide +kernel
theorem block006_data_flat121_original : block006_data_flat121 = (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) := by
  rw [block006_data_flat121_step]
def block006_data_flat122 : CoefficientMerge.Poly := [(nat_lit 164, Int.ofNat (nat_lit 134261101497600))]
theorem block006_data_flat122_step : block006_data_flat122 = (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) := by decide +kernel
theorem block006_data_flat122_original : block006_data_flat122 = (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) := by
  rw [block006_data_flat122_step]
def block006_data_flat123 : CoefficientMerge.Poly := [(nat_lit 165, Int.ofNat (nat_lit 78771686716800))]
theorem block006_data_flat123_step : block006_data_flat123 = (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded) := by decide +kernel
theorem block006_data_flat123_original : block006_data_flat123 = (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded) := by
  rw [block006_data_flat123_step]
def block006_data_flat124 : CoefficientMerge.Poly := [(nat_lit 164, Int.ofNat (nat_lit 134261101497600)), (nat_lit 165, Int.ofNat (nat_lit 78771686716800))]
theorem block006_data_flat124_step : block006_data_flat124 = (CoefficientMerge.fastMerge block006_data_flat122 block006_data_flat123) := by decide +kernel
theorem block006_data_flat124_original : block006_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded)) := by
  rw [block006_data_flat124_step, block006_data_flat122_original, block006_data_flat123_original]
def block006_data_flat125 : CoefficientMerge.Poly := [(nat_lit 163, Int.ofNat (nat_lit 169646965488000)), (nat_lit 164, Int.ofNat (nat_lit 134261101497600)), (nat_lit 165, Int.ofNat (nat_lit 78771686716800))]
theorem block006_data_flat125_step : block006_data_flat125 = (CoefficientMerge.fastMerge block006_data_flat121 block006_data_flat124) := by decide +kernel
theorem block006_data_flat125_original : block006_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded))) := by
  rw [block006_data_flat125_step, block006_data_flat121_original, block006_data_flat124_original]
def block006_data_flat126 : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 211071336537600)), (nat_lit 162, Int.ofNat (nat_lit 229282538284800)), (nat_lit 163, Int.ofNat (nat_lit 169646965488000)), (nat_lit 164, Int.ofNat (nat_lit 134261101497600)), (nat_lit 165, Int.ofNat (nat_lit 78771686716800))]
theorem block006_data_flat126_step : block006_data_flat126 = (CoefficientMerge.fastMerge block006_data_flat120 block006_data_flat125) := by decide +kernel
theorem block006_data_flat126_original : block006_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded)))) := by
  rw [block006_data_flat126_step, block006_data_flat120_original, block006_data_flat125_original]
def block006_data_flat127 : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 89313301526400))]
theorem block006_data_flat127_step : block006_data_flat127 = (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) := by decide +kernel
theorem block006_data_flat127_original : block006_data_flat127 = (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) := by
  rw [block006_data_flat127_step]
def block006_data_flat128 : CoefficientMerge.Poly := [(nat_lit 167, Int.ofNat (nat_lit 55414996560000))]
theorem block006_data_flat128_step : block006_data_flat128 = (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded) := by decide +kernel
theorem block006_data_flat128_original : block006_data_flat128 = (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded) := by
  rw [block006_data_flat128_step]
def block006_data_flat129 : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 89313301526400)), (nat_lit 167, Int.ofNat (nat_lit 55414996560000))]
theorem block006_data_flat129_step : block006_data_flat129 = (CoefficientMerge.fastMerge block006_data_flat127 block006_data_flat128) := by decide +kernel
theorem block006_data_flat129_original : block006_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded)) := by
  rw [block006_data_flat129_step, block006_data_flat127_original, block006_data_flat128_original]
def block006_data_flat130 : CoefficientMerge.Poly := [(nat_lit 175, Int.ofNat (nat_lit 112758960652800))]
theorem block006_data_flat130_step : block006_data_flat130 = (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) := by decide +kernel
theorem block006_data_flat130_original : block006_data_flat130 = (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) := by
  rw [block006_data_flat130_step]
def block006_data_flat131 : CoefficientMerge.Poly := [(nat_lit 176, Int.ofNat (nat_lit 207122327744640))]
theorem block006_data_flat131_step : block006_data_flat131 = (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) := by decide +kernel
theorem block006_data_flat131_original : block006_data_flat131 = (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) := by
  rw [block006_data_flat131_step]
def block006_data_flat132 : CoefficientMerge.Poly := [(nat_lit 177, Int.ofNat (nat_lit 186386366252196))]
theorem block006_data_flat132_step : block006_data_flat132 = (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded) := by decide +kernel
theorem block006_data_flat132_original : block006_data_flat132 = (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded) := by
  rw [block006_data_flat132_step]
def block006_data_flat133 : CoefficientMerge.Poly := [(nat_lit 176, Int.ofNat (nat_lit 207122327744640)), (nat_lit 177, Int.ofNat (nat_lit 186386366252196))]
theorem block006_data_flat133_step : block006_data_flat133 = (CoefficientMerge.fastMerge block006_data_flat131 block006_data_flat132) := by decide +kernel
theorem block006_data_flat133_original : block006_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded)) := by
  rw [block006_data_flat133_step, block006_data_flat131_original, block006_data_flat132_original]
def block006_data_flat134 : CoefficientMerge.Poly := [(nat_lit 175, Int.ofNat (nat_lit 112758960652800)), (nat_lit 176, Int.ofNat (nat_lit 207122327744640)), (nat_lit 177, Int.ofNat (nat_lit 186386366252196))]
theorem block006_data_flat134_step : block006_data_flat134 = (CoefficientMerge.fastMerge block006_data_flat130 block006_data_flat133) := by decide +kernel
theorem block006_data_flat134_original : block006_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded))) := by
  rw [block006_data_flat134_step, block006_data_flat130_original, block006_data_flat133_original]
def block006_data_flat135 : CoefficientMerge.Poly := [(nat_lit 166, Int.ofNat (nat_lit 89313301526400)), (nat_lit 167, Int.ofNat (nat_lit 55414996560000)), (nat_lit 175, Int.ofNat (nat_lit 112758960652800)), (nat_lit 176, Int.ofNat (nat_lit 207122327744640)), (nat_lit 177, Int.ofNat (nat_lit 186386366252196))]
theorem block006_data_flat135_step : block006_data_flat135 = (CoefficientMerge.fastMerge block006_data_flat129 block006_data_flat134) := by decide +kernel
theorem block006_data_flat135_original : block006_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded)))) := by
  rw [block006_data_flat135_step, block006_data_flat129_original, block006_data_flat134_original]
def block006_data_flat136 : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 211071336537600)), (nat_lit 162, Int.ofNat (nat_lit 229282538284800)), (nat_lit 163, Int.ofNat (nat_lit 169646965488000)), (nat_lit 164, Int.ofNat (nat_lit 134261101497600)), (nat_lit 165, Int.ofNat (nat_lit 78771686716800)), (nat_lit 166, Int.ofNat (nat_lit 89313301526400)), (nat_lit 167, Int.ofNat (nat_lit 55414996560000)), (nat_lit 175, Int.ofNat (nat_lit 112758960652800)), (nat_lit 176, Int.ofNat (nat_lit 207122327744640)), (nat_lit 177, Int.ofNat (nat_lit 186386366252196))]
theorem block006_data_flat136_step : block006_data_flat136 = (CoefficientMerge.fastMerge block006_data_flat126 block006_data_flat135) := by decide +kernel
theorem block006_data_flat136_original : block006_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded))))) := by
  rw [block006_data_flat136_step, block006_data_flat126_original, block006_data_flat135_original]
def block006_data_flat137 : CoefficientMerge.Poly := [(nat_lit 178, Int.ofNat (nat_lit 187147461941484))]
theorem block006_data_flat137_step : block006_data_flat137 = (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) := by decide +kernel
theorem block006_data_flat137_original : block006_data_flat137 = (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) := by
  rw [block006_data_flat137_step]
def block006_data_flat138 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 193043804570232))]
theorem block006_data_flat138_step : block006_data_flat138 = (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded) := by decide +kernel
theorem block006_data_flat138_original : block006_data_flat138 = (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded) := by
  rw [block006_data_flat138_step]
def block006_data_flat139 : CoefficientMerge.Poly := [(nat_lit 178, Int.ofNat (nat_lit 187147461941484)), (nat_lit 179, Int.ofNat (nat_lit 193043804570232))]
theorem block006_data_flat139_step : block006_data_flat139 = (CoefficientMerge.fastMerge block006_data_flat137 block006_data_flat138) := by decide +kernel
theorem block006_data_flat139_original : block006_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded)) := by
  rw [block006_data_flat139_step, block006_data_flat137_original, block006_data_flat138_original]
def block006_data_flat140 : CoefficientMerge.Poly := [(nat_lit 180, Int.ofNat (nat_lit 241907273461392))]
theorem block006_data_flat140_step : block006_data_flat140 = (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) := by decide +kernel
theorem block006_data_flat140_original : block006_data_flat140 = (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) := by
  rw [block006_data_flat140_step]
def block006_data_flat141 : CoefficientMerge.Poly := [(nat_lit 181, Int.ofNat (nat_lit 226750295032800))]
theorem block006_data_flat141_step : block006_data_flat141 = (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) := by decide +kernel
theorem block006_data_flat141_original : block006_data_flat141 = (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) := by
  rw [block006_data_flat141_step]
def block006_data_flat142 : CoefficientMerge.Poly := [(nat_lit 182, Int.ofNat (nat_lit 205163356675200))]
theorem block006_data_flat142_step : block006_data_flat142 = (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded) := by decide +kernel
theorem block006_data_flat142_original : block006_data_flat142 = (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded) := by
  rw [block006_data_flat142_step]
def block006_data_flat143 : CoefficientMerge.Poly := [(nat_lit 181, Int.ofNat (nat_lit 226750295032800)), (nat_lit 182, Int.ofNat (nat_lit 205163356675200))]
theorem block006_data_flat143_step : block006_data_flat143 = (CoefficientMerge.fastMerge block006_data_flat141 block006_data_flat142) := by decide +kernel
theorem block006_data_flat143_original : block006_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded)) := by
  rw [block006_data_flat143_step, block006_data_flat141_original, block006_data_flat142_original]
def block006_data_flat144 : CoefficientMerge.Poly := [(nat_lit 180, Int.ofNat (nat_lit 241907273461392)), (nat_lit 181, Int.ofNat (nat_lit 226750295032800)), (nat_lit 182, Int.ofNat (nat_lit 205163356675200))]
theorem block006_data_flat144_step : block006_data_flat144 = (CoefficientMerge.fastMerge block006_data_flat140 block006_data_flat143) := by decide +kernel
theorem block006_data_flat144_original : block006_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded))) := by
  rw [block006_data_flat144_step, block006_data_flat140_original, block006_data_flat143_original]
def block006_data_flat145 : CoefficientMerge.Poly := [(nat_lit 178, Int.ofNat (nat_lit 187147461941484)), (nat_lit 179, Int.ofNat (nat_lit 193043804570232)), (nat_lit 180, Int.ofNat (nat_lit 241907273461392)), (nat_lit 181, Int.ofNat (nat_lit 226750295032800)), (nat_lit 182, Int.ofNat (nat_lit 205163356675200))]
theorem block006_data_flat145_step : block006_data_flat145 = (CoefficientMerge.fastMerge block006_data_flat139 block006_data_flat144) := by decide +kernel
theorem block006_data_flat145_original : block006_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded)))) := by
  rw [block006_data_flat145_step, block006_data_flat139_original, block006_data_flat144_original]
def block006_data_flat146 : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 210716534515200))]
theorem block006_data_flat146_step : block006_data_flat146 = (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) := by decide +kernel
theorem block006_data_flat146_original : block006_data_flat146 = (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) := by
  rw [block006_data_flat146_step]
def block006_data_flat147 : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 219225339916800))]
theorem block006_data_flat147_step : block006_data_flat147 = (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded) := by decide +kernel
theorem block006_data_flat147_original : block006_data_flat147 = (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded) := by
  rw [block006_data_flat147_step]
def block006_data_flat148 : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 210716534515200)), (nat_lit 184, Int.ofNat (nat_lit 219225339916800))]
theorem block006_data_flat148_step : block006_data_flat148 = (CoefficientMerge.fastMerge block006_data_flat146 block006_data_flat147) := by decide +kernel
theorem block006_data_flat148_original : block006_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded)) := by
  rw [block006_data_flat148_step, block006_data_flat146_original, block006_data_flat147_original]
def block006_data_flat149 : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 225250960704000))]
theorem block006_data_flat149_step : block006_data_flat149 = (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) := by decide +kernel
theorem block006_data_flat149_original : block006_data_flat149 = (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) := by
  rw [block006_data_flat149_step]
def block006_data_flat150 : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 243279070003200))]
theorem block006_data_flat150_step : block006_data_flat150 = (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) := by decide +kernel
theorem block006_data_flat150_original : block006_data_flat150 = (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) := by
  rw [block006_data_flat150_step]
def block006_data_flat151 : CoefficientMerge.Poly := [(nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
theorem block006_data_flat151_step : block006_data_flat151 = (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded) := by decide +kernel
theorem block006_data_flat151_original : block006_data_flat151 = (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded) := by
  rw [block006_data_flat151_step]
def block006_data_flat152 : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 243279070003200)), (nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
theorem block006_data_flat152_step : block006_data_flat152 = (CoefficientMerge.fastMerge block006_data_flat150 block006_data_flat151) := by decide +kernel
theorem block006_data_flat152_original : block006_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded)) := by
  rw [block006_data_flat152_step, block006_data_flat150_original, block006_data_flat151_original]
def block006_data_flat153 : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 225250960704000)), (nat_lit 186, Int.ofNat (nat_lit 243279070003200)), (nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
theorem block006_data_flat153_step : block006_data_flat153 = (CoefficientMerge.fastMerge block006_data_flat149 block006_data_flat152) := by decide +kernel
theorem block006_data_flat153_original : block006_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded))) := by
  rw [block006_data_flat153_step, block006_data_flat149_original, block006_data_flat152_original]
def block006_data_flat154 : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 210716534515200)), (nat_lit 184, Int.ofNat (nat_lit 219225339916800)), (nat_lit 185, Int.ofNat (nat_lit 225250960704000)), (nat_lit 186, Int.ofNat (nat_lit 243279070003200)), (nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
theorem block006_data_flat154_step : block006_data_flat154 = (CoefficientMerge.fastMerge block006_data_flat148 block006_data_flat153) := by decide +kernel
theorem block006_data_flat154_original : block006_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded)))) := by
  rw [block006_data_flat154_step, block006_data_flat148_original, block006_data_flat153_original]
def block006_data_flat155 : CoefficientMerge.Poly := [(nat_lit 178, Int.ofNat (nat_lit 187147461941484)), (nat_lit 179, Int.ofNat (nat_lit 193043804570232)), (nat_lit 180, Int.ofNat (nat_lit 241907273461392)), (nat_lit 181, Int.ofNat (nat_lit 226750295032800)), (nat_lit 182, Int.ofNat (nat_lit 205163356675200)), (nat_lit 183, Int.ofNat (nat_lit 210716534515200)), (nat_lit 184, Int.ofNat (nat_lit 219225339916800)), (nat_lit 185, Int.ofNat (nat_lit 225250960704000)), (nat_lit 186, Int.ofNat (nat_lit 243279070003200)), (nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
theorem block006_data_flat155_step : block006_data_flat155 = (CoefficientMerge.fastMerge block006_data_flat145 block006_data_flat154) := by decide +kernel
theorem block006_data_flat155_original : block006_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded))))) := by
  rw [block006_data_flat155_step, block006_data_flat145_original, block006_data_flat154_original]
def block006_data_flat156 : CoefficientMerge.Poly := [(nat_lit 161, Int.ofNat (nat_lit 211071336537600)), (nat_lit 162, Int.ofNat (nat_lit 229282538284800)), (nat_lit 163, Int.ofNat (nat_lit 169646965488000)), (nat_lit 164, Int.ofNat (nat_lit 134261101497600)), (nat_lit 165, Int.ofNat (nat_lit 78771686716800)), (nat_lit 166, Int.ofNat (nat_lit 89313301526400)), (nat_lit 167, Int.ofNat (nat_lit 55414996560000)), (nat_lit 175, Int.ofNat (nat_lit 112758960652800)), (nat_lit 176, Int.ofNat (nat_lit 207122327744640)), (nat_lit 177, Int.ofNat (nat_lit 186386366252196)), (nat_lit 178, Int.ofNat (nat_lit 187147461941484)), (nat_lit 179, Int.ofNat (nat_lit 193043804570232)), (nat_lit 180, Int.ofNat (nat_lit 241907273461392)), (nat_lit 181, Int.ofNat (nat_lit 226750295032800)), (nat_lit 182, Int.ofNat (nat_lit 205163356675200)), (nat_lit 183, Int.ofNat (nat_lit 210716534515200)), (nat_lit 184, Int.ofNat (nat_lit 219225339916800)), (nat_lit 185, Int.ofNat (nat_lit 225250960704000)), (nat_lit 186, Int.ofNat (nat_lit 243279070003200)), (nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
theorem block006_data_flat156_step : block006_data_flat156 = (CoefficientMerge.fastMerge block006_data_flat136 block006_data_flat155) := by decide +kernel
theorem block006_data_flat156_original : block006_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded)))))) := by
  rw [block006_data_flat156_step, block006_data_flat136_original, block006_data_flat155_original]
def block006_data_flat157 : CoefficientMerge.Poly := [(nat_lit 135, Int.ofNat (nat_lit 181637319427200)), (nat_lit 136, Int.ofNat (nat_lit 189880345468800)), (nat_lit 137, Int.ofNat (nat_lit 195640186896000)), (nat_lit 138, Int.ofNat (nat_lit 216778750372800)), (nat_lit 139, Int.ofNat (nat_lit 158226313291200)), (nat_lit 140, Int.ofNat (nat_lit 130583902680000)), (nat_lit 141, Int.ofNat (nat_lit 75892956955200)), (nat_lit 142, Int.ofNat (nat_lit 81891667368000)), (nat_lit 143, Int.ofNat (nat_lit 53774798616000)), (nat_lit 150, Int.ofNat (nat_lit 100400811033600)), (nat_lit 151, Int.ofNat (nat_lit 177142415936640)), (nat_lit 152, Int.ofNat (nat_lit 167536677369600)), (nat_lit 153, Int.ofNat (nat_lit 171625729842468)), (nat_lit 154, Int.ofNat (nat_lit 174036270802284)), (nat_lit 155, Int.ofNat (nat_lit 179411685885432)), (nat_lit 156, Int.ofNat (nat_lit 227754227230992)), (nat_lit 157, Int.ofNat (nat_lit 212591933215200)), (nat_lit 158, Int.ofNat (nat_lit 190999679270400)), (nat_lit 159, Int.ofNat (nat_lit 196547541523200)), (nat_lit 160, Int.ofNat (nat_lit 205051031337600)), (nat_lit 161, Int.ofNat (nat_lit 211071336537600)), (nat_lit 162, Int.ofNat (nat_lit 229282538284800)), (nat_lit 163, Int.ofNat (nat_lit 169646965488000)), (nat_lit 164, Int.ofNat (nat_lit 134261101497600)), (nat_lit 165, Int.ofNat (nat_lit 78771686716800)), (nat_lit 166, Int.ofNat (nat_lit 89313301526400)), (nat_lit 167, Int.ofNat (nat_lit 55414996560000)), (nat_lit 175, Int.ofNat (nat_lit 112758960652800)), (nat_lit 176, Int.ofNat (nat_lit 207122327744640)), (nat_lit 177, Int.ofNat (nat_lit 186386366252196)), (nat_lit 178, Int.ofNat (nat_lit 187147461941484)), (nat_lit 179, Int.ofNat (nat_lit 193043804570232)), (nat_lit 180, Int.ofNat (nat_lit 241907273461392)), (nat_lit 181, Int.ofNat (nat_lit 226750295032800)), (nat_lit 182, Int.ofNat (nat_lit 205163356675200)), (nat_lit 183, Int.ofNat (nat_lit 210716534515200)), (nat_lit 184, Int.ofNat (nat_lit 219225339916800)), (nat_lit 185, Int.ofNat (nat_lit 225250960704000)), (nat_lit 186, Int.ofNat (nat_lit 243279070003200)), (nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
theorem block006_data_flat157_step : block006_data_flat157 = (CoefficientMerge.fastMerge block006_data_flat117 block006_data_flat156) := by decide +kernel
theorem block006_data_flat157_original : block006_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded))))))) := by
  rw [block006_data_flat157_step, block006_data_flat117_original, block006_data_flat156_original]
def block006_data_flat158 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 162146671948800)), (nat_lit 87, Int.ofNat (nat_lit 165208450176000)), (nat_lit 88, Int.ofNat (nat_lit 168270228403200)), (nat_lit 89, Int.ofNat (nat_lit 171332006630400)), (nat_lit 90, Int.ofNat (nat_lit 194231556288000)), (nat_lit 91, Int.ofNat (nat_lit 121344224601600)), (nat_lit 92, Int.ofNat (nat_lit 98593511385600)), (nat_lit 93, Int.ofNat (nat_lit 28810482624000)), (nat_lit 94, Int.ofNat (nat_lit 38762067254400)), (nat_lit 95, Int.ofNat (nat_lit 4273732108800)), (nat_lit 100, Int.ofNat (nat_lit 72859948358400)), (nat_lit 101, Int.ofNat (nat_lit 134698516442424)), (nat_lit 102, Int.ofNat (nat_lit 136589328691200)), (nat_lit 103, Int.ofNat (nat_lit 140671699660800)), (nat_lit 104, Int.ofNat (nat_lit 144754070630400)), (nat_lit 105, Int.ofNat (nat_lit 148836441600000)), (nat_lit 106, Int.ofNat (nat_lit 152918812569600)), (nat_lit 107, Int.ofNat (nat_lit 161648510303808)), (nat_lit 108, Int.ofNat (nat_lit 215408764568448)), (nat_lit 109, Int.ofNat (nat_lit 196002793324800)), (nat_lit 110, Int.ofNat (nat_lit 169248296448000)), (nat_lit 111, Int.ofNat (nat_lit 173330667417600)), (nat_lit 112, Int.ofNat (nat_lit 177413038387200)), (nat_lit 113, Int.ofNat (nat_lit 182657267856000)), (nat_lit 114, Int.ofNat (nat_lit 204644791612800)), (nat_lit 115, Int.ofNat (nat_lit 139707504493200)), (nat_lit 116, Int.ofNat (nat_lit 106646444780400)), (nat_lit 117, Int.ofNat (nat_lit 47333592558000)), (nat_lit 118, Int.ofNat (nat_lit 57134810502000)), (nat_lit 119, Int.ofNat (nat_lit 22496108670000)), (nat_lit 125, Int.ofNat (nat_lit 82684750579200)), (nat_lit 126, Int.ofNat (nat_lit 148625354906424)), (nat_lit 127, Int.ofNat (nat_lit 148356622442424)), (nat_lit 128, Int.ofNat (nat_lit 154227963861576)), (nat_lit 129, Int.ofNat (nat_lit 158423328078444)), (nat_lit 130, Int.ofNat (nat_lit 158481345814308)), (nat_lit 131, Int.ofNat (nat_lit 165688356575808)), (nat_lit 132, Int.ofNat (nat_lit 220469203582848)), (nat_lit 133, Int.ofNat (nat_lit 202083825081600)), (nat_lit 134, Int.ofNat (nat_lit 176349920947200)), (nat_lit 135, Int.ofNat (nat_lit 181637319427200)), (nat_lit 136, Int.ofNat (nat_lit 189880345468800)), (nat_lit 137, Int.ofNat (nat_lit 195640186896000)), (nat_lit 138, Int.ofNat (nat_lit 216778750372800)), (nat_lit 139, Int.ofNat (nat_lit 158226313291200)), (nat_lit 140, Int.ofNat (nat_lit 130583902680000)), (nat_lit 141, Int.ofNat (nat_lit 75892956955200)), (nat_lit 142, Int.ofNat (nat_lit 81891667368000)), (nat_lit 143, Int.ofNat (nat_lit 53774798616000)), (nat_lit 150, Int.ofNat (nat_lit 100400811033600)), (nat_lit 151, Int.ofNat (nat_lit 177142415936640)), (nat_lit 152, Int.ofNat (nat_lit 167536677369600)), (nat_lit 153, Int.ofNat (nat_lit 171625729842468)), (nat_lit 154, Int.ofNat (nat_lit 174036270802284)), (nat_lit 155, Int.ofNat (nat_lit 179411685885432)), (nat_lit 156, Int.ofNat (nat_lit 227754227230992)), (nat_lit 157, Int.ofNat (nat_lit 212591933215200)), (nat_lit 158, Int.ofNat (nat_lit 190999679270400)), (nat_lit 159, Int.ofNat (nat_lit 196547541523200)), (nat_lit 160, Int.ofNat (nat_lit 205051031337600)), (nat_lit 161, Int.ofNat (nat_lit 211071336537600)), (nat_lit 162, Int.ofNat (nat_lit 229282538284800)), (nat_lit 163, Int.ofNat (nat_lit 169646965488000)), (nat_lit 164, Int.ofNat (nat_lit 134261101497600)), (nat_lit 165, Int.ofNat (nat_lit 78771686716800)), (nat_lit 166, Int.ofNat (nat_lit 89313301526400)), (nat_lit 167, Int.ofNat (nat_lit 55414996560000)), (nat_lit 175, Int.ofNat (nat_lit 112758960652800)), (nat_lit 176, Int.ofNat (nat_lit 207122327744640)), (nat_lit 177, Int.ofNat (nat_lit 186386366252196)), (nat_lit 178, Int.ofNat (nat_lit 187147461941484)), (nat_lit 179, Int.ofNat (nat_lit 193043804570232)), (nat_lit 180, Int.ofNat (nat_lit 241907273461392)), (nat_lit 181, Int.ofNat (nat_lit 226750295032800)), (nat_lit 182, Int.ofNat (nat_lit 205163356675200)), (nat_lit 183, Int.ofNat (nat_lit 210716534515200)), (nat_lit 184, Int.ofNat (nat_lit 219225339916800)), (nat_lit 185, Int.ofNat (nat_lit 225250960704000)), (nat_lit 186, Int.ofNat (nat_lit 243279070003200)), (nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
theorem block006_data_flat158_step : block006_data_flat158 = (CoefficientMerge.fastMerge block006_data_flat078 block006_data_flat157) := by decide +kernel
theorem block006_data_flat158_original : block006_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded)))))))) := by
  rw [block006_data_flat158_step, block006_data_flat078_original, block006_data_flat157_original]
def block006_data_flat159 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 162146671948800)), (nat_lit 87, Int.ofNat (nat_lit 165208450176000)), (nat_lit 88, Int.ofNat (nat_lit 168270228403200)), (nat_lit 89, Int.ofNat (nat_lit 171332006630400)), (nat_lit 90, Int.ofNat (nat_lit 194231556288000)), (nat_lit 91, Int.ofNat (nat_lit 121344224601600)), (nat_lit 92, Int.ofNat (nat_lit 98593511385600)), (nat_lit 93, Int.ofNat (nat_lit 28810482624000)), (nat_lit 94, Int.ofNat (nat_lit 38762067254400)), (nat_lit 95, Int.ofNat (nat_lit 4273732108800)), (nat_lit 100, Int.ofNat (nat_lit 72859948358400)), (nat_lit 101, Int.ofNat (nat_lit 134698516442424)), (nat_lit 102, Int.ofNat (nat_lit 136589328691200)), (nat_lit 103, Int.ofNat (nat_lit 140671699660800)), (nat_lit 104, Int.ofNat (nat_lit 144754070630400)), (nat_lit 105, Int.ofNat (nat_lit 148836441600000)), (nat_lit 106, Int.ofNat (nat_lit 152918812569600)), (nat_lit 107, Int.ofNat (nat_lit 161648510303808)), (nat_lit 108, Int.ofNat (nat_lit 215408764568448)), (nat_lit 109, Int.ofNat (nat_lit 196002793324800)), (nat_lit 110, Int.ofNat (nat_lit 169248296448000)), (nat_lit 111, Int.ofNat (nat_lit 173330667417600)), (nat_lit 112, Int.ofNat (nat_lit 177413038387200)), (nat_lit 113, Int.ofNat (nat_lit 182657267856000)), (nat_lit 114, Int.ofNat (nat_lit 204644791612800)), (nat_lit 115, Int.ofNat (nat_lit 139707504493200)), (nat_lit 116, Int.ofNat (nat_lit 106646444780400)), (nat_lit 117, Int.ofNat (nat_lit 47333592558000)), (nat_lit 118, Int.ofNat (nat_lit 57134810502000)), (nat_lit 119, Int.ofNat (nat_lit 22496108670000)), (nat_lit 125, Int.ofNat (nat_lit 82684750579200)), (nat_lit 126, Int.ofNat (nat_lit 148625354906424)), (nat_lit 127, Int.ofNat (nat_lit 148356622442424)), (nat_lit 128, Int.ofNat (nat_lit 154227963861576)), (nat_lit 129, Int.ofNat (nat_lit 158423328078444)), (nat_lit 130, Int.ofNat (nat_lit 158481345814308)), (nat_lit 131, Int.ofNat (nat_lit 165688356575808)), (nat_lit 132, Int.ofNat (nat_lit 220469203582848)), (nat_lit 133, Int.ofNat (nat_lit 202083825081600)), (nat_lit 134, Int.ofNat (nat_lit 176349920947200)), (nat_lit 135, Int.ofNat (nat_lit 181637319427200)), (nat_lit 136, Int.ofNat (nat_lit 189880345468800)), (nat_lit 137, Int.ofNat (nat_lit 195640186896000)), (nat_lit 138, Int.ofNat (nat_lit 216778750372800)), (nat_lit 139, Int.ofNat (nat_lit 158226313291200)), (nat_lit 140, Int.ofNat (nat_lit 130583902680000)), (nat_lit 141, Int.ofNat (nat_lit 75892956955200)), (nat_lit 142, Int.ofNat (nat_lit 81891667368000)), (nat_lit 143, Int.ofNat (nat_lit 53774798616000)), (nat_lit 150, Int.ofNat (nat_lit 100400811033600)), (nat_lit 151, Int.ofNat (nat_lit 177142415936640)), (nat_lit 152, Int.ofNat (nat_lit 167536677369600)), (nat_lit 153, Int.ofNat (nat_lit 171625729842468)), (nat_lit 154, Int.ofNat (nat_lit 174036270802284)), (nat_lit 155, Int.ofNat (nat_lit 179411685885432)), (nat_lit 156, Int.ofNat (nat_lit 227754227230992)), (nat_lit 157, Int.ofNat (nat_lit 212591933215200)), (nat_lit 158, Int.ofNat (nat_lit 190999679270400)), (nat_lit 159, Int.ofNat (nat_lit 196547541523200)), (nat_lit 160, Int.ofNat (nat_lit 205051031337600)), (nat_lit 161, Int.ofNat (nat_lit 211071336537600)), (nat_lit 162, Int.ofNat (nat_lit 229282538284800)), (nat_lit 163, Int.ofNat (nat_lit 169646965488000)), (nat_lit 164, Int.ofNat (nat_lit 134261101497600)), (nat_lit 165, Int.ofNat (nat_lit 78771686716800)), (nat_lit 166, Int.ofNat (nat_lit 89313301526400)), (nat_lit 167, Int.ofNat (nat_lit 55414996560000)), (nat_lit 175, Int.ofNat (nat_lit 112758960652800)), (nat_lit 176, Int.ofNat (nat_lit 207122327744640)), (nat_lit 177, Int.ofNat (nat_lit 186386366252196)), (nat_lit 178, Int.ofNat (nat_lit 187147461941484)), (nat_lit 179, Int.ofNat (nat_lit 193043804570232)), (nat_lit 180, Int.ofNat (nat_lit 241907273461392)), (nat_lit 181, Int.ofNat (nat_lit 226750295032800)), (nat_lit 182, Int.ofNat (nat_lit 205163356675200)), (nat_lit 183, Int.ofNat (nat_lit 210716534515200)), (nat_lit 184, Int.ofNat (nat_lit 219225339916800)), (nat_lit 185, Int.ofNat (nat_lit 225250960704000)), (nat_lit 186, Int.ofNat (nat_lit 243279070003200)), (nat_lit 187, Int.ofNat (nat_lit 183271996723200))]
theorem block006_data_flat159_step : block006_data_flat159 = (CoefficientMerge.trim block006_data_flat158) := by decide +kernel
theorem block006_data_flat159_original : block006_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded))))))))) := by
  rw [block006_data_flat159_step, block006_data_flat158_original]
theorem block006_data : block006 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (162146671948800 : Int) atom0289Coded) (CoefficientMerge.scale (165208450176000 : Int) atom0290Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (168270228403200 : Int) atom0291Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171332006630400 : Int) atom0292Coded) (CoefficientMerge.scale (194231556288000 : Int) atom0293Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (121344224601600 : Int) atom0294Coded) (CoefficientMerge.scale (98593511385600 : Int) atom0295Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28810482624000 : Int) atom0296Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38762067254400 : Int) atom0297Coded) (CoefficientMerge.scale (4273732108800 : Int) atom0298Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (72859948358400 : Int) atom0299Coded) (CoefficientMerge.scale (134698516442424 : Int) atom0300Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136589328691200 : Int) atom0301Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140671699660800 : Int) atom0302Coded) (CoefficientMerge.scale (144754070630400 : Int) atom0303Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (148836441600000 : Int) atom0304Coded) (CoefficientMerge.scale (152918812569600 : Int) atom0305Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (161648510303808 : Int) atom0306Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (215408764568448 : Int) atom0307Coded) (CoefficientMerge.scale (196002793324800 : Int) atom0308Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (169248296448000 : Int) atom0309Coded) (CoefficientMerge.scale (173330667417600 : Int) atom0310Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177413038387200 : Int) atom0311Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182657267856000 : Int) atom0312Coded) (CoefficientMerge.scale (204644791612800 : Int) atom0313Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (139707504493200 : Int) atom0314Coded) (CoefficientMerge.scale (106646444780400 : Int) atom0315Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47333592558000 : Int) atom0316Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57134810502000 : Int) atom0317Coded) (CoefficientMerge.scale (22496108670000 : Int) atom0318Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (82684750579200 : Int) atom0319Coded) (CoefficientMerge.scale (148625354906424 : Int) atom0320Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148356622442424 : Int) atom0321Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154227963861576 : Int) atom0322Coded) (CoefficientMerge.scale (158423328078444 : Int) atom0323Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (158481345814308 : Int) atom0324Coded) (CoefficientMerge.scale (165688356575808 : Int) atom0325Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220469203582848 : Int) atom0326Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (202083825081600 : Int) atom0327Coded) (CoefficientMerge.scale (176349920947200 : Int) atom0328Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (181637319427200 : Int) atom0329Coded) (CoefficientMerge.scale (189880345468800 : Int) atom0330Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195640186896000 : Int) atom0331Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216778750372800 : Int) atom0332Coded) (CoefficientMerge.scale (158226313291200 : Int) atom0333Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130583902680000 : Int) atom0334Coded) (CoefficientMerge.scale (75892956955200 : Int) atom0335Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (81891667368000 : Int) atom0336Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53774798616000 : Int) atom0337Coded) (CoefficientMerge.scale (100400811033600 : Int) atom0338Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (177142415936640 : Int) atom0339Coded) (CoefficientMerge.scale (167536677369600 : Int) atom0340Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (171625729842468 : Int) atom0341Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174036270802284 : Int) atom0342Coded) (CoefficientMerge.scale (179411685885432 : Int) atom0343Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (227754227230992 : Int) atom0344Coded) (CoefficientMerge.scale (212591933215200 : Int) atom0345Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (190999679270400 : Int) atom0346Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (196547541523200 : Int) atom0347Coded) (CoefficientMerge.scale (205051031337600 : Int) atom0348Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (211071336537600 : Int) atom0349Coded) (CoefficientMerge.scale (229282538284800 : Int) atom0350Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (169646965488000 : Int) atom0351Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134261101497600 : Int) atom0352Coded) (CoefficientMerge.scale (78771686716800 : Int) atom0353Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89313301526400 : Int) atom0354Coded) (CoefficientMerge.scale (55414996560000 : Int) atom0355Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112758960652800 : Int) atom0356Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207122327744640 : Int) atom0357Coded) (CoefficientMerge.scale (186386366252196 : Int) atom0358Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (187147461941484 : Int) atom0359Coded) (CoefficientMerge.scale (193043804570232 : Int) atom0360Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241907273461392 : Int) atom0361Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226750295032800 : Int) atom0362Coded) (CoefficientMerge.scale (205163356675200 : Int) atom0363Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (210716534515200 : Int) atom0364Coded) (CoefficientMerge.scale (219225339916800 : Int) atom0365Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225250960704000 : Int) atom0366Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (243279070003200 : Int) atom0367Coded) (CoefficientMerge.scale (183271996723200 : Int) atom0368Coded)))))))) := by
  have h : block006 = block006_data_flat159 := by decide +kernel
  exact h.trans block006_data_flat159_original
theorem block006_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block006 := by
  rw [block006_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0289Coded_nonneg g hg hA hB) (atom0290Coded_nonneg g hg hA hB)) (add_nonneg (atom0291Coded_nonneg g hg hA hB) (add_nonneg (atom0292Coded_nonneg g hg hA hB) (atom0293Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0294Coded_nonneg g hg hA hB) (atom0295Coded_nonneg g hg hA hB)) (add_nonneg (atom0296Coded_nonneg g hg hA hB) (add_nonneg (atom0297Coded_nonneg g hg hA hB) (atom0298Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0299Coded_nonneg g hg hA hB) (atom0300Coded_nonneg g hg hA hB)) (add_nonneg (atom0301Coded_nonneg g hg hA hB) (add_nonneg (atom0302Coded_nonneg g hg hA hB) (atom0303Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0304Coded_nonneg g hg hA hB) (atom0305Coded_nonneg g hg hA hB)) (add_nonneg (atom0306Coded_nonneg g hg hA hB) (add_nonneg (atom0307Coded_nonneg g hg hA hB) (atom0308Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0309Coded_nonneg g hg hA hB) (atom0310Coded_nonneg g hg hA hB)) (add_nonneg (atom0311Coded_nonneg g hg hA hB) (add_nonneg (atom0312Coded_nonneg g hg hA hB) (atom0313Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0314Coded_nonneg g hg hA hB) (atom0315Coded_nonneg g hg hA hB)) (add_nonneg (atom0316Coded_nonneg g hg hA hB) (add_nonneg (atom0317Coded_nonneg g hg hA hB) (atom0318Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0319Coded_nonneg g hg hA hB) (atom0320Coded_nonneg g hg hA hB)) (add_nonneg (atom0321Coded_nonneg g hg hA hB) (add_nonneg (atom0322Coded_nonneg g hg hA hB) (atom0323Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0324Coded_nonneg g hg hA hB) (atom0325Coded_nonneg g hg hA hB)) (add_nonneg (atom0326Coded_nonneg g hg hA hB) (add_nonneg (atom0327Coded_nonneg g hg hA hB) (atom0328Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0329Coded_nonneg g hg hA hB) (atom0330Coded_nonneg g hg hA hB)) (add_nonneg (atom0331Coded_nonneg g hg hA hB) (add_nonneg (atom0332Coded_nonneg g hg hA hB) (atom0333Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0334Coded_nonneg g hg hA hB) (atom0335Coded_nonneg g hg hA hB)) (add_nonneg (atom0336Coded_nonneg g hg hA hB) (add_nonneg (atom0337Coded_nonneg g hg hA hB) (atom0338Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0339Coded_nonneg g hg hA hB) (atom0340Coded_nonneg g hg hA hB)) (add_nonneg (atom0341Coded_nonneg g hg hA hB) (add_nonneg (atom0342Coded_nonneg g hg hA hB) (atom0343Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0344Coded_nonneg g hg hA hB) (atom0345Coded_nonneg g hg hA hB)) (add_nonneg (atom0346Coded_nonneg g hg hA hB) (add_nonneg (atom0347Coded_nonneg g hg hA hB) (atom0348Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0349Coded_nonneg g hg hA hB) (atom0350Coded_nonneg g hg hA hB)) (add_nonneg (atom0351Coded_nonneg g hg hA hB) (add_nonneg (atom0352Coded_nonneg g hg hA hB) (atom0353Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0354Coded_nonneg g hg hA hB) (atom0355Coded_nonneg g hg hA hB)) (add_nonneg (atom0356Coded_nonneg g hg hA hB) (add_nonneg (atom0357Coded_nonneg g hg hA hB) (atom0358Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0359Coded_nonneg g hg hA hB) (atom0360Coded_nonneg g hg hA hB)) (add_nonneg (atom0361Coded_nonneg g hg hA hB) (add_nonneg (atom0362Coded_nonneg g hg hA hB) (atom0363Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0364Coded_nonneg g hg hA hB) (atom0365Coded_nonneg g hg hA hB)) (add_nonneg (atom0366Coded_nonneg g hg hA hB) (add_nonneg (atom0367Coded_nonneg g hg hA hB) (atom0368Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
