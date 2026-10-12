-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0449 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0449 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0449 = ((g 0) * (g 13) * (g 19)) := by
  norm_num [atom0449, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0449_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (280362100233600 : Int) atom0449) := by
  rw [SparsePolynomial.eval_scale, eval_atom0449]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0449Coded : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 1))]
theorem atom0449Coded_decode : atom0449 = SparsePolynomial.decodeCubic 24 atom0449Coded := by decide +kernel
theorem atom0449Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) := by
  have h := atom0449_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0449Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0450 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0450 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0450 = ((g 0) * (g 13) * (g 20)) := by
  norm_num [atom0450, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0450_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283858818566400 : Int) atom0450) := by
  rw [SparsePolynomial.eval_scale, eval_atom0450]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0450Coded : CoefficientMerge.Poly := [(nat_lit 332, Int.ofNat (nat_lit 1))]
theorem atom0450Coded_decode : atom0450 = SparsePolynomial.decodeCubic 24 atom0450Coded := by decide +kernel
theorem atom0450Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded) := by
  have h := atom0450_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0450Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0451 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0451 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0451 = ((g 0) * (g 13) * (g 21)) := by
  norm_num [atom0451, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0451_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220539543840000 : Int) atom0451) := by
  rw [SparsePolynomial.eval_scale, eval_atom0451]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0451Coded : CoefficientMerge.Poly := [(nat_lit 333, Int.ofNat (nat_lit 1))]
theorem atom0451Coded_decode : atom0451 = SparsePolynomial.decodeCubic 24 atom0451Coded := by decide +kernel
theorem atom0451Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) := by
  have h := atom0451_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0451Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0452 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0452 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0452 = ((g 0) * (g 13) * (g 22)) := by
  norm_num [atom0452, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0452_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165174808478400 : Int) atom0452) := by
  rw [SparsePolynomial.eval_scale, eval_atom0452]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0452Coded : CoefficientMerge.Poly := [(nat_lit 334, Int.ofNat (nat_lit 1))]
theorem atom0452Coded_decode : atom0452 = SparsePolynomial.decodeCubic 24 atom0452Coded := by decide +kernel
theorem atom0452Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) := by
  have h := atom0452_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0452Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0453 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0453 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0453 = ((g 0) * (g 13) * (g 23)) := by
  norm_num [atom0453, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0453_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153751952692800 : Int) atom0453) := by
  rw [SparsePolynomial.eval_scale, eval_atom0453]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0453Coded : CoefficientMerge.Poly := [(nat_lit 335, Int.ofNat (nat_lit 1))]
theorem atom0453Coded_decode : atom0453 = SparsePolynomial.decodeCubic 24 atom0453Coded := by decide +kernel
theorem atom0453Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded) := by
  have h := atom0453_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0453Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0454 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0454 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0454 = ((g 0) * (g 14) * (g 14)) := by
  norm_num [atom0454, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0454_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (180207265392000 : Int) atom0454) := by
  rw [SparsePolynomial.eval_scale, eval_atom0454]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0454Coded : CoefficientMerge.Poly := [(nat_lit 350, Int.ofNat (nat_lit 1))]
theorem atom0454Coded_decode : atom0454 = SparsePolynomial.decodeCubic 24 atom0454Coded := by decide +kernel
theorem atom0454Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) := by
  have h := atom0454_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0454Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0455 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0455 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0455 = ((g 0) * (g 14) * (g 15)) := by
  norm_num [atom0455, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0455_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (326270355747840 : Int) atom0455) := by
  rw [SparsePolynomial.eval_scale, eval_atom0455]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0455Coded : CoefficientMerge.Poly := [(nat_lit 351, Int.ofNat (nat_lit 1))]
theorem atom0455Coded_decode : atom0455 = SparsePolynomial.decodeCubic 24 atom0455Coded := by decide +kernel
theorem atom0455Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded) := by
  have h := atom0455_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0455Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0456 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0456 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0456 = ((g 0) * (g 14) * (g 16)) := by
  norm_num [atom0456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0456_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (298937896306560 : Int) atom0456) := by
  rw [SparsePolynomial.eval_scale, eval_atom0456]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0456Coded : CoefficientMerge.Poly := [(nat_lit 352, Int.ofNat (nat_lit 1))]
theorem atom0456Coded_decode : atom0456 = SparsePolynomial.decodeCubic 24 atom0456Coded := by decide +kernel
theorem atom0456Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) := by
  have h := atom0456_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0456Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0457 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0457 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0457 = ((g 0) * (g 14) * (g 17)) := by
  norm_num [atom0457, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0457_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (297051845428800 : Int) atom0457) := by
  rw [SparsePolynomial.eval_scale, eval_atom0457]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0457Coded : CoefficientMerge.Poly := [(nat_lit 353, Int.ofNat (nat_lit 1))]
theorem atom0457Coded_decode : atom0457 = SparsePolynomial.decodeCubic 24 atom0457Coded := by decide +kernel
theorem atom0457Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) := by
  have h := atom0457_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0457Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0458 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0458 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0458 = ((g 0) * (g 14) * (g 18)) := by
  norm_num [atom0458, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0458_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (320423596416000 : Int) atom0458) := by
  rw [SparsePolynomial.eval_scale, eval_atom0458]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0458Coded : CoefficientMerge.Poly := [(nat_lit 354, Int.ofNat (nat_lit 1))]
theorem atom0458Coded_decode : atom0458 = SparsePolynomial.decodeCubic 24 atom0458Coded := by decide +kernel
theorem atom0458Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded) := by
  have h := atom0458_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0458Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0459 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0459 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0459 = ((g 0) * (g 14) * (g 19)) := by
  norm_num [atom0459, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0459_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (262910161067400 : Int) atom0459) := by
  rw [SparsePolynomial.eval_scale, eval_atom0459]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0459Coded : CoefficientMerge.Poly := [(nat_lit 355, Int.ofNat (nat_lit 1))]
theorem atom0459Coded_decode : atom0459 = SparsePolynomial.decodeCubic 24 atom0459Coded := by decide +kernel
theorem atom0459Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) := by
  have h := atom0459_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0459Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0460 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0460 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0460 = ((g 0) * (g 14) * (g 20)) := by
  norm_num [atom0460, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0460_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (266247131673600 : Int) atom0460) := by
  rw [SparsePolynomial.eval_scale, eval_atom0460]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0460Coded : CoefficientMerge.Poly := [(nat_lit 356, Int.ofNat (nat_lit 1))]
theorem atom0460Coded_decode : atom0460 = SparsePolynomial.decodeCubic 24 atom0460Coded := by decide +kernel
theorem atom0460Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded) := by
  have h := atom0460_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0460Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0461 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0461 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0461 = ((g 0) * (g 14) * (g 21)) := by
  norm_num [atom0461, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0461_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (203948449689600 : Int) atom0461) := by
  rw [SparsePolynomial.eval_scale, eval_atom0461]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0461Coded : CoefficientMerge.Poly := [(nat_lit 357, Int.ofNat (nat_lit 1))]
theorem atom0461Coded_decode : atom0461 = SparsePolynomial.decodeCubic 24 atom0461Coded := by decide +kernel
theorem atom0461Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) := by
  have h := atom0461_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0461Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0462 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0462 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0462 = ((g 0) * (g 14) * (g 22)) := by
  norm_num [atom0462, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0462_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163012699899000 : Int) atom0462) := by
  rw [SparsePolynomial.eval_scale, eval_atom0462]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0462Coded : CoefficientMerge.Poly := [(nat_lit 358, Int.ofNat (nat_lit 1))]
theorem atom0462Coded_decode : atom0462 = SparsePolynomial.decodeCubic 24 atom0462Coded := by decide +kernel
theorem atom0462Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) := by
  have h := atom0462_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0462Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0463 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0463 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0463 = ((g 0) * (g 14) * (g 23)) := by
  norm_num [atom0463, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0463_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150660684682200 : Int) atom0463) := by
  rw [SparsePolynomial.eval_scale, eval_atom0463]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0463Coded : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 1))]
theorem atom0463Coded_decode : atom0463 = SparsePolynomial.decodeCubic 24 atom0463Coded := by decide +kernel
theorem atom0463Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded) := by
  have h := atom0463_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0463Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0464 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0464 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0464 = ((g 0) * (g 15) * (g 15)) := by
  norm_num [atom0464, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0464_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185418634867200 : Int) atom0464) := by
  rw [SparsePolynomial.eval_scale, eval_atom0464]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0464Coded : CoefficientMerge.Poly := [(nat_lit 375, Int.ofNat (nat_lit 1))]
theorem atom0464Coded_decode : atom0464 = SparsePolynomial.decodeCubic 24 atom0464Coded := by decide +kernel
theorem atom0464Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) := by
  have h := atom0464_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0464Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0465 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0465 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0465 = ((g 0) * (g 15) * (g 16)) := by
  norm_num [atom0465, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0465_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (335715348810240 : Int) atom0465) := by
  rw [SparsePolynomial.eval_scale, eval_atom0465]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0465Coded : CoefficientMerge.Poly := [(nat_lit 376, Int.ofNat (nat_lit 1))]
theorem atom0465Coded_decode : atom0465 = SparsePolynomial.decodeCubic 24 atom0465Coded := by decide +kernel
theorem atom0465Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded) := by
  have h := atom0465_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0465Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0466 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0466 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0466 = ((g 0) * (g 15) * (g 17)) := by
  norm_num [atom0466, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0466_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (309666780864000 : Int) atom0466) := by
  rw [SparsePolynomial.eval_scale, eval_atom0466]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0466Coded : CoefficientMerge.Poly := [(nat_lit 377, Int.ofNat (nat_lit 1))]
theorem atom0466Coded_decode : atom0466 = SparsePolynomial.decodeCubic 24 atom0466Coded := by decide +kernel
theorem atom0466Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) := by
  have h := atom0466_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0466Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0467 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0467 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0467 = ((g 0) * (g 15) * (g 18)) := by
  norm_num [atom0467, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0467_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (331449735052800 : Int) atom0467) := by
  rw [SparsePolynomial.eval_scale, eval_atom0467]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0467Coded : CoefficientMerge.Poly := [(nat_lit 378, Int.ofNat (nat_lit 1))]
theorem atom0467Coded_decode : atom0467 = SparsePolynomial.decodeCubic 24 atom0467Coded := by decide +kernel
theorem atom0467Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) := by
  have h := atom0467_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0467Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0468 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0468 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0468 = ((g 0) * (g 15) * (g 19)) := by
  norm_num [atom0468, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0468_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (269855932147200 : Int) atom0468) := by
  rw [SparsePolynomial.eval_scale, eval_atom0468]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0468Coded : CoefficientMerge.Poly := [(nat_lit 379, Int.ofNat (nat_lit 1))]
theorem atom0468Coded_decode : atom0468 = SparsePolynomial.decodeCubic 24 atom0468Coded := by decide +kernel
theorem atom0468Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded) := by
  have h := atom0468_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0468Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0469 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0469 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0469 = ((g 0) * (g 15) * (g 20)) := by
  norm_num [atom0469, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0469_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278367314803200 : Int) atom0469) := by
  rw [SparsePolynomial.eval_scale, eval_atom0469]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0469Coded : CoefficientMerge.Poly := [(nat_lit 380, Int.ofNat (nat_lit 1))]
theorem atom0469Coded_decode : atom0469 = SparsePolynomial.decodeCubic 24 atom0469Coded := by decide +kernel
theorem atom0469Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) := by
  have h := atom0469_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0469Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0470 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0470 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0470 = ((g 0) * (g 15) * (g 21)) := by
  norm_num [atom0470, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0470_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (216773511897600 : Int) atom0470) := by
  rw [SparsePolynomial.eval_scale, eval_atom0470]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0470Coded : CoefficientMerge.Poly := [(nat_lit 381, Int.ofNat (nat_lit 1))]
theorem atom0470Coded_decode : atom0470 = SparsePolynomial.decodeCubic 24 atom0470Coded := by decide +kernel
theorem atom0470Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded) := by
  have h := atom0470_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0470Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0471 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0471 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0471 = ((g 0) * (g 15) * (g 22)) := by
  norm_num [atom0471, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0471_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154848692880000 : Int) atom0471) := by
  rw [SparsePolynomial.eval_scale, eval_atom0471]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0471Coded : CoefficientMerge.Poly := [(nat_lit 382, Int.ofNat (nat_lit 1))]
theorem atom0471Coded_decode : atom0471 = SparsePolynomial.decodeCubic 24 atom0471Coded := by decide +kernel
theorem atom0471Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) := by
  have h := atom0471_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0471Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0472 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0472 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0472 = ((g 0) * (g 15) * (g 23)) := by
  norm_num [atom0472, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0472_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139633710451200 : Int) atom0472) := by
  rw [SparsePolynomial.eval_scale, eval_atom0472]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0472Coded : CoefficientMerge.Poly := [(nat_lit 383, Int.ofNat (nat_lit 1))]
theorem atom0472Coded_decode : atom0472 = SparsePolynomial.decodeCubic 24 atom0472Coded := by decide +kernel
theorem atom0472Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) := by
  have h := atom0472_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0472Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0473 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0473 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0473 = ((g 0) * (g 16) * (g 16)) := by
  norm_num [atom0473, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0473_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (190423018598400 : Int) atom0473) := by
  rw [SparsePolynomial.eval_scale, eval_atom0473]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0473Coded : CoefficientMerge.Poly := [(nat_lit 400, Int.ofNat (nat_lit 1))]
theorem atom0473Coded_decode : atom0473 = SparsePolynomial.decodeCubic 24 atom0473Coded := by decide +kernel
theorem atom0473Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded) := by
  have h := atom0473_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0473Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0474 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0474 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0474 = ((g 0) * (g 16) * (g 17)) := by
  norm_num [atom0474, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0474_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (337110459571200 : Int) atom0474) := by
  rw [SparsePolynomial.eval_scale, eval_atom0474]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0474Coded : CoefficientMerge.Poly := [(nat_lit 401, Int.ofNat (nat_lit 1))]
theorem atom0474Coded_decode : atom0474 = SparsePolynomial.decodeCubic 24 atom0474Coded := by decide +kernel
theorem atom0474Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) := by
  have h := atom0474_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0474Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0475 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0475 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0475 = ((g 0) * (g 16) * (g 18)) := by
  norm_num [atom0475, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0475_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (339520246128000 : Int) atom0475) := by
  rw [SparsePolynomial.eval_scale, eval_atom0475]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0475Coded : CoefficientMerge.Poly := [(nat_lit 402, Int.ofNat (nat_lit 1))]
theorem atom0475Coded_decode : atom0475 = SparsePolynomial.decodeCubic 24 atom0475Coded := by decide +kernel
theorem atom0475Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded) := by
  have h := atom0475_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0475Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0476 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0476 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0476 = ((g 0) * (g 16) * (g 19)) := by
  norm_num [atom0476, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0476_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (272720067177600 : Int) atom0476) := by
  rw [SparsePolynomial.eval_scale, eval_atom0476]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0476Coded : CoefficientMerge.Poly := [(nat_lit 403, Int.ofNat (nat_lit 1))]
theorem atom0476Coded_decode : atom0476 = SparsePolynomial.decodeCubic 24 atom0476Coded := by decide +kernel
theorem atom0476Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) := by
  have h := atom0476_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0476Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0477 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0477 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0477 = ((g 0) * (g 16) * (g 20)) := by
  norm_num [atom0477, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0477_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (269798105001600 : Int) atom0477) := by
  rw [SparsePolynomial.eval_scale, eval_atom0477]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0477Coded : CoefficientMerge.Poly := [(nat_lit 404, Int.ofNat (nat_lit 1))]
theorem atom0477Coded_decode : atom0477 = SparsePolynomial.decodeCubic 24 atom0477Coded := by decide +kernel
theorem atom0477Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) := by
  have h := atom0477_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0477Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0478 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0478 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0478 = ((g 0) * (g 16) * (g 21)) := by
  norm_num [atom0478, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0478_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202997926051200 : Int) atom0478) := by
  rw [SparsePolynomial.eval_scale, eval_atom0478]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0478Coded : CoefficientMerge.Poly := [(nat_lit 405, Int.ofNat (nat_lit 1))]
theorem atom0478Coded_decode : atom0478 = SparsePolynomial.decodeCubic 24 atom0478Coded := by decide +kernel
theorem atom0478Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded) := by
  have h := atom0478_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0478Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0479 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0479 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0479 = ((g 0) * (g 16) * (g 22)) := by
  norm_num [atom0479, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0479_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129247858454400 : Int) atom0479) := by
  rw [SparsePolynomial.eval_scale, eval_atom0479]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0479Coded : CoefficientMerge.Poly := [(nat_lit 406, Int.ofNat (nat_lit 1))]
theorem atom0479Coded_decode : atom0479 = SparsePolynomial.decodeCubic 24 atom0479Coded := by decide +kernel
theorem atom0479Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) := by
  have h := atom0479_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0479Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0480 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0480 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0480 = ((g 0) * (g 16) * (g 23)) := by
  norm_num [atom0480, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0480_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121733228937600 : Int) atom0480) := by
  rw [SparsePolynomial.eval_scale, eval_atom0480]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0480Coded : CoefficientMerge.Poly := [(nat_lit 407, Int.ofNat (nat_lit 1))]
theorem atom0480Coded_decode : atom0480 = SparsePolynomial.decodeCubic 24 atom0480Coded := by decide +kernel
theorem atom0480Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded) := by
  have h := atom0480_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0480Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0481 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0481 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0481 = ((g 0) * (g 17) * (g 17)) := by
  norm_num [atom0481, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0481_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (187597703462400 : Int) atom0481) := by
  rw [SparsePolynomial.eval_scale, eval_atom0481]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0481Coded : CoefficientMerge.Poly := [(nat_lit 425, Int.ofNat (nat_lit 1))]
theorem atom0481Coded_decode : atom0481 = SparsePolynomial.decodeCubic 24 atom0481Coded := by decide +kernel
theorem atom0481Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) := by
  have h := atom0481_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0481Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0482 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0482 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0482 = ((g 0) * (g 17) * (g 18)) := by
  norm_num [atom0482, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0482_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (350073941817600 : Int) atom0482) := by
  rw [SparsePolynomial.eval_scale, eval_atom0482]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0482Coded : CoefficientMerge.Poly := [(nat_lit 426, Int.ofNat (nat_lit 1))]
theorem atom0482Coded_decode : atom0482 = SparsePolynomial.decodeCubic 24 atom0482Coded := by decide +kernel
theorem atom0482Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) := by
  have h := atom0482_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0482Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0483 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0483 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0483 = ((g 0) * (g 17) * (g 19)) := by
  norm_num [atom0483, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0483_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283033756051200 : Int) atom0483) := by
  rw [SparsePolynomial.eval_scale, eval_atom0483]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0483Coded : CoefficientMerge.Poly := [(nat_lit 427, Int.ofNat (nat_lit 1))]
theorem atom0483Coded_decode : atom0483 = SparsePolynomial.decodeCubic 24 atom0483Coded := by decide +kernel
theorem atom0483Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded) := by
  have h := atom0483_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0483Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0484 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0484 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0484 = ((g 0) * (g 17) * (g 20)) := by
  norm_num [atom0484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0484_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278611187500800 : Int) atom0484) := by
  rw [SparsePolynomial.eval_scale, eval_atom0484]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0484Coded : CoefficientMerge.Poly := [(nat_lit 428, Int.ofNat (nat_lit 1))]
theorem atom0484Coded_decode : atom0484 = SparsePolynomial.decodeCubic 24 atom0484Coded := by decide +kernel
theorem atom0484Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) := by
  have h := atom0484_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0484Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0485 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0485 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0485 = ((g 0) * (g 17) * (g 21)) := by
  norm_num [atom0485, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0485_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (211571001734400 : Int) atom0485) := by
  rw [SparsePolynomial.eval_scale, eval_atom0485]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0485Coded : CoefficientMerge.Poly := [(nat_lit 429, Int.ofNat (nat_lit 1))]
theorem atom0485Coded_decode : atom0485 = SparsePolynomial.decodeCubic 24 atom0485Coded := by decide +kernel
theorem atom0485Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded) := by
  have h := atom0485_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0485Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0486 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0486 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0486 = ((g 0) * (g 17) * (g 22)) := by
  norm_num [atom0486, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0486_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135196644844800 : Int) atom0486) := by
  rw [SparsePolynomial.eval_scale, eval_atom0486]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0486Coded : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 1))]
theorem atom0486Coded_decode : atom0486 = SparsePolynomial.decodeCubic 24 atom0486Coded := by decide +kernel
theorem atom0486Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) := by
  have h := atom0486_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0486Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0487 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0487 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0487 = ((g 0) * (g 17) * (g 23)) := by
  norm_num [atom0487, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0487_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126181408953600 : Int) atom0487) := by
  rw [SparsePolynomial.eval_scale, eval_atom0487]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0487Coded : CoefficientMerge.Poly := [(nat_lit 431, Int.ofNat (nat_lit 1))]
theorem atom0487Coded_decode : atom0487 = SparsePolynomial.decodeCubic 24 atom0487Coded := by decide +kernel
theorem atom0487Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) := by
  have h := atom0487_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0487Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0488 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0488 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0488 = ((g 0) * (g 18) * (g 18)) := by
  norm_num [atom0488, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0488_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (194082719846400 : Int) atom0488) := by
  rw [SparsePolynomial.eval_scale, eval_atom0488]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0488Coded : CoefficientMerge.Poly := [(nat_lit 450, Int.ofNat (nat_lit 1))]
theorem atom0488Coded_decode : atom0488 = SparsePolynomial.decodeCubic 24 atom0488Coded := by decide +kernel
theorem atom0488Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded) := by
  have h := atom0488_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0488Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0489 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0489 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0489 = ((g 0) * (g 18) * (g 19)) := by
  norm_num [atom0489, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0489_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (329949128678400 : Int) atom0489) := by
  rw [SparsePolynomial.eval_scale, eval_atom0489]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0489Coded : CoefficientMerge.Poly := [(nat_lit 451, Int.ofNat (nat_lit 1))]
theorem atom0489Coded_decode : atom0489 = SparsePolynomial.decodeCubic 24 atom0489Coded := by decide +kernel
theorem atom0489Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) := by
  have h := atom0489_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0489Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0490 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0490 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0490 = ((g 0) * (g 18) * (g 20)) := by
  norm_num [atom0490, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0490_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (342153716889600 : Int) atom0490) := by
  rw [SparsePolynomial.eval_scale, eval_atom0490]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0490Coded : CoefficientMerge.Poly := [(nat_lit 452, Int.ofNat (nat_lit 1))]
theorem atom0490Coded_decode : atom0490 = SparsePolynomial.decodeCubic 24 atom0490Coded := by decide +kernel
theorem atom0490Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded) := by
  have h := atom0490_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0490Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0491 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0491 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0491 = ((g 0) * (g 18) * (g 21)) := by
  norm_num [atom0491, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0491_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283937405875200 : Int) atom0491) := by
  rw [SparsePolynomial.eval_scale, eval_atom0491]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0491Coded : CoefficientMerge.Poly := [(nat_lit 453, Int.ofNat (nat_lit 1))]
theorem atom0491Coded_decode : atom0491 = SparsePolynomial.decodeCubic 24 atom0491Coded := by decide +kernel
theorem atom0491Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) := by
  have h := atom0491_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0491Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0492 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0492 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0492 = ((g 0) * (g 18) * (g 22)) := by
  norm_num [atom0492, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0492_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163805135155200 : Int) atom0492) := by
  rw [SparsePolynomial.eval_scale, eval_atom0492]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0492Coded : CoefficientMerge.Poly := [(nat_lit 454, Int.ofNat (nat_lit 1))]
theorem atom0492Coded_decode : atom0492 = SparsePolynomial.decodeCubic 24 atom0492Coded := by decide +kernel
theorem atom0492Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) := by
  have h := atom0492_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0492Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0493 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0493 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0493 = ((g 0) * (g 18) * (g 23)) := by
  norm_num [atom0493, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0493_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171417056025600 : Int) atom0493) := by
  rw [SparsePolynomial.eval_scale, eval_atom0493]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0493Coded : CoefficientMerge.Poly := [(nat_lit 455, Int.ofNat (nat_lit 1))]
theorem atom0493Coded_decode : atom0493 = SparsePolynomial.decodeCubic 24 atom0493Coded := by decide +kernel
theorem atom0493Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded) := by
  have h := atom0493_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0493Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0494 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0494 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0494 = ((g 0) * (g 19) * (g 19)) := by
  norm_num [atom0494, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0494_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137682213419520 : Int) atom0494) := by
  rw [SparsePolynomial.eval_scale, eval_atom0494]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0494Coded : CoefficientMerge.Poly := [(nat_lit 475, Int.ofNat (nat_lit 1))]
theorem atom0494Coded_decode : atom0494 = SparsePolynomial.decodeCubic 24 atom0494Coded := by decide +kernel
theorem atom0494Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) := by
  have h := atom0494_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0494Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0495 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0495 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0495 = ((g 0) * (g 19) * (g 20)) := by
  norm_num [atom0495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0495_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278791917465600 : Int) atom0495) := by
  rw [SparsePolynomial.eval_scale, eval_atom0495]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0495Coded : CoefficientMerge.Poly := [(nat_lit 476, Int.ofNat (nat_lit 1))]
theorem atom0495Coded_decode : atom0495 = SparsePolynomial.decodeCubic 24 atom0495Coded := by decide +kernel
theorem atom0495Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded) := by
  have h := atom0495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0496 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0496 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0496 = ((g 0) * (g 19) * (g 21)) := by
  norm_num [atom0496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0496_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (292017098419200 : Int) atom0496) := by
  rw [SparsePolynomial.eval_scale, eval_atom0496]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0496Coded : CoefficientMerge.Poly := [(nat_lit 477, Int.ofNat (nat_lit 1))]
theorem atom0496Coded_decode : atom0496 = SparsePolynomial.decodeCubic 24 atom0496Coded := by decide +kernel
theorem atom0496Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) := by
  have h := atom0496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0497 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0497 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0497 = ((g 0) * (g 19) * (g 22)) := by
  norm_num [atom0497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0497_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (172905420441600 : Int) atom0497) := by
  rw [SparsePolynomial.eval_scale, eval_atom0497]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0497Coded : CoefficientMerge.Poly := [(nat_lit 478, Int.ofNat (nat_lit 1))]
theorem atom0497Coded_decode : atom0497 = SparsePolynomial.decodeCubic 24 atom0497Coded := by decide +kernel
theorem atom0497Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) := by
  have h := atom0497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0498 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0498 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0498 = ((g 0) * (g 19) * (g 23)) := by
  norm_num [atom0498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0498_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (181537934054400 : Int) atom0498) := by
  rw [SparsePolynomial.eval_scale, eval_atom0498]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0498Coded : CoefficientMerge.Poly := [(nat_lit 479, Int.ofNat (nat_lit 1))]
theorem atom0498Coded_decode : atom0498 = SparsePolynomial.decodeCubic 24 atom0498Coded := by decide +kernel
theorem atom0498Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded) := by
  have h := atom0498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0499 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0499 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0499 = ((g 0) * (g 20) * (g 20)) := by
  norm_num [atom0499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0499_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142925508633600 : Int) atom0499) := by
  rw [SparsePolynomial.eval_scale, eval_atom0499]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0499Coded : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 1))]
theorem atom0499Coded_decode : atom0499 = SparsePolynomial.decodeCubic 24 atom0499Coded := by decide +kernel
theorem atom0499Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) := by
  have h := atom0499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0500 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0500 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0500 = ((g 0) * (g 20) * (g 21)) := by
  norm_num [atom0500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0500_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (300096790963200 : Int) atom0500) := by
  rw [SparsePolynomial.eval_scale, eval_atom0500]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0500Coded : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 1))]
theorem atom0500Coded_decode : atom0500 = SparsePolynomial.decodeCubic 24 atom0500Coded := by decide +kernel
theorem atom0500Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded) := by
  have h := atom0500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0501 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0501 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0501 = ((g 0) * (g 20) * (g 22)) := by
  norm_num [atom0501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0501_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182005705728000 : Int) atom0501) := by
  rw [SparsePolynomial.eval_scale, eval_atom0501]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0501Coded : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 1))]
theorem atom0501Coded_decode : atom0501 = SparsePolynomial.decodeCubic 24 atom0501Coded := by decide +kernel
theorem atom0501Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) := by
  have h := atom0501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0502 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0502 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0502 = ((g 0) * (g 20) * (g 23)) := by
  norm_num [atom0502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0502_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167207110963200 : Int) atom0502) := by
  rw [SparsePolynomial.eval_scale, eval_atom0502]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0502Coded : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 1))]
theorem atom0502Coded_decode : atom0502 = SparsePolynomial.decodeCubic 24 atom0502Coded := by decide +kernel
theorem atom0502Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) := by
  have h := atom0502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0503 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0503 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0503 = ((g 0) * (g 21) * (g 21)) := by
  norm_num [atom0503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0503_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154088241753600 : Int) atom0503) := by
  rw [SparsePolynomial.eval_scale, eval_atom0503]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 0) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0503Coded : CoefficientMerge.Poly := [(nat_lit 525, Int.ofNat (nat_lit 1))]
theorem atom0503Coded_decode : atom0503 = SparsePolynomial.decodeCubic 24 atom0503Coded := by decide +kernel
theorem atom0503Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded) := by
  have h := atom0503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0504 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0504 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0504 = ((g 0) * (g 21) * (g 22)) := by
  norm_num [atom0504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0504_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191105991014400 : Int) atom0504) := by
  rw [SparsePolynomial.eval_scale, eval_atom0504]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0504Coded : CoefficientMerge.Poly := [(nat_lit 526, Int.ofNat (nat_lit 1))]
theorem atom0504Coded_decode : atom0504 = SparsePolynomial.decodeCubic 24 atom0504Coded := by decide +kernel
theorem atom0504Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) := by
  have h := atom0504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0505 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0505 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0505 = ((g 0) * (g 21) * (g 23)) := by
  norm_num [atom0505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0505_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177327988992000 : Int) atom0505) := by
  rw [SparsePolynomial.eval_scale, eval_atom0505]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0505Coded : CoefficientMerge.Poly := [(nat_lit 527, Int.ofNat (nat_lit 1))]
theorem atom0505Coded_decode : atom0505 = SparsePolynomial.decodeCubic 24 atom0505Coded := by decide +kernel
theorem atom0505Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded) := by
  have h := atom0505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0506 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 22, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0506 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0506 = ((g 0) * (g 22) * (g 22)) := by
  norm_num [atom0506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0506_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22316002884000 : Int) atom0506) := by
  rw [SparsePolynomial.eval_scale, eval_atom0506]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 0) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0506Coded : CoefficientMerge.Poly := [(nat_lit 550, Int.ofNat (nat_lit 1))]
theorem atom0506Coded_decode : atom0506 = SparsePolynomial.decodeCubic 24 atom0506Coded := by decide +kernel
theorem atom0506Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) := by
  have h := atom0506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0507 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0507 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0507 = ((g 0) * (g 22) * (g 23)) := by
  norm_num [atom0507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0507_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35848320076800 : Int) atom0507) := by
  rw [SparsePolynomial.eval_scale, eval_atom0507]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 0) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0507Coded : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 1))]
theorem atom0507Coded_decode : atom0507 = SparsePolynomial.decodeCubic 24 atom0507Coded := by decide +kernel
theorem atom0507Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) := by
  have h := atom0507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0508 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0508 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0508 = ((g 1) * (g 1) * (g 2)) := by
  norm_num [atom0508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0508_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43587815040000 : Int) atom0508) := by
  rw [SparsePolynomial.eval_scale, eval_atom0508]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0508Coded : CoefficientMerge.Poly := [(nat_lit 602, Int.ofNat (nat_lit 1))]
theorem atom0508Coded_decode : atom0508 = SparsePolynomial.decodeCubic 24 atom0508Coded := by decide +kernel
theorem atom0508Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded) := by
  have h := atom0508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0509 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0509 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0509 = ((g 1) * (g 1) * (g 3)) := by
  norm_num [atom0509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0509_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38442326630400 : Int) atom0509) := by
  rw [SparsePolynomial.eval_scale, eval_atom0509]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0509Coded : CoefficientMerge.Poly := [(nat_lit 603, Int.ofNat (nat_lit 1))]
theorem atom0509Coded_decode : atom0509 = SparsePolynomial.decodeCubic 24 atom0509Coded := by decide +kernel
theorem atom0509Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) := by
  have h := atom0509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0510 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0510 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0510 = ((g 1) * (g 1) * (g 4)) := by
  norm_num [atom0510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0510_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33296838220800 : Int) atom0510) := by
  rw [SparsePolynomial.eval_scale, eval_atom0510]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0510Coded : CoefficientMerge.Poly := [(nat_lit 604, Int.ofNat (nat_lit 1))]
theorem atom0510Coded_decode : atom0510 = SparsePolynomial.decodeCubic 24 atom0510Coded := by decide +kernel
theorem atom0510Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded) := by
  have h := atom0510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0511 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0511 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0511 = ((g 1) * (g 1) * (g 5)) := by
  norm_num [atom0511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0511_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35034243552000 : Int) atom0511) := by
  rw [SparsePolynomial.eval_scale, eval_atom0511]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0511Coded : CoefficientMerge.Poly := [(nat_lit 605, Int.ofNat (nat_lit 1))]
theorem atom0511Coded_decode : atom0511 = SparsePolynomial.decodeCubic 24 atom0511Coded := by decide +kernel
theorem atom0511Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) := by
  have h := atom0511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0512 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0512 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0512 = ((g 1) * (g 1) * (g 6)) := by
  norm_num [atom0512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0512_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23005861401600 : Int) atom0512) := by
  rw [SparsePolynomial.eval_scale, eval_atom0512]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0512Coded : CoefficientMerge.Poly := [(nat_lit 606, Int.ofNat (nat_lit 1))]
theorem atom0512Coded_decode : atom0512 = SparsePolynomial.decodeCubic 24 atom0512Coded := by decide +kernel
theorem atom0512Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) := by
  have h := atom0512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0513 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0513 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0513 = ((g 1) * (g 1) * (g 7)) := by
  norm_num [atom0513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0513_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17860372992000 : Int) atom0513) := by
  rw [SparsePolynomial.eval_scale, eval_atom0513]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0513Coded : CoefficientMerge.Poly := [(nat_lit 607, Int.ofNat (nat_lit 1))]
theorem atom0513Coded_decode : atom0513 = SparsePolynomial.decodeCubic 24 atom0513Coded := by decide +kernel
theorem atom0513Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded) := by
  have h := atom0513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0514 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0514 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0514 = ((g 1) * (g 1) * (g 8)) := by
  norm_num [atom0514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0514_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12714884582400 : Int) atom0514) := by
  rw [SparsePolynomial.eval_scale, eval_atom0514]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0514Coded : CoefficientMerge.Poly := [(nat_lit 608, Int.ofNat (nat_lit 1))]
theorem atom0514Coded_decode : atom0514 = SparsePolynomial.decodeCubic 24 atom0514Coded := by decide +kernel
theorem atom0514Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) := by
  have h := atom0514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0515 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0515 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0515 = ((g 1) * (g 1) * (g 9)) := by
  norm_num [atom0515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0515_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13581177218928 : Int) atom0515) := by
  rw [SparsePolynomial.eval_scale, eval_atom0515]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0515Coded : CoefficientMerge.Poly := [(nat_lit 609, Int.ofNat (nat_lit 1))]
theorem atom0515Coded_decode : atom0515 = SparsePolynomial.decodeCubic 24 atom0515Coded := by decide +kernel
theorem atom0515Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded) := by
  have h := atom0515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0516 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0516 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0516 = ((g 1) * (g 1) * (g 10)) := by
  norm_num [atom0516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0516_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26079185843568 : Int) atom0516) := by
  rw [SparsePolynomial.eval_scale, eval_atom0516]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0516Coded : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 1))]
theorem atom0516Coded_decode : atom0516 = SparsePolynomial.decodeCubic 24 atom0516Coded := by decide +kernel
theorem atom0516Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) := by
  have h := atom0516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0517 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0517 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0517 = ((g 1) * (g 1) * (g 11)) := by
  norm_num [atom0517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0517_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36938767228704 : Int) atom0517) := by
  rw [SparsePolynomial.eval_scale, eval_atom0517]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0517Coded : CoefficientMerge.Poly := [(nat_lit 611, Int.ofNat (nat_lit 1))]
theorem atom0517Coded_decode : atom0517 = SparsePolynomial.decodeCubic 24 atom0517Coded := by decide +kernel
theorem atom0517Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) := by
  have h := atom0517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0518 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0518 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0518 = ((g 1) * (g 1) * (g 12)) := by
  norm_num [atom0518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0518_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59715261042624 : Int) atom0518) := by
  rw [SparsePolynomial.eval_scale, eval_atom0518]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0518Coded : CoefficientMerge.Poly := [(nat_lit 612, Int.ofNat (nat_lit 1))]
theorem atom0518Coded_decode : atom0518 = SparsePolynomial.decodeCubic 24 atom0518Coded := by decide +kernel
theorem atom0518Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded) := by
  have h := atom0518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0519 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0519 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0519 = ((g 1) * (g 1) * (g 13)) := by
  norm_num [atom0519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0519_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45908642102400 : Int) atom0519) := by
  rw [SparsePolynomial.eval_scale, eval_atom0519]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0519Coded : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 1))]
theorem atom0519Coded_decode : atom0519 = SparsePolynomial.decodeCubic 24 atom0519Coded := by decide +kernel
theorem atom0519Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) := by
  have h := atom0519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0520 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0520 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0520 = ((g 1) * (g 1) * (g 14)) := by
  norm_num [atom0520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0520_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28427760345600 : Int) atom0520) := by
  rw [SparsePolynomial.eval_scale, eval_atom0520]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0520Coded : CoefficientMerge.Poly := [(nat_lit 614, Int.ofNat (nat_lit 1))]
theorem atom0520Coded_decode : atom0520 = SparsePolynomial.decodeCubic 24 atom0520Coded := by decide +kernel
theorem atom0520Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded) := by
  have h := atom0520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0521 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0521 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0521 = ((g 1) * (g 1) * (g 15)) := by
  norm_num [atom0521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0521_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25733885184000 : Int) atom0521) := by
  rw [SparsePolynomial.eval_scale, eval_atom0521]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0521Coded : CoefficientMerge.Poly := [(nat_lit 615, Int.ofNat (nat_lit 1))]
theorem atom0521Coded_decode : atom0521 = SparsePolynomial.decodeCubic 24 atom0521Coded := by decide +kernel
theorem atom0521Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) := by
  have h := atom0521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0522 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0522 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0522 = ((g 1) * (g 1) * (g 16)) := by
  norm_num [atom0522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0522_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11217499776000 : Int) atom0522) := by
  rw [SparsePolynomial.eval_scale, eval_atom0522]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0522Coded : CoefficientMerge.Poly := [(nat_lit 616, Int.ofNat (nat_lit 1))]
theorem atom0522Coded_decode : atom0522 = SparsePolynomial.decodeCubic 24 atom0522Coded := by decide +kernel
theorem atom0522Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) := by
  have h := atom0522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0523 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0523 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0523 = ((g 1) * (g 1) * (g 17)) := by
  norm_num [atom0523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0523_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6633852825600 : Int) atom0523) := by
  rw [SparsePolynomial.eval_scale, eval_atom0523]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0523Coded : CoefficientMerge.Poly := [(nat_lit 617, Int.ofNat (nat_lit 1))]
theorem atom0523Coded_decode : atom0523 = SparsePolynomial.decodeCubic 24 atom0523Coded := by decide +kernel
theorem atom0523Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded) := by
  have h := atom0523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0524 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0524 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0524 = ((g 1) * (g 1) * (g 18)) := by
  norm_num [atom0524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0524_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29512140134400 : Int) atom0524) := by
  rw [SparsePolynomial.eval_scale, eval_atom0524]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 1) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0524Coded : CoefficientMerge.Poly := [(nat_lit 618, Int.ofNat (nat_lit 1))]
theorem atom0524Coded_decode : atom0524 = SparsePolynomial.decodeCubic 24 atom0524Coded := by decide +kernel
theorem atom0524Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) := by
  have h := atom0524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0525 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 1, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0525 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0525 = ((g 1) * (g 1) * (g 20)) := by
  norm_num [atom0525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0525_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6208605849600 : Int) atom0525) := by
  rw [SparsePolynomial.eval_scale, eval_atom0525]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 1) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0525Coded : CoefficientMerge.Poly := [(nat_lit 620, Int.ofNat (nat_lit 1))]
theorem atom0525Coded_decode : atom0525 = SparsePolynomial.decodeCubic 24 atom0525Coded := by decide +kernel
theorem atom0525Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded) := by
  have h := atom0525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0526 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0526 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0526 = ((g 1) * (g 2) * (g 2)) := by
  norm_num [atom0526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0526_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85347068083200 : Int) atom0526) := by
  rw [SparsePolynomial.eval_scale, eval_atom0526]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0526Coded : CoefficientMerge.Poly := [(nat_lit 626, Int.ofNat (nat_lit 1))]
theorem atom0526Coded_decode : atom0526 = SparsePolynomial.decodeCubic 24 atom0526Coded := by decide +kernel
theorem atom0526Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) := by
  have h := atom0526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0527 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0527 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0527 = ((g 1) * (g 2) * (g 3)) := by
  norm_num [atom0527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0527_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (162444344832000 : Int) atom0527) := by
  rw [SparsePolynomial.eval_scale, eval_atom0527]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0527Coded : CoefficientMerge.Poly := [(nat_lit 627, Int.ofNat (nat_lit 1))]
theorem atom0527Coded_decode : atom0527 = SparsePolynomial.decodeCubic 24 atom0527Coded := by decide +kernel
theorem atom0527Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) := by
  have h := atom0527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0528 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0528 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0528 = ((g 1) * (g 2) * (g 4)) := by
  norm_num [atom0528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0528_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154194553497600 : Int) atom0528) := by
  rw [SparsePolynomial.eval_scale, eval_atom0528]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0528Coded : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 1))]
theorem atom0528Coded_decode : atom0528 = SparsePolynomial.decodeCubic 24 atom0528Coded := by decide +kernel
theorem atom0528Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded) := by
  have h := atom0528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block008 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 280362100233600)), (nat_lit 332, Int.ofNat (nat_lit 283858818566400)), (nat_lit 333, Int.ofNat (nat_lit 220539543840000)), (nat_lit 334, Int.ofNat (nat_lit 165174808478400)), (nat_lit 335, Int.ofNat (nat_lit 153751952692800)), (nat_lit 350, Int.ofNat (nat_lit 180207265392000)), (nat_lit 351, Int.ofNat (nat_lit 326270355747840)), (nat_lit 352, Int.ofNat (nat_lit 298937896306560)), (nat_lit 353, Int.ofNat (nat_lit 297051845428800)), (nat_lit 354, Int.ofNat (nat_lit 320423596416000)), (nat_lit 355, Int.ofNat (nat_lit 262910161067400)), (nat_lit 356, Int.ofNat (nat_lit 266247131673600)), (nat_lit 357, Int.ofNat (nat_lit 203948449689600)), (nat_lit 358, Int.ofNat (nat_lit 163012699899000)), (nat_lit 359, Int.ofNat (nat_lit 150660684682200)), (nat_lit 375, Int.ofNat (nat_lit 185418634867200)), (nat_lit 376, Int.ofNat (nat_lit 335715348810240)), (nat_lit 377, Int.ofNat (nat_lit 309666780864000)), (nat_lit 378, Int.ofNat (nat_lit 331449735052800)), (nat_lit 379, Int.ofNat (nat_lit 269855932147200)), (nat_lit 380, Int.ofNat (nat_lit 278367314803200)), (nat_lit 381, Int.ofNat (nat_lit 216773511897600)), (nat_lit 382, Int.ofNat (nat_lit 154848692880000)), (nat_lit 383, Int.ofNat (nat_lit 139633710451200)), (nat_lit 400, Int.ofNat (nat_lit 190423018598400)), (nat_lit 401, Int.ofNat (nat_lit 337110459571200)), (nat_lit 402, Int.ofNat (nat_lit 339520246128000)), (nat_lit 403, Int.ofNat (nat_lit 272720067177600)), (nat_lit 404, Int.ofNat (nat_lit 269798105001600)), (nat_lit 405, Int.ofNat (nat_lit 202997926051200)), (nat_lit 406, Int.ofNat (nat_lit 129247858454400)), (nat_lit 407, Int.ofNat (nat_lit 121733228937600)), (nat_lit 425, Int.ofNat (nat_lit 187597703462400)), (nat_lit 426, Int.ofNat (nat_lit 350073941817600)), (nat_lit 427, Int.ofNat (nat_lit 283033756051200)), (nat_lit 428, Int.ofNat (nat_lit 278611187500800)), (nat_lit 429, Int.ofNat (nat_lit 211571001734400)), (nat_lit 430, Int.ofNat (nat_lit 135196644844800)), (nat_lit 431, Int.ofNat (nat_lit 126181408953600)), (nat_lit 450, Int.ofNat (nat_lit 194082719846400)), (nat_lit 451, Int.ofNat (nat_lit 329949128678400)), (nat_lit 452, Int.ofNat (nat_lit 342153716889600)), (nat_lit 453, Int.ofNat (nat_lit 283937405875200)), (nat_lit 454, Int.ofNat (nat_lit 163805135155200)), (nat_lit 455, Int.ofNat (nat_lit 171417056025600)), (nat_lit 475, Int.ofNat (nat_lit 137682213419520)), (nat_lit 476, Int.ofNat (nat_lit 278791917465600)), (nat_lit 477, Int.ofNat (nat_lit 292017098419200)), (nat_lit 478, Int.ofNat (nat_lit 172905420441600)), (nat_lit 479, Int.ofNat (nat_lit 181537934054400)), (nat_lit 500, Int.ofNat (nat_lit 142925508633600)), (nat_lit 501, Int.ofNat (nat_lit 300096790963200)), (nat_lit 502, Int.ofNat (nat_lit 182005705728000)), (nat_lit 503, Int.ofNat (nat_lit 167207110963200)), (nat_lit 525, Int.ofNat (nat_lit 154088241753600)), (nat_lit 526, Int.ofNat (nat_lit 191105991014400)), (nat_lit 527, Int.ofNat (nat_lit 177327988992000)), (nat_lit 550, Int.ofNat (nat_lit 22316002884000)), (nat_lit 551, Int.ofNat (nat_lit 35848320076800)), (nat_lit 602, Int.ofNat (nat_lit 43587815040000)), (nat_lit 603, Int.ofNat (nat_lit 38442326630400)), (nat_lit 604, Int.ofNat (nat_lit 33296838220800)), (nat_lit 605, Int.ofNat (nat_lit 35034243552000)), (nat_lit 606, Int.ofNat (nat_lit 23005861401600)), (nat_lit 607, Int.ofNat (nat_lit 17860372992000)), (nat_lit 608, Int.ofNat (nat_lit 12714884582400)), (nat_lit 609, Int.ofNat (nat_lit 13581177218928)), (nat_lit 610, Int.ofNat (nat_lit 26079185843568)), (nat_lit 611, Int.ofNat (nat_lit 36938767228704)), (nat_lit 612, Int.ofNat (nat_lit 59715261042624)), (nat_lit 613, Int.ofNat (nat_lit 45908642102400)), (nat_lit 614, Int.ofNat (nat_lit 28427760345600)), (nat_lit 615, Int.ofNat (nat_lit 25733885184000)), (nat_lit 616, Int.ofNat (nat_lit 11217499776000)), (nat_lit 617, Int.ofNat (nat_lit 6633852825600)), (nat_lit 618, Int.ofNat (nat_lit 29512140134400)), (nat_lit 620, Int.ofNat (nat_lit 6208605849600)), (nat_lit 626, Int.ofNat (nat_lit 85347068083200)), (nat_lit 627, Int.ofNat (nat_lit 162444344832000)), (nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
def block008_data_flat000 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 280362100233600))]
theorem block008_data_flat000_step : block008_data_flat000 = (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) := by decide +kernel
theorem block008_data_flat000_original : block008_data_flat000 = (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) := by
  rw [block008_data_flat000_step]
def block008_data_flat001 : CoefficientMerge.Poly := [(nat_lit 332, Int.ofNat (nat_lit 283858818566400))]
theorem block008_data_flat001_step : block008_data_flat001 = (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded) := by decide +kernel
theorem block008_data_flat001_original : block008_data_flat001 = (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded) := by
  rw [block008_data_flat001_step]
def block008_data_flat002 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 280362100233600)), (nat_lit 332, Int.ofNat (nat_lit 283858818566400))]
theorem block008_data_flat002_step : block008_data_flat002 = (CoefficientMerge.fastMerge block008_data_flat000 block008_data_flat001) := by decide +kernel
theorem block008_data_flat002_original : block008_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded)) := by
  rw [block008_data_flat002_step, block008_data_flat000_original, block008_data_flat001_original]
def block008_data_flat003 : CoefficientMerge.Poly := [(nat_lit 333, Int.ofNat (nat_lit 220539543840000))]
theorem block008_data_flat003_step : block008_data_flat003 = (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) := by decide +kernel
theorem block008_data_flat003_original : block008_data_flat003 = (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) := by
  rw [block008_data_flat003_step]
def block008_data_flat004 : CoefficientMerge.Poly := [(nat_lit 334, Int.ofNat (nat_lit 165174808478400))]
theorem block008_data_flat004_step : block008_data_flat004 = (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) := by decide +kernel
theorem block008_data_flat004_original : block008_data_flat004 = (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) := by
  rw [block008_data_flat004_step]
def block008_data_flat005 : CoefficientMerge.Poly := [(nat_lit 335, Int.ofNat (nat_lit 153751952692800))]
theorem block008_data_flat005_step : block008_data_flat005 = (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded) := by decide +kernel
theorem block008_data_flat005_original : block008_data_flat005 = (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded) := by
  rw [block008_data_flat005_step]
def block008_data_flat006 : CoefficientMerge.Poly := [(nat_lit 334, Int.ofNat (nat_lit 165174808478400)), (nat_lit 335, Int.ofNat (nat_lit 153751952692800))]
theorem block008_data_flat006_step : block008_data_flat006 = (CoefficientMerge.fastMerge block008_data_flat004 block008_data_flat005) := by decide +kernel
theorem block008_data_flat006_original : block008_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded)) := by
  rw [block008_data_flat006_step, block008_data_flat004_original, block008_data_flat005_original]
def block008_data_flat007 : CoefficientMerge.Poly := [(nat_lit 333, Int.ofNat (nat_lit 220539543840000)), (nat_lit 334, Int.ofNat (nat_lit 165174808478400)), (nat_lit 335, Int.ofNat (nat_lit 153751952692800))]
theorem block008_data_flat007_step : block008_data_flat007 = (CoefficientMerge.fastMerge block008_data_flat003 block008_data_flat006) := by decide +kernel
theorem block008_data_flat007_original : block008_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded))) := by
  rw [block008_data_flat007_step, block008_data_flat003_original, block008_data_flat006_original]
def block008_data_flat008 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 280362100233600)), (nat_lit 332, Int.ofNat (nat_lit 283858818566400)), (nat_lit 333, Int.ofNat (nat_lit 220539543840000)), (nat_lit 334, Int.ofNat (nat_lit 165174808478400)), (nat_lit 335, Int.ofNat (nat_lit 153751952692800))]
theorem block008_data_flat008_step : block008_data_flat008 = (CoefficientMerge.fastMerge block008_data_flat002 block008_data_flat007) := by decide +kernel
theorem block008_data_flat008_original : block008_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded)))) := by
  rw [block008_data_flat008_step, block008_data_flat002_original, block008_data_flat007_original]
def block008_data_flat009 : CoefficientMerge.Poly := [(nat_lit 350, Int.ofNat (nat_lit 180207265392000))]
theorem block008_data_flat009_step : block008_data_flat009 = (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) := by decide +kernel
theorem block008_data_flat009_original : block008_data_flat009 = (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) := by
  rw [block008_data_flat009_step]
def block008_data_flat010 : CoefficientMerge.Poly := [(nat_lit 351, Int.ofNat (nat_lit 326270355747840))]
theorem block008_data_flat010_step : block008_data_flat010 = (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded) := by decide +kernel
theorem block008_data_flat010_original : block008_data_flat010 = (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded) := by
  rw [block008_data_flat010_step]
def block008_data_flat011 : CoefficientMerge.Poly := [(nat_lit 350, Int.ofNat (nat_lit 180207265392000)), (nat_lit 351, Int.ofNat (nat_lit 326270355747840))]
theorem block008_data_flat011_step : block008_data_flat011 = (CoefficientMerge.fastMerge block008_data_flat009 block008_data_flat010) := by decide +kernel
theorem block008_data_flat011_original : block008_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded)) := by
  rw [block008_data_flat011_step, block008_data_flat009_original, block008_data_flat010_original]
def block008_data_flat012 : CoefficientMerge.Poly := [(nat_lit 352, Int.ofNat (nat_lit 298937896306560))]
theorem block008_data_flat012_step : block008_data_flat012 = (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) := by decide +kernel
theorem block008_data_flat012_original : block008_data_flat012 = (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) := by
  rw [block008_data_flat012_step]
def block008_data_flat013 : CoefficientMerge.Poly := [(nat_lit 353, Int.ofNat (nat_lit 297051845428800))]
theorem block008_data_flat013_step : block008_data_flat013 = (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) := by decide +kernel
theorem block008_data_flat013_original : block008_data_flat013 = (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) := by
  rw [block008_data_flat013_step]
def block008_data_flat014 : CoefficientMerge.Poly := [(nat_lit 354, Int.ofNat (nat_lit 320423596416000))]
theorem block008_data_flat014_step : block008_data_flat014 = (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded) := by decide +kernel
theorem block008_data_flat014_original : block008_data_flat014 = (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded) := by
  rw [block008_data_flat014_step]
def block008_data_flat015 : CoefficientMerge.Poly := [(nat_lit 353, Int.ofNat (nat_lit 297051845428800)), (nat_lit 354, Int.ofNat (nat_lit 320423596416000))]
theorem block008_data_flat015_step : block008_data_flat015 = (CoefficientMerge.fastMerge block008_data_flat013 block008_data_flat014) := by decide +kernel
theorem block008_data_flat015_original : block008_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded)) := by
  rw [block008_data_flat015_step, block008_data_flat013_original, block008_data_flat014_original]
def block008_data_flat016 : CoefficientMerge.Poly := [(nat_lit 352, Int.ofNat (nat_lit 298937896306560)), (nat_lit 353, Int.ofNat (nat_lit 297051845428800)), (nat_lit 354, Int.ofNat (nat_lit 320423596416000))]
theorem block008_data_flat016_step : block008_data_flat016 = (CoefficientMerge.fastMerge block008_data_flat012 block008_data_flat015) := by decide +kernel
theorem block008_data_flat016_original : block008_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded))) := by
  rw [block008_data_flat016_step, block008_data_flat012_original, block008_data_flat015_original]
def block008_data_flat017 : CoefficientMerge.Poly := [(nat_lit 350, Int.ofNat (nat_lit 180207265392000)), (nat_lit 351, Int.ofNat (nat_lit 326270355747840)), (nat_lit 352, Int.ofNat (nat_lit 298937896306560)), (nat_lit 353, Int.ofNat (nat_lit 297051845428800)), (nat_lit 354, Int.ofNat (nat_lit 320423596416000))]
theorem block008_data_flat017_step : block008_data_flat017 = (CoefficientMerge.fastMerge block008_data_flat011 block008_data_flat016) := by decide +kernel
theorem block008_data_flat017_original : block008_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded)))) := by
  rw [block008_data_flat017_step, block008_data_flat011_original, block008_data_flat016_original]
def block008_data_flat018 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 280362100233600)), (nat_lit 332, Int.ofNat (nat_lit 283858818566400)), (nat_lit 333, Int.ofNat (nat_lit 220539543840000)), (nat_lit 334, Int.ofNat (nat_lit 165174808478400)), (nat_lit 335, Int.ofNat (nat_lit 153751952692800)), (nat_lit 350, Int.ofNat (nat_lit 180207265392000)), (nat_lit 351, Int.ofNat (nat_lit 326270355747840)), (nat_lit 352, Int.ofNat (nat_lit 298937896306560)), (nat_lit 353, Int.ofNat (nat_lit 297051845428800)), (nat_lit 354, Int.ofNat (nat_lit 320423596416000))]
theorem block008_data_flat018_step : block008_data_flat018 = (CoefficientMerge.fastMerge block008_data_flat008 block008_data_flat017) := by decide +kernel
theorem block008_data_flat018_original : block008_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded))))) := by
  rw [block008_data_flat018_step, block008_data_flat008_original, block008_data_flat017_original]
def block008_data_flat019 : CoefficientMerge.Poly := [(nat_lit 355, Int.ofNat (nat_lit 262910161067400))]
theorem block008_data_flat019_step : block008_data_flat019 = (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) := by decide +kernel
theorem block008_data_flat019_original : block008_data_flat019 = (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) := by
  rw [block008_data_flat019_step]
def block008_data_flat020 : CoefficientMerge.Poly := [(nat_lit 356, Int.ofNat (nat_lit 266247131673600))]
theorem block008_data_flat020_step : block008_data_flat020 = (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded) := by decide +kernel
theorem block008_data_flat020_original : block008_data_flat020 = (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded) := by
  rw [block008_data_flat020_step]
def block008_data_flat021 : CoefficientMerge.Poly := [(nat_lit 355, Int.ofNat (nat_lit 262910161067400)), (nat_lit 356, Int.ofNat (nat_lit 266247131673600))]
theorem block008_data_flat021_step : block008_data_flat021 = (CoefficientMerge.fastMerge block008_data_flat019 block008_data_flat020) := by decide +kernel
theorem block008_data_flat021_original : block008_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded)) := by
  rw [block008_data_flat021_step, block008_data_flat019_original, block008_data_flat020_original]
def block008_data_flat022 : CoefficientMerge.Poly := [(nat_lit 357, Int.ofNat (nat_lit 203948449689600))]
theorem block008_data_flat022_step : block008_data_flat022 = (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) := by decide +kernel
theorem block008_data_flat022_original : block008_data_flat022 = (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) := by
  rw [block008_data_flat022_step]
def block008_data_flat023 : CoefficientMerge.Poly := [(nat_lit 358, Int.ofNat (nat_lit 163012699899000))]
theorem block008_data_flat023_step : block008_data_flat023 = (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) := by decide +kernel
theorem block008_data_flat023_original : block008_data_flat023 = (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) := by
  rw [block008_data_flat023_step]
def block008_data_flat024 : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 150660684682200))]
theorem block008_data_flat024_step : block008_data_flat024 = (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded) := by decide +kernel
theorem block008_data_flat024_original : block008_data_flat024 = (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded) := by
  rw [block008_data_flat024_step]
def block008_data_flat025 : CoefficientMerge.Poly := [(nat_lit 358, Int.ofNat (nat_lit 163012699899000)), (nat_lit 359, Int.ofNat (nat_lit 150660684682200))]
theorem block008_data_flat025_step : block008_data_flat025 = (CoefficientMerge.fastMerge block008_data_flat023 block008_data_flat024) := by decide +kernel
theorem block008_data_flat025_original : block008_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded)) := by
  rw [block008_data_flat025_step, block008_data_flat023_original, block008_data_flat024_original]
def block008_data_flat026 : CoefficientMerge.Poly := [(nat_lit 357, Int.ofNat (nat_lit 203948449689600)), (nat_lit 358, Int.ofNat (nat_lit 163012699899000)), (nat_lit 359, Int.ofNat (nat_lit 150660684682200))]
theorem block008_data_flat026_step : block008_data_flat026 = (CoefficientMerge.fastMerge block008_data_flat022 block008_data_flat025) := by decide +kernel
theorem block008_data_flat026_original : block008_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded))) := by
  rw [block008_data_flat026_step, block008_data_flat022_original, block008_data_flat025_original]
def block008_data_flat027 : CoefficientMerge.Poly := [(nat_lit 355, Int.ofNat (nat_lit 262910161067400)), (nat_lit 356, Int.ofNat (nat_lit 266247131673600)), (nat_lit 357, Int.ofNat (nat_lit 203948449689600)), (nat_lit 358, Int.ofNat (nat_lit 163012699899000)), (nat_lit 359, Int.ofNat (nat_lit 150660684682200))]
theorem block008_data_flat027_step : block008_data_flat027 = (CoefficientMerge.fastMerge block008_data_flat021 block008_data_flat026) := by decide +kernel
theorem block008_data_flat027_original : block008_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded)))) := by
  rw [block008_data_flat027_step, block008_data_flat021_original, block008_data_flat026_original]
def block008_data_flat028 : CoefficientMerge.Poly := [(nat_lit 375, Int.ofNat (nat_lit 185418634867200))]
theorem block008_data_flat028_step : block008_data_flat028 = (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) := by decide +kernel
theorem block008_data_flat028_original : block008_data_flat028 = (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) := by
  rw [block008_data_flat028_step]
def block008_data_flat029 : CoefficientMerge.Poly := [(nat_lit 376, Int.ofNat (nat_lit 335715348810240))]
theorem block008_data_flat029_step : block008_data_flat029 = (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded) := by decide +kernel
theorem block008_data_flat029_original : block008_data_flat029 = (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded) := by
  rw [block008_data_flat029_step]
def block008_data_flat030 : CoefficientMerge.Poly := [(nat_lit 375, Int.ofNat (nat_lit 185418634867200)), (nat_lit 376, Int.ofNat (nat_lit 335715348810240))]
theorem block008_data_flat030_step : block008_data_flat030 = (CoefficientMerge.fastMerge block008_data_flat028 block008_data_flat029) := by decide +kernel
theorem block008_data_flat030_original : block008_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded)) := by
  rw [block008_data_flat030_step, block008_data_flat028_original, block008_data_flat029_original]
def block008_data_flat031 : CoefficientMerge.Poly := [(nat_lit 377, Int.ofNat (nat_lit 309666780864000))]
theorem block008_data_flat031_step : block008_data_flat031 = (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) := by decide +kernel
theorem block008_data_flat031_original : block008_data_flat031 = (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) := by
  rw [block008_data_flat031_step]
def block008_data_flat032 : CoefficientMerge.Poly := [(nat_lit 378, Int.ofNat (nat_lit 331449735052800))]
theorem block008_data_flat032_step : block008_data_flat032 = (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) := by decide +kernel
theorem block008_data_flat032_original : block008_data_flat032 = (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) := by
  rw [block008_data_flat032_step]
def block008_data_flat033 : CoefficientMerge.Poly := [(nat_lit 379, Int.ofNat (nat_lit 269855932147200))]
theorem block008_data_flat033_step : block008_data_flat033 = (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded) := by decide +kernel
theorem block008_data_flat033_original : block008_data_flat033 = (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded) := by
  rw [block008_data_flat033_step]
def block008_data_flat034 : CoefficientMerge.Poly := [(nat_lit 378, Int.ofNat (nat_lit 331449735052800)), (nat_lit 379, Int.ofNat (nat_lit 269855932147200))]
theorem block008_data_flat034_step : block008_data_flat034 = (CoefficientMerge.fastMerge block008_data_flat032 block008_data_flat033) := by decide +kernel
theorem block008_data_flat034_original : block008_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded)) := by
  rw [block008_data_flat034_step, block008_data_flat032_original, block008_data_flat033_original]
def block008_data_flat035 : CoefficientMerge.Poly := [(nat_lit 377, Int.ofNat (nat_lit 309666780864000)), (nat_lit 378, Int.ofNat (nat_lit 331449735052800)), (nat_lit 379, Int.ofNat (nat_lit 269855932147200))]
theorem block008_data_flat035_step : block008_data_flat035 = (CoefficientMerge.fastMerge block008_data_flat031 block008_data_flat034) := by decide +kernel
theorem block008_data_flat035_original : block008_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded))) := by
  rw [block008_data_flat035_step, block008_data_flat031_original, block008_data_flat034_original]
def block008_data_flat036 : CoefficientMerge.Poly := [(nat_lit 375, Int.ofNat (nat_lit 185418634867200)), (nat_lit 376, Int.ofNat (nat_lit 335715348810240)), (nat_lit 377, Int.ofNat (nat_lit 309666780864000)), (nat_lit 378, Int.ofNat (nat_lit 331449735052800)), (nat_lit 379, Int.ofNat (nat_lit 269855932147200))]
theorem block008_data_flat036_step : block008_data_flat036 = (CoefficientMerge.fastMerge block008_data_flat030 block008_data_flat035) := by decide +kernel
theorem block008_data_flat036_original : block008_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded)))) := by
  rw [block008_data_flat036_step, block008_data_flat030_original, block008_data_flat035_original]
def block008_data_flat037 : CoefficientMerge.Poly := [(nat_lit 355, Int.ofNat (nat_lit 262910161067400)), (nat_lit 356, Int.ofNat (nat_lit 266247131673600)), (nat_lit 357, Int.ofNat (nat_lit 203948449689600)), (nat_lit 358, Int.ofNat (nat_lit 163012699899000)), (nat_lit 359, Int.ofNat (nat_lit 150660684682200)), (nat_lit 375, Int.ofNat (nat_lit 185418634867200)), (nat_lit 376, Int.ofNat (nat_lit 335715348810240)), (nat_lit 377, Int.ofNat (nat_lit 309666780864000)), (nat_lit 378, Int.ofNat (nat_lit 331449735052800)), (nat_lit 379, Int.ofNat (nat_lit 269855932147200))]
theorem block008_data_flat037_step : block008_data_flat037 = (CoefficientMerge.fastMerge block008_data_flat027 block008_data_flat036) := by decide +kernel
theorem block008_data_flat037_original : block008_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded))))) := by
  rw [block008_data_flat037_step, block008_data_flat027_original, block008_data_flat036_original]
def block008_data_flat038 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 280362100233600)), (nat_lit 332, Int.ofNat (nat_lit 283858818566400)), (nat_lit 333, Int.ofNat (nat_lit 220539543840000)), (nat_lit 334, Int.ofNat (nat_lit 165174808478400)), (nat_lit 335, Int.ofNat (nat_lit 153751952692800)), (nat_lit 350, Int.ofNat (nat_lit 180207265392000)), (nat_lit 351, Int.ofNat (nat_lit 326270355747840)), (nat_lit 352, Int.ofNat (nat_lit 298937896306560)), (nat_lit 353, Int.ofNat (nat_lit 297051845428800)), (nat_lit 354, Int.ofNat (nat_lit 320423596416000)), (nat_lit 355, Int.ofNat (nat_lit 262910161067400)), (nat_lit 356, Int.ofNat (nat_lit 266247131673600)), (nat_lit 357, Int.ofNat (nat_lit 203948449689600)), (nat_lit 358, Int.ofNat (nat_lit 163012699899000)), (nat_lit 359, Int.ofNat (nat_lit 150660684682200)), (nat_lit 375, Int.ofNat (nat_lit 185418634867200)), (nat_lit 376, Int.ofNat (nat_lit 335715348810240)), (nat_lit 377, Int.ofNat (nat_lit 309666780864000)), (nat_lit 378, Int.ofNat (nat_lit 331449735052800)), (nat_lit 379, Int.ofNat (nat_lit 269855932147200))]
theorem block008_data_flat038_step : block008_data_flat038 = (CoefficientMerge.fastMerge block008_data_flat018 block008_data_flat037) := by decide +kernel
theorem block008_data_flat038_original : block008_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded)))))) := by
  rw [block008_data_flat038_step, block008_data_flat018_original, block008_data_flat037_original]
def block008_data_flat039 : CoefficientMerge.Poly := [(nat_lit 380, Int.ofNat (nat_lit 278367314803200))]
theorem block008_data_flat039_step : block008_data_flat039 = (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) := by decide +kernel
theorem block008_data_flat039_original : block008_data_flat039 = (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) := by
  rw [block008_data_flat039_step]
def block008_data_flat040 : CoefficientMerge.Poly := [(nat_lit 381, Int.ofNat (nat_lit 216773511897600))]
theorem block008_data_flat040_step : block008_data_flat040 = (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded) := by decide +kernel
theorem block008_data_flat040_original : block008_data_flat040 = (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded) := by
  rw [block008_data_flat040_step]
def block008_data_flat041 : CoefficientMerge.Poly := [(nat_lit 380, Int.ofNat (nat_lit 278367314803200)), (nat_lit 381, Int.ofNat (nat_lit 216773511897600))]
theorem block008_data_flat041_step : block008_data_flat041 = (CoefficientMerge.fastMerge block008_data_flat039 block008_data_flat040) := by decide +kernel
theorem block008_data_flat041_original : block008_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded)) := by
  rw [block008_data_flat041_step, block008_data_flat039_original, block008_data_flat040_original]
def block008_data_flat042 : CoefficientMerge.Poly := [(nat_lit 382, Int.ofNat (nat_lit 154848692880000))]
theorem block008_data_flat042_step : block008_data_flat042 = (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) := by decide +kernel
theorem block008_data_flat042_original : block008_data_flat042 = (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) := by
  rw [block008_data_flat042_step]
def block008_data_flat043 : CoefficientMerge.Poly := [(nat_lit 383, Int.ofNat (nat_lit 139633710451200))]
theorem block008_data_flat043_step : block008_data_flat043 = (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) := by decide +kernel
theorem block008_data_flat043_original : block008_data_flat043 = (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) := by
  rw [block008_data_flat043_step]
def block008_data_flat044 : CoefficientMerge.Poly := [(nat_lit 400, Int.ofNat (nat_lit 190423018598400))]
theorem block008_data_flat044_step : block008_data_flat044 = (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded) := by decide +kernel
theorem block008_data_flat044_original : block008_data_flat044 = (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded) := by
  rw [block008_data_flat044_step]
def block008_data_flat045 : CoefficientMerge.Poly := [(nat_lit 383, Int.ofNat (nat_lit 139633710451200)), (nat_lit 400, Int.ofNat (nat_lit 190423018598400))]
theorem block008_data_flat045_step : block008_data_flat045 = (CoefficientMerge.fastMerge block008_data_flat043 block008_data_flat044) := by decide +kernel
theorem block008_data_flat045_original : block008_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded)) := by
  rw [block008_data_flat045_step, block008_data_flat043_original, block008_data_flat044_original]
def block008_data_flat046 : CoefficientMerge.Poly := [(nat_lit 382, Int.ofNat (nat_lit 154848692880000)), (nat_lit 383, Int.ofNat (nat_lit 139633710451200)), (nat_lit 400, Int.ofNat (nat_lit 190423018598400))]
theorem block008_data_flat046_step : block008_data_flat046 = (CoefficientMerge.fastMerge block008_data_flat042 block008_data_flat045) := by decide +kernel
theorem block008_data_flat046_original : block008_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded))) := by
  rw [block008_data_flat046_step, block008_data_flat042_original, block008_data_flat045_original]
def block008_data_flat047 : CoefficientMerge.Poly := [(nat_lit 380, Int.ofNat (nat_lit 278367314803200)), (nat_lit 381, Int.ofNat (nat_lit 216773511897600)), (nat_lit 382, Int.ofNat (nat_lit 154848692880000)), (nat_lit 383, Int.ofNat (nat_lit 139633710451200)), (nat_lit 400, Int.ofNat (nat_lit 190423018598400))]
theorem block008_data_flat047_step : block008_data_flat047 = (CoefficientMerge.fastMerge block008_data_flat041 block008_data_flat046) := by decide +kernel
theorem block008_data_flat047_original : block008_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded)))) := by
  rw [block008_data_flat047_step, block008_data_flat041_original, block008_data_flat046_original]
def block008_data_flat048 : CoefficientMerge.Poly := [(nat_lit 401, Int.ofNat (nat_lit 337110459571200))]
theorem block008_data_flat048_step : block008_data_flat048 = (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) := by decide +kernel
theorem block008_data_flat048_original : block008_data_flat048 = (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) := by
  rw [block008_data_flat048_step]
def block008_data_flat049 : CoefficientMerge.Poly := [(nat_lit 402, Int.ofNat (nat_lit 339520246128000))]
theorem block008_data_flat049_step : block008_data_flat049 = (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded) := by decide +kernel
theorem block008_data_flat049_original : block008_data_flat049 = (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded) := by
  rw [block008_data_flat049_step]
def block008_data_flat050 : CoefficientMerge.Poly := [(nat_lit 401, Int.ofNat (nat_lit 337110459571200)), (nat_lit 402, Int.ofNat (nat_lit 339520246128000))]
theorem block008_data_flat050_step : block008_data_flat050 = (CoefficientMerge.fastMerge block008_data_flat048 block008_data_flat049) := by decide +kernel
theorem block008_data_flat050_original : block008_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded)) := by
  rw [block008_data_flat050_step, block008_data_flat048_original, block008_data_flat049_original]
def block008_data_flat051 : CoefficientMerge.Poly := [(nat_lit 403, Int.ofNat (nat_lit 272720067177600))]
theorem block008_data_flat051_step : block008_data_flat051 = (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) := by decide +kernel
theorem block008_data_flat051_original : block008_data_flat051 = (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) := by
  rw [block008_data_flat051_step]
def block008_data_flat052 : CoefficientMerge.Poly := [(nat_lit 404, Int.ofNat (nat_lit 269798105001600))]
theorem block008_data_flat052_step : block008_data_flat052 = (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) := by decide +kernel
theorem block008_data_flat052_original : block008_data_flat052 = (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) := by
  rw [block008_data_flat052_step]
def block008_data_flat053 : CoefficientMerge.Poly := [(nat_lit 405, Int.ofNat (nat_lit 202997926051200))]
theorem block008_data_flat053_step : block008_data_flat053 = (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded) := by decide +kernel
theorem block008_data_flat053_original : block008_data_flat053 = (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded) := by
  rw [block008_data_flat053_step]
def block008_data_flat054 : CoefficientMerge.Poly := [(nat_lit 404, Int.ofNat (nat_lit 269798105001600)), (nat_lit 405, Int.ofNat (nat_lit 202997926051200))]
theorem block008_data_flat054_step : block008_data_flat054 = (CoefficientMerge.fastMerge block008_data_flat052 block008_data_flat053) := by decide +kernel
theorem block008_data_flat054_original : block008_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded)) := by
  rw [block008_data_flat054_step, block008_data_flat052_original, block008_data_flat053_original]
def block008_data_flat055 : CoefficientMerge.Poly := [(nat_lit 403, Int.ofNat (nat_lit 272720067177600)), (nat_lit 404, Int.ofNat (nat_lit 269798105001600)), (nat_lit 405, Int.ofNat (nat_lit 202997926051200))]
theorem block008_data_flat055_step : block008_data_flat055 = (CoefficientMerge.fastMerge block008_data_flat051 block008_data_flat054) := by decide +kernel
theorem block008_data_flat055_original : block008_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded))) := by
  rw [block008_data_flat055_step, block008_data_flat051_original, block008_data_flat054_original]
def block008_data_flat056 : CoefficientMerge.Poly := [(nat_lit 401, Int.ofNat (nat_lit 337110459571200)), (nat_lit 402, Int.ofNat (nat_lit 339520246128000)), (nat_lit 403, Int.ofNat (nat_lit 272720067177600)), (nat_lit 404, Int.ofNat (nat_lit 269798105001600)), (nat_lit 405, Int.ofNat (nat_lit 202997926051200))]
theorem block008_data_flat056_step : block008_data_flat056 = (CoefficientMerge.fastMerge block008_data_flat050 block008_data_flat055) := by decide +kernel
theorem block008_data_flat056_original : block008_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded)))) := by
  rw [block008_data_flat056_step, block008_data_flat050_original, block008_data_flat055_original]
def block008_data_flat057 : CoefficientMerge.Poly := [(nat_lit 380, Int.ofNat (nat_lit 278367314803200)), (nat_lit 381, Int.ofNat (nat_lit 216773511897600)), (nat_lit 382, Int.ofNat (nat_lit 154848692880000)), (nat_lit 383, Int.ofNat (nat_lit 139633710451200)), (nat_lit 400, Int.ofNat (nat_lit 190423018598400)), (nat_lit 401, Int.ofNat (nat_lit 337110459571200)), (nat_lit 402, Int.ofNat (nat_lit 339520246128000)), (nat_lit 403, Int.ofNat (nat_lit 272720067177600)), (nat_lit 404, Int.ofNat (nat_lit 269798105001600)), (nat_lit 405, Int.ofNat (nat_lit 202997926051200))]
theorem block008_data_flat057_step : block008_data_flat057 = (CoefficientMerge.fastMerge block008_data_flat047 block008_data_flat056) := by decide +kernel
theorem block008_data_flat057_original : block008_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded))))) := by
  rw [block008_data_flat057_step, block008_data_flat047_original, block008_data_flat056_original]
def block008_data_flat058 : CoefficientMerge.Poly := [(nat_lit 406, Int.ofNat (nat_lit 129247858454400))]
theorem block008_data_flat058_step : block008_data_flat058 = (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) := by decide +kernel
theorem block008_data_flat058_original : block008_data_flat058 = (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) := by
  rw [block008_data_flat058_step]
def block008_data_flat059 : CoefficientMerge.Poly := [(nat_lit 407, Int.ofNat (nat_lit 121733228937600))]
theorem block008_data_flat059_step : block008_data_flat059 = (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded) := by decide +kernel
theorem block008_data_flat059_original : block008_data_flat059 = (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded) := by
  rw [block008_data_flat059_step]
def block008_data_flat060 : CoefficientMerge.Poly := [(nat_lit 406, Int.ofNat (nat_lit 129247858454400)), (nat_lit 407, Int.ofNat (nat_lit 121733228937600))]
theorem block008_data_flat060_step : block008_data_flat060 = (CoefficientMerge.fastMerge block008_data_flat058 block008_data_flat059) := by decide +kernel
theorem block008_data_flat060_original : block008_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded)) := by
  rw [block008_data_flat060_step, block008_data_flat058_original, block008_data_flat059_original]
def block008_data_flat061 : CoefficientMerge.Poly := [(nat_lit 425, Int.ofNat (nat_lit 187597703462400))]
theorem block008_data_flat061_step : block008_data_flat061 = (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) := by decide +kernel
theorem block008_data_flat061_original : block008_data_flat061 = (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) := by
  rw [block008_data_flat061_step]
def block008_data_flat062 : CoefficientMerge.Poly := [(nat_lit 426, Int.ofNat (nat_lit 350073941817600))]
theorem block008_data_flat062_step : block008_data_flat062 = (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) := by decide +kernel
theorem block008_data_flat062_original : block008_data_flat062 = (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) := by
  rw [block008_data_flat062_step]
def block008_data_flat063 : CoefficientMerge.Poly := [(nat_lit 427, Int.ofNat (nat_lit 283033756051200))]
theorem block008_data_flat063_step : block008_data_flat063 = (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded) := by decide +kernel
theorem block008_data_flat063_original : block008_data_flat063 = (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded) := by
  rw [block008_data_flat063_step]
def block008_data_flat064 : CoefficientMerge.Poly := [(nat_lit 426, Int.ofNat (nat_lit 350073941817600)), (nat_lit 427, Int.ofNat (nat_lit 283033756051200))]
theorem block008_data_flat064_step : block008_data_flat064 = (CoefficientMerge.fastMerge block008_data_flat062 block008_data_flat063) := by decide +kernel
theorem block008_data_flat064_original : block008_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded)) := by
  rw [block008_data_flat064_step, block008_data_flat062_original, block008_data_flat063_original]
def block008_data_flat065 : CoefficientMerge.Poly := [(nat_lit 425, Int.ofNat (nat_lit 187597703462400)), (nat_lit 426, Int.ofNat (nat_lit 350073941817600)), (nat_lit 427, Int.ofNat (nat_lit 283033756051200))]
theorem block008_data_flat065_step : block008_data_flat065 = (CoefficientMerge.fastMerge block008_data_flat061 block008_data_flat064) := by decide +kernel
theorem block008_data_flat065_original : block008_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded))) := by
  rw [block008_data_flat065_step, block008_data_flat061_original, block008_data_flat064_original]
def block008_data_flat066 : CoefficientMerge.Poly := [(nat_lit 406, Int.ofNat (nat_lit 129247858454400)), (nat_lit 407, Int.ofNat (nat_lit 121733228937600)), (nat_lit 425, Int.ofNat (nat_lit 187597703462400)), (nat_lit 426, Int.ofNat (nat_lit 350073941817600)), (nat_lit 427, Int.ofNat (nat_lit 283033756051200))]
theorem block008_data_flat066_step : block008_data_flat066 = (CoefficientMerge.fastMerge block008_data_flat060 block008_data_flat065) := by decide +kernel
theorem block008_data_flat066_original : block008_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded)))) := by
  rw [block008_data_flat066_step, block008_data_flat060_original, block008_data_flat065_original]
def block008_data_flat067 : CoefficientMerge.Poly := [(nat_lit 428, Int.ofNat (nat_lit 278611187500800))]
theorem block008_data_flat067_step : block008_data_flat067 = (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) := by decide +kernel
theorem block008_data_flat067_original : block008_data_flat067 = (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) := by
  rw [block008_data_flat067_step]
def block008_data_flat068 : CoefficientMerge.Poly := [(nat_lit 429, Int.ofNat (nat_lit 211571001734400))]
theorem block008_data_flat068_step : block008_data_flat068 = (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded) := by decide +kernel
theorem block008_data_flat068_original : block008_data_flat068 = (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded) := by
  rw [block008_data_flat068_step]
def block008_data_flat069 : CoefficientMerge.Poly := [(nat_lit 428, Int.ofNat (nat_lit 278611187500800)), (nat_lit 429, Int.ofNat (nat_lit 211571001734400))]
theorem block008_data_flat069_step : block008_data_flat069 = (CoefficientMerge.fastMerge block008_data_flat067 block008_data_flat068) := by decide +kernel
theorem block008_data_flat069_original : block008_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded)) := by
  rw [block008_data_flat069_step, block008_data_flat067_original, block008_data_flat068_original]
def block008_data_flat070 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 135196644844800))]
theorem block008_data_flat070_step : block008_data_flat070 = (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) := by decide +kernel
theorem block008_data_flat070_original : block008_data_flat070 = (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) := by
  rw [block008_data_flat070_step]
def block008_data_flat071 : CoefficientMerge.Poly := [(nat_lit 431, Int.ofNat (nat_lit 126181408953600))]
theorem block008_data_flat071_step : block008_data_flat071 = (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) := by decide +kernel
theorem block008_data_flat071_original : block008_data_flat071 = (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) := by
  rw [block008_data_flat071_step]
def block008_data_flat072 : CoefficientMerge.Poly := [(nat_lit 450, Int.ofNat (nat_lit 194082719846400))]
theorem block008_data_flat072_step : block008_data_flat072 = (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded) := by decide +kernel
theorem block008_data_flat072_original : block008_data_flat072 = (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded) := by
  rw [block008_data_flat072_step]
def block008_data_flat073 : CoefficientMerge.Poly := [(nat_lit 431, Int.ofNat (nat_lit 126181408953600)), (nat_lit 450, Int.ofNat (nat_lit 194082719846400))]
theorem block008_data_flat073_step : block008_data_flat073 = (CoefficientMerge.fastMerge block008_data_flat071 block008_data_flat072) := by decide +kernel
theorem block008_data_flat073_original : block008_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded)) := by
  rw [block008_data_flat073_step, block008_data_flat071_original, block008_data_flat072_original]
def block008_data_flat074 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 135196644844800)), (nat_lit 431, Int.ofNat (nat_lit 126181408953600)), (nat_lit 450, Int.ofNat (nat_lit 194082719846400))]
theorem block008_data_flat074_step : block008_data_flat074 = (CoefficientMerge.fastMerge block008_data_flat070 block008_data_flat073) := by decide +kernel
theorem block008_data_flat074_original : block008_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded))) := by
  rw [block008_data_flat074_step, block008_data_flat070_original, block008_data_flat073_original]
def block008_data_flat075 : CoefficientMerge.Poly := [(nat_lit 428, Int.ofNat (nat_lit 278611187500800)), (nat_lit 429, Int.ofNat (nat_lit 211571001734400)), (nat_lit 430, Int.ofNat (nat_lit 135196644844800)), (nat_lit 431, Int.ofNat (nat_lit 126181408953600)), (nat_lit 450, Int.ofNat (nat_lit 194082719846400))]
theorem block008_data_flat075_step : block008_data_flat075 = (CoefficientMerge.fastMerge block008_data_flat069 block008_data_flat074) := by decide +kernel
theorem block008_data_flat075_original : block008_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded)))) := by
  rw [block008_data_flat075_step, block008_data_flat069_original, block008_data_flat074_original]
def block008_data_flat076 : CoefficientMerge.Poly := [(nat_lit 406, Int.ofNat (nat_lit 129247858454400)), (nat_lit 407, Int.ofNat (nat_lit 121733228937600)), (nat_lit 425, Int.ofNat (nat_lit 187597703462400)), (nat_lit 426, Int.ofNat (nat_lit 350073941817600)), (nat_lit 427, Int.ofNat (nat_lit 283033756051200)), (nat_lit 428, Int.ofNat (nat_lit 278611187500800)), (nat_lit 429, Int.ofNat (nat_lit 211571001734400)), (nat_lit 430, Int.ofNat (nat_lit 135196644844800)), (nat_lit 431, Int.ofNat (nat_lit 126181408953600)), (nat_lit 450, Int.ofNat (nat_lit 194082719846400))]
theorem block008_data_flat076_step : block008_data_flat076 = (CoefficientMerge.fastMerge block008_data_flat066 block008_data_flat075) := by decide +kernel
theorem block008_data_flat076_original : block008_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded))))) := by
  rw [block008_data_flat076_step, block008_data_flat066_original, block008_data_flat075_original]
def block008_data_flat077 : CoefficientMerge.Poly := [(nat_lit 380, Int.ofNat (nat_lit 278367314803200)), (nat_lit 381, Int.ofNat (nat_lit 216773511897600)), (nat_lit 382, Int.ofNat (nat_lit 154848692880000)), (nat_lit 383, Int.ofNat (nat_lit 139633710451200)), (nat_lit 400, Int.ofNat (nat_lit 190423018598400)), (nat_lit 401, Int.ofNat (nat_lit 337110459571200)), (nat_lit 402, Int.ofNat (nat_lit 339520246128000)), (nat_lit 403, Int.ofNat (nat_lit 272720067177600)), (nat_lit 404, Int.ofNat (nat_lit 269798105001600)), (nat_lit 405, Int.ofNat (nat_lit 202997926051200)), (nat_lit 406, Int.ofNat (nat_lit 129247858454400)), (nat_lit 407, Int.ofNat (nat_lit 121733228937600)), (nat_lit 425, Int.ofNat (nat_lit 187597703462400)), (nat_lit 426, Int.ofNat (nat_lit 350073941817600)), (nat_lit 427, Int.ofNat (nat_lit 283033756051200)), (nat_lit 428, Int.ofNat (nat_lit 278611187500800)), (nat_lit 429, Int.ofNat (nat_lit 211571001734400)), (nat_lit 430, Int.ofNat (nat_lit 135196644844800)), (nat_lit 431, Int.ofNat (nat_lit 126181408953600)), (nat_lit 450, Int.ofNat (nat_lit 194082719846400))]
theorem block008_data_flat077_step : block008_data_flat077 = (CoefficientMerge.fastMerge block008_data_flat057 block008_data_flat076) := by decide +kernel
theorem block008_data_flat077_original : block008_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded)))))) := by
  rw [block008_data_flat077_step, block008_data_flat057_original, block008_data_flat076_original]
def block008_data_flat078 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 280362100233600)), (nat_lit 332, Int.ofNat (nat_lit 283858818566400)), (nat_lit 333, Int.ofNat (nat_lit 220539543840000)), (nat_lit 334, Int.ofNat (nat_lit 165174808478400)), (nat_lit 335, Int.ofNat (nat_lit 153751952692800)), (nat_lit 350, Int.ofNat (nat_lit 180207265392000)), (nat_lit 351, Int.ofNat (nat_lit 326270355747840)), (nat_lit 352, Int.ofNat (nat_lit 298937896306560)), (nat_lit 353, Int.ofNat (nat_lit 297051845428800)), (nat_lit 354, Int.ofNat (nat_lit 320423596416000)), (nat_lit 355, Int.ofNat (nat_lit 262910161067400)), (nat_lit 356, Int.ofNat (nat_lit 266247131673600)), (nat_lit 357, Int.ofNat (nat_lit 203948449689600)), (nat_lit 358, Int.ofNat (nat_lit 163012699899000)), (nat_lit 359, Int.ofNat (nat_lit 150660684682200)), (nat_lit 375, Int.ofNat (nat_lit 185418634867200)), (nat_lit 376, Int.ofNat (nat_lit 335715348810240)), (nat_lit 377, Int.ofNat (nat_lit 309666780864000)), (nat_lit 378, Int.ofNat (nat_lit 331449735052800)), (nat_lit 379, Int.ofNat (nat_lit 269855932147200)), (nat_lit 380, Int.ofNat (nat_lit 278367314803200)), (nat_lit 381, Int.ofNat (nat_lit 216773511897600)), (nat_lit 382, Int.ofNat (nat_lit 154848692880000)), (nat_lit 383, Int.ofNat (nat_lit 139633710451200)), (nat_lit 400, Int.ofNat (nat_lit 190423018598400)), (nat_lit 401, Int.ofNat (nat_lit 337110459571200)), (nat_lit 402, Int.ofNat (nat_lit 339520246128000)), (nat_lit 403, Int.ofNat (nat_lit 272720067177600)), (nat_lit 404, Int.ofNat (nat_lit 269798105001600)), (nat_lit 405, Int.ofNat (nat_lit 202997926051200)), (nat_lit 406, Int.ofNat (nat_lit 129247858454400)), (nat_lit 407, Int.ofNat (nat_lit 121733228937600)), (nat_lit 425, Int.ofNat (nat_lit 187597703462400)), (nat_lit 426, Int.ofNat (nat_lit 350073941817600)), (nat_lit 427, Int.ofNat (nat_lit 283033756051200)), (nat_lit 428, Int.ofNat (nat_lit 278611187500800)), (nat_lit 429, Int.ofNat (nat_lit 211571001734400)), (nat_lit 430, Int.ofNat (nat_lit 135196644844800)), (nat_lit 431, Int.ofNat (nat_lit 126181408953600)), (nat_lit 450, Int.ofNat (nat_lit 194082719846400))]
theorem block008_data_flat078_step : block008_data_flat078 = (CoefficientMerge.fastMerge block008_data_flat038 block008_data_flat077) := by decide +kernel
theorem block008_data_flat078_original : block008_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded))))))) := by
  rw [block008_data_flat078_step, block008_data_flat038_original, block008_data_flat077_original]
def block008_data_flat079 : CoefficientMerge.Poly := [(nat_lit 451, Int.ofNat (nat_lit 329949128678400))]
theorem block008_data_flat079_step : block008_data_flat079 = (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) := by decide +kernel
theorem block008_data_flat079_original : block008_data_flat079 = (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) := by
  rw [block008_data_flat079_step]
def block008_data_flat080 : CoefficientMerge.Poly := [(nat_lit 452, Int.ofNat (nat_lit 342153716889600))]
theorem block008_data_flat080_step : block008_data_flat080 = (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded) := by decide +kernel
theorem block008_data_flat080_original : block008_data_flat080 = (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded) := by
  rw [block008_data_flat080_step]
def block008_data_flat081 : CoefficientMerge.Poly := [(nat_lit 451, Int.ofNat (nat_lit 329949128678400)), (nat_lit 452, Int.ofNat (nat_lit 342153716889600))]
theorem block008_data_flat081_step : block008_data_flat081 = (CoefficientMerge.fastMerge block008_data_flat079 block008_data_flat080) := by decide +kernel
theorem block008_data_flat081_original : block008_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded)) := by
  rw [block008_data_flat081_step, block008_data_flat079_original, block008_data_flat080_original]
def block008_data_flat082 : CoefficientMerge.Poly := [(nat_lit 453, Int.ofNat (nat_lit 283937405875200))]
theorem block008_data_flat082_step : block008_data_flat082 = (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) := by decide +kernel
theorem block008_data_flat082_original : block008_data_flat082 = (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) := by
  rw [block008_data_flat082_step]
def block008_data_flat083 : CoefficientMerge.Poly := [(nat_lit 454, Int.ofNat (nat_lit 163805135155200))]
theorem block008_data_flat083_step : block008_data_flat083 = (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) := by decide +kernel
theorem block008_data_flat083_original : block008_data_flat083 = (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) := by
  rw [block008_data_flat083_step]
def block008_data_flat084 : CoefficientMerge.Poly := [(nat_lit 455, Int.ofNat (nat_lit 171417056025600))]
theorem block008_data_flat084_step : block008_data_flat084 = (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded) := by decide +kernel
theorem block008_data_flat084_original : block008_data_flat084 = (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded) := by
  rw [block008_data_flat084_step]
def block008_data_flat085 : CoefficientMerge.Poly := [(nat_lit 454, Int.ofNat (nat_lit 163805135155200)), (nat_lit 455, Int.ofNat (nat_lit 171417056025600))]
theorem block008_data_flat085_step : block008_data_flat085 = (CoefficientMerge.fastMerge block008_data_flat083 block008_data_flat084) := by decide +kernel
theorem block008_data_flat085_original : block008_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded)) := by
  rw [block008_data_flat085_step, block008_data_flat083_original, block008_data_flat084_original]
def block008_data_flat086 : CoefficientMerge.Poly := [(nat_lit 453, Int.ofNat (nat_lit 283937405875200)), (nat_lit 454, Int.ofNat (nat_lit 163805135155200)), (nat_lit 455, Int.ofNat (nat_lit 171417056025600))]
theorem block008_data_flat086_step : block008_data_flat086 = (CoefficientMerge.fastMerge block008_data_flat082 block008_data_flat085) := by decide +kernel
theorem block008_data_flat086_original : block008_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded))) := by
  rw [block008_data_flat086_step, block008_data_flat082_original, block008_data_flat085_original]
def block008_data_flat087 : CoefficientMerge.Poly := [(nat_lit 451, Int.ofNat (nat_lit 329949128678400)), (nat_lit 452, Int.ofNat (nat_lit 342153716889600)), (nat_lit 453, Int.ofNat (nat_lit 283937405875200)), (nat_lit 454, Int.ofNat (nat_lit 163805135155200)), (nat_lit 455, Int.ofNat (nat_lit 171417056025600))]
theorem block008_data_flat087_step : block008_data_flat087 = (CoefficientMerge.fastMerge block008_data_flat081 block008_data_flat086) := by decide +kernel
theorem block008_data_flat087_original : block008_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded)))) := by
  rw [block008_data_flat087_step, block008_data_flat081_original, block008_data_flat086_original]
def block008_data_flat088 : CoefficientMerge.Poly := [(nat_lit 475, Int.ofNat (nat_lit 137682213419520))]
theorem block008_data_flat088_step : block008_data_flat088 = (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) := by decide +kernel
theorem block008_data_flat088_original : block008_data_flat088 = (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) := by
  rw [block008_data_flat088_step]
def block008_data_flat089 : CoefficientMerge.Poly := [(nat_lit 476, Int.ofNat (nat_lit 278791917465600))]
theorem block008_data_flat089_step : block008_data_flat089 = (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded) := by decide +kernel
theorem block008_data_flat089_original : block008_data_flat089 = (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded) := by
  rw [block008_data_flat089_step]
def block008_data_flat090 : CoefficientMerge.Poly := [(nat_lit 475, Int.ofNat (nat_lit 137682213419520)), (nat_lit 476, Int.ofNat (nat_lit 278791917465600))]
theorem block008_data_flat090_step : block008_data_flat090 = (CoefficientMerge.fastMerge block008_data_flat088 block008_data_flat089) := by decide +kernel
theorem block008_data_flat090_original : block008_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded)) := by
  rw [block008_data_flat090_step, block008_data_flat088_original, block008_data_flat089_original]
def block008_data_flat091 : CoefficientMerge.Poly := [(nat_lit 477, Int.ofNat (nat_lit 292017098419200))]
theorem block008_data_flat091_step : block008_data_flat091 = (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) := by decide +kernel
theorem block008_data_flat091_original : block008_data_flat091 = (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) := by
  rw [block008_data_flat091_step]
def block008_data_flat092 : CoefficientMerge.Poly := [(nat_lit 478, Int.ofNat (nat_lit 172905420441600))]
theorem block008_data_flat092_step : block008_data_flat092 = (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) := by decide +kernel
theorem block008_data_flat092_original : block008_data_flat092 = (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) := by
  rw [block008_data_flat092_step]
def block008_data_flat093 : CoefficientMerge.Poly := [(nat_lit 479, Int.ofNat (nat_lit 181537934054400))]
theorem block008_data_flat093_step : block008_data_flat093 = (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded) := by decide +kernel
theorem block008_data_flat093_original : block008_data_flat093 = (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded) := by
  rw [block008_data_flat093_step]
def block008_data_flat094 : CoefficientMerge.Poly := [(nat_lit 478, Int.ofNat (nat_lit 172905420441600)), (nat_lit 479, Int.ofNat (nat_lit 181537934054400))]
theorem block008_data_flat094_step : block008_data_flat094 = (CoefficientMerge.fastMerge block008_data_flat092 block008_data_flat093) := by decide +kernel
theorem block008_data_flat094_original : block008_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded)) := by
  rw [block008_data_flat094_step, block008_data_flat092_original, block008_data_flat093_original]
def block008_data_flat095 : CoefficientMerge.Poly := [(nat_lit 477, Int.ofNat (nat_lit 292017098419200)), (nat_lit 478, Int.ofNat (nat_lit 172905420441600)), (nat_lit 479, Int.ofNat (nat_lit 181537934054400))]
theorem block008_data_flat095_step : block008_data_flat095 = (CoefficientMerge.fastMerge block008_data_flat091 block008_data_flat094) := by decide +kernel
theorem block008_data_flat095_original : block008_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded))) := by
  rw [block008_data_flat095_step, block008_data_flat091_original, block008_data_flat094_original]
def block008_data_flat096 : CoefficientMerge.Poly := [(nat_lit 475, Int.ofNat (nat_lit 137682213419520)), (nat_lit 476, Int.ofNat (nat_lit 278791917465600)), (nat_lit 477, Int.ofNat (nat_lit 292017098419200)), (nat_lit 478, Int.ofNat (nat_lit 172905420441600)), (nat_lit 479, Int.ofNat (nat_lit 181537934054400))]
theorem block008_data_flat096_step : block008_data_flat096 = (CoefficientMerge.fastMerge block008_data_flat090 block008_data_flat095) := by decide +kernel
theorem block008_data_flat096_original : block008_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded)))) := by
  rw [block008_data_flat096_step, block008_data_flat090_original, block008_data_flat095_original]
def block008_data_flat097 : CoefficientMerge.Poly := [(nat_lit 451, Int.ofNat (nat_lit 329949128678400)), (nat_lit 452, Int.ofNat (nat_lit 342153716889600)), (nat_lit 453, Int.ofNat (nat_lit 283937405875200)), (nat_lit 454, Int.ofNat (nat_lit 163805135155200)), (nat_lit 455, Int.ofNat (nat_lit 171417056025600)), (nat_lit 475, Int.ofNat (nat_lit 137682213419520)), (nat_lit 476, Int.ofNat (nat_lit 278791917465600)), (nat_lit 477, Int.ofNat (nat_lit 292017098419200)), (nat_lit 478, Int.ofNat (nat_lit 172905420441600)), (nat_lit 479, Int.ofNat (nat_lit 181537934054400))]
theorem block008_data_flat097_step : block008_data_flat097 = (CoefficientMerge.fastMerge block008_data_flat087 block008_data_flat096) := by decide +kernel
theorem block008_data_flat097_original : block008_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded))))) := by
  rw [block008_data_flat097_step, block008_data_flat087_original, block008_data_flat096_original]
def block008_data_flat098 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 142925508633600))]
theorem block008_data_flat098_step : block008_data_flat098 = (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) := by decide +kernel
theorem block008_data_flat098_original : block008_data_flat098 = (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) := by
  rw [block008_data_flat098_step]
def block008_data_flat099 : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 300096790963200))]
theorem block008_data_flat099_step : block008_data_flat099 = (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded) := by decide +kernel
theorem block008_data_flat099_original : block008_data_flat099 = (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded) := by
  rw [block008_data_flat099_step]
def block008_data_flat100 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 142925508633600)), (nat_lit 501, Int.ofNat (nat_lit 300096790963200))]
theorem block008_data_flat100_step : block008_data_flat100 = (CoefficientMerge.fastMerge block008_data_flat098 block008_data_flat099) := by decide +kernel
theorem block008_data_flat100_original : block008_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded)) := by
  rw [block008_data_flat100_step, block008_data_flat098_original, block008_data_flat099_original]
def block008_data_flat101 : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 182005705728000))]
theorem block008_data_flat101_step : block008_data_flat101 = (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) := by decide +kernel
theorem block008_data_flat101_original : block008_data_flat101 = (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) := by
  rw [block008_data_flat101_step]
def block008_data_flat102 : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 167207110963200))]
theorem block008_data_flat102_step : block008_data_flat102 = (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) := by decide +kernel
theorem block008_data_flat102_original : block008_data_flat102 = (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) := by
  rw [block008_data_flat102_step]
def block008_data_flat103 : CoefficientMerge.Poly := [(nat_lit 525, Int.ofNat (nat_lit 154088241753600))]
theorem block008_data_flat103_step : block008_data_flat103 = (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded) := by decide +kernel
theorem block008_data_flat103_original : block008_data_flat103 = (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded) := by
  rw [block008_data_flat103_step]
def block008_data_flat104 : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 167207110963200)), (nat_lit 525, Int.ofNat (nat_lit 154088241753600))]
theorem block008_data_flat104_step : block008_data_flat104 = (CoefficientMerge.fastMerge block008_data_flat102 block008_data_flat103) := by decide +kernel
theorem block008_data_flat104_original : block008_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded)) := by
  rw [block008_data_flat104_step, block008_data_flat102_original, block008_data_flat103_original]
def block008_data_flat105 : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 182005705728000)), (nat_lit 503, Int.ofNat (nat_lit 167207110963200)), (nat_lit 525, Int.ofNat (nat_lit 154088241753600))]
theorem block008_data_flat105_step : block008_data_flat105 = (CoefficientMerge.fastMerge block008_data_flat101 block008_data_flat104) := by decide +kernel
theorem block008_data_flat105_original : block008_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded))) := by
  rw [block008_data_flat105_step, block008_data_flat101_original, block008_data_flat104_original]
def block008_data_flat106 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 142925508633600)), (nat_lit 501, Int.ofNat (nat_lit 300096790963200)), (nat_lit 502, Int.ofNat (nat_lit 182005705728000)), (nat_lit 503, Int.ofNat (nat_lit 167207110963200)), (nat_lit 525, Int.ofNat (nat_lit 154088241753600))]
theorem block008_data_flat106_step : block008_data_flat106 = (CoefficientMerge.fastMerge block008_data_flat100 block008_data_flat105) := by decide +kernel
theorem block008_data_flat106_original : block008_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded)))) := by
  rw [block008_data_flat106_step, block008_data_flat100_original, block008_data_flat105_original]
def block008_data_flat107 : CoefficientMerge.Poly := [(nat_lit 526, Int.ofNat (nat_lit 191105991014400))]
theorem block008_data_flat107_step : block008_data_flat107 = (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) := by decide +kernel
theorem block008_data_flat107_original : block008_data_flat107 = (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) := by
  rw [block008_data_flat107_step]
def block008_data_flat108 : CoefficientMerge.Poly := [(nat_lit 527, Int.ofNat (nat_lit 177327988992000))]
theorem block008_data_flat108_step : block008_data_flat108 = (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded) := by decide +kernel
theorem block008_data_flat108_original : block008_data_flat108 = (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded) := by
  rw [block008_data_flat108_step]
def block008_data_flat109 : CoefficientMerge.Poly := [(nat_lit 526, Int.ofNat (nat_lit 191105991014400)), (nat_lit 527, Int.ofNat (nat_lit 177327988992000))]
theorem block008_data_flat109_step : block008_data_flat109 = (CoefficientMerge.fastMerge block008_data_flat107 block008_data_flat108) := by decide +kernel
theorem block008_data_flat109_original : block008_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded)) := by
  rw [block008_data_flat109_step, block008_data_flat107_original, block008_data_flat108_original]
def block008_data_flat110 : CoefficientMerge.Poly := [(nat_lit 550, Int.ofNat (nat_lit 22316002884000))]
theorem block008_data_flat110_step : block008_data_flat110 = (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) := by decide +kernel
theorem block008_data_flat110_original : block008_data_flat110 = (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) := by
  rw [block008_data_flat110_step]
def block008_data_flat111 : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 35848320076800))]
theorem block008_data_flat111_step : block008_data_flat111 = (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) := by decide +kernel
theorem block008_data_flat111_original : block008_data_flat111 = (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) := by
  rw [block008_data_flat111_step]
def block008_data_flat112 : CoefficientMerge.Poly := [(nat_lit 602, Int.ofNat (nat_lit 43587815040000))]
theorem block008_data_flat112_step : block008_data_flat112 = (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded) := by decide +kernel
theorem block008_data_flat112_original : block008_data_flat112 = (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded) := by
  rw [block008_data_flat112_step]
def block008_data_flat113 : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 35848320076800)), (nat_lit 602, Int.ofNat (nat_lit 43587815040000))]
theorem block008_data_flat113_step : block008_data_flat113 = (CoefficientMerge.fastMerge block008_data_flat111 block008_data_flat112) := by decide +kernel
theorem block008_data_flat113_original : block008_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded)) := by
  rw [block008_data_flat113_step, block008_data_flat111_original, block008_data_flat112_original]
def block008_data_flat114 : CoefficientMerge.Poly := [(nat_lit 550, Int.ofNat (nat_lit 22316002884000)), (nat_lit 551, Int.ofNat (nat_lit 35848320076800)), (nat_lit 602, Int.ofNat (nat_lit 43587815040000))]
theorem block008_data_flat114_step : block008_data_flat114 = (CoefficientMerge.fastMerge block008_data_flat110 block008_data_flat113) := by decide +kernel
theorem block008_data_flat114_original : block008_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded))) := by
  rw [block008_data_flat114_step, block008_data_flat110_original, block008_data_flat113_original]
def block008_data_flat115 : CoefficientMerge.Poly := [(nat_lit 526, Int.ofNat (nat_lit 191105991014400)), (nat_lit 527, Int.ofNat (nat_lit 177327988992000)), (nat_lit 550, Int.ofNat (nat_lit 22316002884000)), (nat_lit 551, Int.ofNat (nat_lit 35848320076800)), (nat_lit 602, Int.ofNat (nat_lit 43587815040000))]
theorem block008_data_flat115_step : block008_data_flat115 = (CoefficientMerge.fastMerge block008_data_flat109 block008_data_flat114) := by decide +kernel
theorem block008_data_flat115_original : block008_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded)))) := by
  rw [block008_data_flat115_step, block008_data_flat109_original, block008_data_flat114_original]
def block008_data_flat116 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 142925508633600)), (nat_lit 501, Int.ofNat (nat_lit 300096790963200)), (nat_lit 502, Int.ofNat (nat_lit 182005705728000)), (nat_lit 503, Int.ofNat (nat_lit 167207110963200)), (nat_lit 525, Int.ofNat (nat_lit 154088241753600)), (nat_lit 526, Int.ofNat (nat_lit 191105991014400)), (nat_lit 527, Int.ofNat (nat_lit 177327988992000)), (nat_lit 550, Int.ofNat (nat_lit 22316002884000)), (nat_lit 551, Int.ofNat (nat_lit 35848320076800)), (nat_lit 602, Int.ofNat (nat_lit 43587815040000))]
theorem block008_data_flat116_step : block008_data_flat116 = (CoefficientMerge.fastMerge block008_data_flat106 block008_data_flat115) := by decide +kernel
theorem block008_data_flat116_original : block008_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded))))) := by
  rw [block008_data_flat116_step, block008_data_flat106_original, block008_data_flat115_original]
def block008_data_flat117 : CoefficientMerge.Poly := [(nat_lit 451, Int.ofNat (nat_lit 329949128678400)), (nat_lit 452, Int.ofNat (nat_lit 342153716889600)), (nat_lit 453, Int.ofNat (nat_lit 283937405875200)), (nat_lit 454, Int.ofNat (nat_lit 163805135155200)), (nat_lit 455, Int.ofNat (nat_lit 171417056025600)), (nat_lit 475, Int.ofNat (nat_lit 137682213419520)), (nat_lit 476, Int.ofNat (nat_lit 278791917465600)), (nat_lit 477, Int.ofNat (nat_lit 292017098419200)), (nat_lit 478, Int.ofNat (nat_lit 172905420441600)), (nat_lit 479, Int.ofNat (nat_lit 181537934054400)), (nat_lit 500, Int.ofNat (nat_lit 142925508633600)), (nat_lit 501, Int.ofNat (nat_lit 300096790963200)), (nat_lit 502, Int.ofNat (nat_lit 182005705728000)), (nat_lit 503, Int.ofNat (nat_lit 167207110963200)), (nat_lit 525, Int.ofNat (nat_lit 154088241753600)), (nat_lit 526, Int.ofNat (nat_lit 191105991014400)), (nat_lit 527, Int.ofNat (nat_lit 177327988992000)), (nat_lit 550, Int.ofNat (nat_lit 22316002884000)), (nat_lit 551, Int.ofNat (nat_lit 35848320076800)), (nat_lit 602, Int.ofNat (nat_lit 43587815040000))]
theorem block008_data_flat117_step : block008_data_flat117 = (CoefficientMerge.fastMerge block008_data_flat097 block008_data_flat116) := by decide +kernel
theorem block008_data_flat117_original : block008_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded)))))) := by
  rw [block008_data_flat117_step, block008_data_flat097_original, block008_data_flat116_original]
def block008_data_flat118 : CoefficientMerge.Poly := [(nat_lit 603, Int.ofNat (nat_lit 38442326630400))]
theorem block008_data_flat118_step : block008_data_flat118 = (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) := by decide +kernel
theorem block008_data_flat118_original : block008_data_flat118 = (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) := by
  rw [block008_data_flat118_step]
def block008_data_flat119 : CoefficientMerge.Poly := [(nat_lit 604, Int.ofNat (nat_lit 33296838220800))]
theorem block008_data_flat119_step : block008_data_flat119 = (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded) := by decide +kernel
theorem block008_data_flat119_original : block008_data_flat119 = (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded) := by
  rw [block008_data_flat119_step]
def block008_data_flat120 : CoefficientMerge.Poly := [(nat_lit 603, Int.ofNat (nat_lit 38442326630400)), (nat_lit 604, Int.ofNat (nat_lit 33296838220800))]
theorem block008_data_flat120_step : block008_data_flat120 = (CoefficientMerge.fastMerge block008_data_flat118 block008_data_flat119) := by decide +kernel
theorem block008_data_flat120_original : block008_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded)) := by
  rw [block008_data_flat120_step, block008_data_flat118_original, block008_data_flat119_original]
def block008_data_flat121 : CoefficientMerge.Poly := [(nat_lit 605, Int.ofNat (nat_lit 35034243552000))]
theorem block008_data_flat121_step : block008_data_flat121 = (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) := by decide +kernel
theorem block008_data_flat121_original : block008_data_flat121 = (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) := by
  rw [block008_data_flat121_step]
def block008_data_flat122 : CoefficientMerge.Poly := [(nat_lit 606, Int.ofNat (nat_lit 23005861401600))]
theorem block008_data_flat122_step : block008_data_flat122 = (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) := by decide +kernel
theorem block008_data_flat122_original : block008_data_flat122 = (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) := by
  rw [block008_data_flat122_step]
def block008_data_flat123 : CoefficientMerge.Poly := [(nat_lit 607, Int.ofNat (nat_lit 17860372992000))]
theorem block008_data_flat123_step : block008_data_flat123 = (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded) := by decide +kernel
theorem block008_data_flat123_original : block008_data_flat123 = (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded) := by
  rw [block008_data_flat123_step]
def block008_data_flat124 : CoefficientMerge.Poly := [(nat_lit 606, Int.ofNat (nat_lit 23005861401600)), (nat_lit 607, Int.ofNat (nat_lit 17860372992000))]
theorem block008_data_flat124_step : block008_data_flat124 = (CoefficientMerge.fastMerge block008_data_flat122 block008_data_flat123) := by decide +kernel
theorem block008_data_flat124_original : block008_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded)) := by
  rw [block008_data_flat124_step, block008_data_flat122_original, block008_data_flat123_original]
def block008_data_flat125 : CoefficientMerge.Poly := [(nat_lit 605, Int.ofNat (nat_lit 35034243552000)), (nat_lit 606, Int.ofNat (nat_lit 23005861401600)), (nat_lit 607, Int.ofNat (nat_lit 17860372992000))]
theorem block008_data_flat125_step : block008_data_flat125 = (CoefficientMerge.fastMerge block008_data_flat121 block008_data_flat124) := by decide +kernel
theorem block008_data_flat125_original : block008_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded))) := by
  rw [block008_data_flat125_step, block008_data_flat121_original, block008_data_flat124_original]
def block008_data_flat126 : CoefficientMerge.Poly := [(nat_lit 603, Int.ofNat (nat_lit 38442326630400)), (nat_lit 604, Int.ofNat (nat_lit 33296838220800)), (nat_lit 605, Int.ofNat (nat_lit 35034243552000)), (nat_lit 606, Int.ofNat (nat_lit 23005861401600)), (nat_lit 607, Int.ofNat (nat_lit 17860372992000))]
theorem block008_data_flat126_step : block008_data_flat126 = (CoefficientMerge.fastMerge block008_data_flat120 block008_data_flat125) := by decide +kernel
theorem block008_data_flat126_original : block008_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded)))) := by
  rw [block008_data_flat126_step, block008_data_flat120_original, block008_data_flat125_original]
def block008_data_flat127 : CoefficientMerge.Poly := [(nat_lit 608, Int.ofNat (nat_lit 12714884582400))]
theorem block008_data_flat127_step : block008_data_flat127 = (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) := by decide +kernel
theorem block008_data_flat127_original : block008_data_flat127 = (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) := by
  rw [block008_data_flat127_step]
def block008_data_flat128 : CoefficientMerge.Poly := [(nat_lit 609, Int.ofNat (nat_lit 13581177218928))]
theorem block008_data_flat128_step : block008_data_flat128 = (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded) := by decide +kernel
theorem block008_data_flat128_original : block008_data_flat128 = (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded) := by
  rw [block008_data_flat128_step]
def block008_data_flat129 : CoefficientMerge.Poly := [(nat_lit 608, Int.ofNat (nat_lit 12714884582400)), (nat_lit 609, Int.ofNat (nat_lit 13581177218928))]
theorem block008_data_flat129_step : block008_data_flat129 = (CoefficientMerge.fastMerge block008_data_flat127 block008_data_flat128) := by decide +kernel
theorem block008_data_flat129_original : block008_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded)) := by
  rw [block008_data_flat129_step, block008_data_flat127_original, block008_data_flat128_original]
def block008_data_flat130 : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 26079185843568))]
theorem block008_data_flat130_step : block008_data_flat130 = (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) := by decide +kernel
theorem block008_data_flat130_original : block008_data_flat130 = (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) := by
  rw [block008_data_flat130_step]
def block008_data_flat131 : CoefficientMerge.Poly := [(nat_lit 611, Int.ofNat (nat_lit 36938767228704))]
theorem block008_data_flat131_step : block008_data_flat131 = (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) := by decide +kernel
theorem block008_data_flat131_original : block008_data_flat131 = (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) := by
  rw [block008_data_flat131_step]
def block008_data_flat132 : CoefficientMerge.Poly := [(nat_lit 612, Int.ofNat (nat_lit 59715261042624))]
theorem block008_data_flat132_step : block008_data_flat132 = (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded) := by decide +kernel
theorem block008_data_flat132_original : block008_data_flat132 = (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded) := by
  rw [block008_data_flat132_step]
def block008_data_flat133 : CoefficientMerge.Poly := [(nat_lit 611, Int.ofNat (nat_lit 36938767228704)), (nat_lit 612, Int.ofNat (nat_lit 59715261042624))]
theorem block008_data_flat133_step : block008_data_flat133 = (CoefficientMerge.fastMerge block008_data_flat131 block008_data_flat132) := by decide +kernel
theorem block008_data_flat133_original : block008_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded)) := by
  rw [block008_data_flat133_step, block008_data_flat131_original, block008_data_flat132_original]
def block008_data_flat134 : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 26079185843568)), (nat_lit 611, Int.ofNat (nat_lit 36938767228704)), (nat_lit 612, Int.ofNat (nat_lit 59715261042624))]
theorem block008_data_flat134_step : block008_data_flat134 = (CoefficientMerge.fastMerge block008_data_flat130 block008_data_flat133) := by decide +kernel
theorem block008_data_flat134_original : block008_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded))) := by
  rw [block008_data_flat134_step, block008_data_flat130_original, block008_data_flat133_original]
def block008_data_flat135 : CoefficientMerge.Poly := [(nat_lit 608, Int.ofNat (nat_lit 12714884582400)), (nat_lit 609, Int.ofNat (nat_lit 13581177218928)), (nat_lit 610, Int.ofNat (nat_lit 26079185843568)), (nat_lit 611, Int.ofNat (nat_lit 36938767228704)), (nat_lit 612, Int.ofNat (nat_lit 59715261042624))]
theorem block008_data_flat135_step : block008_data_flat135 = (CoefficientMerge.fastMerge block008_data_flat129 block008_data_flat134) := by decide +kernel
theorem block008_data_flat135_original : block008_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded)))) := by
  rw [block008_data_flat135_step, block008_data_flat129_original, block008_data_flat134_original]
def block008_data_flat136 : CoefficientMerge.Poly := [(nat_lit 603, Int.ofNat (nat_lit 38442326630400)), (nat_lit 604, Int.ofNat (nat_lit 33296838220800)), (nat_lit 605, Int.ofNat (nat_lit 35034243552000)), (nat_lit 606, Int.ofNat (nat_lit 23005861401600)), (nat_lit 607, Int.ofNat (nat_lit 17860372992000)), (nat_lit 608, Int.ofNat (nat_lit 12714884582400)), (nat_lit 609, Int.ofNat (nat_lit 13581177218928)), (nat_lit 610, Int.ofNat (nat_lit 26079185843568)), (nat_lit 611, Int.ofNat (nat_lit 36938767228704)), (nat_lit 612, Int.ofNat (nat_lit 59715261042624))]
theorem block008_data_flat136_step : block008_data_flat136 = (CoefficientMerge.fastMerge block008_data_flat126 block008_data_flat135) := by decide +kernel
theorem block008_data_flat136_original : block008_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded))))) := by
  rw [block008_data_flat136_step, block008_data_flat126_original, block008_data_flat135_original]
def block008_data_flat137 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 45908642102400))]
theorem block008_data_flat137_step : block008_data_flat137 = (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) := by decide +kernel
theorem block008_data_flat137_original : block008_data_flat137 = (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) := by
  rw [block008_data_flat137_step]
def block008_data_flat138 : CoefficientMerge.Poly := [(nat_lit 614, Int.ofNat (nat_lit 28427760345600))]
theorem block008_data_flat138_step : block008_data_flat138 = (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded) := by decide +kernel
theorem block008_data_flat138_original : block008_data_flat138 = (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded) := by
  rw [block008_data_flat138_step]
def block008_data_flat139 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 45908642102400)), (nat_lit 614, Int.ofNat (nat_lit 28427760345600))]
theorem block008_data_flat139_step : block008_data_flat139 = (CoefficientMerge.fastMerge block008_data_flat137 block008_data_flat138) := by decide +kernel
theorem block008_data_flat139_original : block008_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded)) := by
  rw [block008_data_flat139_step, block008_data_flat137_original, block008_data_flat138_original]
def block008_data_flat140 : CoefficientMerge.Poly := [(nat_lit 615, Int.ofNat (nat_lit 25733885184000))]
theorem block008_data_flat140_step : block008_data_flat140 = (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) := by decide +kernel
theorem block008_data_flat140_original : block008_data_flat140 = (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) := by
  rw [block008_data_flat140_step]
def block008_data_flat141 : CoefficientMerge.Poly := [(nat_lit 616, Int.ofNat (nat_lit 11217499776000))]
theorem block008_data_flat141_step : block008_data_flat141 = (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) := by decide +kernel
theorem block008_data_flat141_original : block008_data_flat141 = (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) := by
  rw [block008_data_flat141_step]
def block008_data_flat142 : CoefficientMerge.Poly := [(nat_lit 617, Int.ofNat (nat_lit 6633852825600))]
theorem block008_data_flat142_step : block008_data_flat142 = (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded) := by decide +kernel
theorem block008_data_flat142_original : block008_data_flat142 = (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded) := by
  rw [block008_data_flat142_step]
def block008_data_flat143 : CoefficientMerge.Poly := [(nat_lit 616, Int.ofNat (nat_lit 11217499776000)), (nat_lit 617, Int.ofNat (nat_lit 6633852825600))]
theorem block008_data_flat143_step : block008_data_flat143 = (CoefficientMerge.fastMerge block008_data_flat141 block008_data_flat142) := by decide +kernel
theorem block008_data_flat143_original : block008_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded)) := by
  rw [block008_data_flat143_step, block008_data_flat141_original, block008_data_flat142_original]
def block008_data_flat144 : CoefficientMerge.Poly := [(nat_lit 615, Int.ofNat (nat_lit 25733885184000)), (nat_lit 616, Int.ofNat (nat_lit 11217499776000)), (nat_lit 617, Int.ofNat (nat_lit 6633852825600))]
theorem block008_data_flat144_step : block008_data_flat144 = (CoefficientMerge.fastMerge block008_data_flat140 block008_data_flat143) := by decide +kernel
theorem block008_data_flat144_original : block008_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded))) := by
  rw [block008_data_flat144_step, block008_data_flat140_original, block008_data_flat143_original]
def block008_data_flat145 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 45908642102400)), (nat_lit 614, Int.ofNat (nat_lit 28427760345600)), (nat_lit 615, Int.ofNat (nat_lit 25733885184000)), (nat_lit 616, Int.ofNat (nat_lit 11217499776000)), (nat_lit 617, Int.ofNat (nat_lit 6633852825600))]
theorem block008_data_flat145_step : block008_data_flat145 = (CoefficientMerge.fastMerge block008_data_flat139 block008_data_flat144) := by decide +kernel
theorem block008_data_flat145_original : block008_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded)))) := by
  rw [block008_data_flat145_step, block008_data_flat139_original, block008_data_flat144_original]
def block008_data_flat146 : CoefficientMerge.Poly := [(nat_lit 618, Int.ofNat (nat_lit 29512140134400))]
theorem block008_data_flat146_step : block008_data_flat146 = (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) := by decide +kernel
theorem block008_data_flat146_original : block008_data_flat146 = (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) := by
  rw [block008_data_flat146_step]
def block008_data_flat147 : CoefficientMerge.Poly := [(nat_lit 620, Int.ofNat (nat_lit 6208605849600))]
theorem block008_data_flat147_step : block008_data_flat147 = (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded) := by decide +kernel
theorem block008_data_flat147_original : block008_data_flat147 = (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded) := by
  rw [block008_data_flat147_step]
def block008_data_flat148 : CoefficientMerge.Poly := [(nat_lit 618, Int.ofNat (nat_lit 29512140134400)), (nat_lit 620, Int.ofNat (nat_lit 6208605849600))]
theorem block008_data_flat148_step : block008_data_flat148 = (CoefficientMerge.fastMerge block008_data_flat146 block008_data_flat147) := by decide +kernel
theorem block008_data_flat148_original : block008_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded)) := by
  rw [block008_data_flat148_step, block008_data_flat146_original, block008_data_flat147_original]
def block008_data_flat149 : CoefficientMerge.Poly := [(nat_lit 626, Int.ofNat (nat_lit 85347068083200))]
theorem block008_data_flat149_step : block008_data_flat149 = (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) := by decide +kernel
theorem block008_data_flat149_original : block008_data_flat149 = (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) := by
  rw [block008_data_flat149_step]
def block008_data_flat150 : CoefficientMerge.Poly := [(nat_lit 627, Int.ofNat (nat_lit 162444344832000))]
theorem block008_data_flat150_step : block008_data_flat150 = (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) := by decide +kernel
theorem block008_data_flat150_original : block008_data_flat150 = (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) := by
  rw [block008_data_flat150_step]
def block008_data_flat151 : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
theorem block008_data_flat151_step : block008_data_flat151 = (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded) := by decide +kernel
theorem block008_data_flat151_original : block008_data_flat151 = (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded) := by
  rw [block008_data_flat151_step]
def block008_data_flat152 : CoefficientMerge.Poly := [(nat_lit 627, Int.ofNat (nat_lit 162444344832000)), (nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
theorem block008_data_flat152_step : block008_data_flat152 = (CoefficientMerge.fastMerge block008_data_flat150 block008_data_flat151) := by decide +kernel
theorem block008_data_flat152_original : block008_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded)) := by
  rw [block008_data_flat152_step, block008_data_flat150_original, block008_data_flat151_original]
def block008_data_flat153 : CoefficientMerge.Poly := [(nat_lit 626, Int.ofNat (nat_lit 85347068083200)), (nat_lit 627, Int.ofNat (nat_lit 162444344832000)), (nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
theorem block008_data_flat153_step : block008_data_flat153 = (CoefficientMerge.fastMerge block008_data_flat149 block008_data_flat152) := by decide +kernel
theorem block008_data_flat153_original : block008_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded))) := by
  rw [block008_data_flat153_step, block008_data_flat149_original, block008_data_flat152_original]
def block008_data_flat154 : CoefficientMerge.Poly := [(nat_lit 618, Int.ofNat (nat_lit 29512140134400)), (nat_lit 620, Int.ofNat (nat_lit 6208605849600)), (nat_lit 626, Int.ofNat (nat_lit 85347068083200)), (nat_lit 627, Int.ofNat (nat_lit 162444344832000)), (nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
theorem block008_data_flat154_step : block008_data_flat154 = (CoefficientMerge.fastMerge block008_data_flat148 block008_data_flat153) := by decide +kernel
theorem block008_data_flat154_original : block008_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded)))) := by
  rw [block008_data_flat154_step, block008_data_flat148_original, block008_data_flat153_original]
def block008_data_flat155 : CoefficientMerge.Poly := [(nat_lit 613, Int.ofNat (nat_lit 45908642102400)), (nat_lit 614, Int.ofNat (nat_lit 28427760345600)), (nat_lit 615, Int.ofNat (nat_lit 25733885184000)), (nat_lit 616, Int.ofNat (nat_lit 11217499776000)), (nat_lit 617, Int.ofNat (nat_lit 6633852825600)), (nat_lit 618, Int.ofNat (nat_lit 29512140134400)), (nat_lit 620, Int.ofNat (nat_lit 6208605849600)), (nat_lit 626, Int.ofNat (nat_lit 85347068083200)), (nat_lit 627, Int.ofNat (nat_lit 162444344832000)), (nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
theorem block008_data_flat155_step : block008_data_flat155 = (CoefficientMerge.fastMerge block008_data_flat145 block008_data_flat154) := by decide +kernel
theorem block008_data_flat155_original : block008_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded))))) := by
  rw [block008_data_flat155_step, block008_data_flat145_original, block008_data_flat154_original]
def block008_data_flat156 : CoefficientMerge.Poly := [(nat_lit 603, Int.ofNat (nat_lit 38442326630400)), (nat_lit 604, Int.ofNat (nat_lit 33296838220800)), (nat_lit 605, Int.ofNat (nat_lit 35034243552000)), (nat_lit 606, Int.ofNat (nat_lit 23005861401600)), (nat_lit 607, Int.ofNat (nat_lit 17860372992000)), (nat_lit 608, Int.ofNat (nat_lit 12714884582400)), (nat_lit 609, Int.ofNat (nat_lit 13581177218928)), (nat_lit 610, Int.ofNat (nat_lit 26079185843568)), (nat_lit 611, Int.ofNat (nat_lit 36938767228704)), (nat_lit 612, Int.ofNat (nat_lit 59715261042624)), (nat_lit 613, Int.ofNat (nat_lit 45908642102400)), (nat_lit 614, Int.ofNat (nat_lit 28427760345600)), (nat_lit 615, Int.ofNat (nat_lit 25733885184000)), (nat_lit 616, Int.ofNat (nat_lit 11217499776000)), (nat_lit 617, Int.ofNat (nat_lit 6633852825600)), (nat_lit 618, Int.ofNat (nat_lit 29512140134400)), (nat_lit 620, Int.ofNat (nat_lit 6208605849600)), (nat_lit 626, Int.ofNat (nat_lit 85347068083200)), (nat_lit 627, Int.ofNat (nat_lit 162444344832000)), (nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
theorem block008_data_flat156_step : block008_data_flat156 = (CoefficientMerge.fastMerge block008_data_flat136 block008_data_flat155) := by decide +kernel
theorem block008_data_flat156_original : block008_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded)))))) := by
  rw [block008_data_flat156_step, block008_data_flat136_original, block008_data_flat155_original]
def block008_data_flat157 : CoefficientMerge.Poly := [(nat_lit 451, Int.ofNat (nat_lit 329949128678400)), (nat_lit 452, Int.ofNat (nat_lit 342153716889600)), (nat_lit 453, Int.ofNat (nat_lit 283937405875200)), (nat_lit 454, Int.ofNat (nat_lit 163805135155200)), (nat_lit 455, Int.ofNat (nat_lit 171417056025600)), (nat_lit 475, Int.ofNat (nat_lit 137682213419520)), (nat_lit 476, Int.ofNat (nat_lit 278791917465600)), (nat_lit 477, Int.ofNat (nat_lit 292017098419200)), (nat_lit 478, Int.ofNat (nat_lit 172905420441600)), (nat_lit 479, Int.ofNat (nat_lit 181537934054400)), (nat_lit 500, Int.ofNat (nat_lit 142925508633600)), (nat_lit 501, Int.ofNat (nat_lit 300096790963200)), (nat_lit 502, Int.ofNat (nat_lit 182005705728000)), (nat_lit 503, Int.ofNat (nat_lit 167207110963200)), (nat_lit 525, Int.ofNat (nat_lit 154088241753600)), (nat_lit 526, Int.ofNat (nat_lit 191105991014400)), (nat_lit 527, Int.ofNat (nat_lit 177327988992000)), (nat_lit 550, Int.ofNat (nat_lit 22316002884000)), (nat_lit 551, Int.ofNat (nat_lit 35848320076800)), (nat_lit 602, Int.ofNat (nat_lit 43587815040000)), (nat_lit 603, Int.ofNat (nat_lit 38442326630400)), (nat_lit 604, Int.ofNat (nat_lit 33296838220800)), (nat_lit 605, Int.ofNat (nat_lit 35034243552000)), (nat_lit 606, Int.ofNat (nat_lit 23005861401600)), (nat_lit 607, Int.ofNat (nat_lit 17860372992000)), (nat_lit 608, Int.ofNat (nat_lit 12714884582400)), (nat_lit 609, Int.ofNat (nat_lit 13581177218928)), (nat_lit 610, Int.ofNat (nat_lit 26079185843568)), (nat_lit 611, Int.ofNat (nat_lit 36938767228704)), (nat_lit 612, Int.ofNat (nat_lit 59715261042624)), (nat_lit 613, Int.ofNat (nat_lit 45908642102400)), (nat_lit 614, Int.ofNat (nat_lit 28427760345600)), (nat_lit 615, Int.ofNat (nat_lit 25733885184000)), (nat_lit 616, Int.ofNat (nat_lit 11217499776000)), (nat_lit 617, Int.ofNat (nat_lit 6633852825600)), (nat_lit 618, Int.ofNat (nat_lit 29512140134400)), (nat_lit 620, Int.ofNat (nat_lit 6208605849600)), (nat_lit 626, Int.ofNat (nat_lit 85347068083200)), (nat_lit 627, Int.ofNat (nat_lit 162444344832000)), (nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
theorem block008_data_flat157_step : block008_data_flat157 = (CoefficientMerge.fastMerge block008_data_flat117 block008_data_flat156) := by decide +kernel
theorem block008_data_flat157_original : block008_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded))))))) := by
  rw [block008_data_flat157_step, block008_data_flat117_original, block008_data_flat156_original]
def block008_data_flat158 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 280362100233600)), (nat_lit 332, Int.ofNat (nat_lit 283858818566400)), (nat_lit 333, Int.ofNat (nat_lit 220539543840000)), (nat_lit 334, Int.ofNat (nat_lit 165174808478400)), (nat_lit 335, Int.ofNat (nat_lit 153751952692800)), (nat_lit 350, Int.ofNat (nat_lit 180207265392000)), (nat_lit 351, Int.ofNat (nat_lit 326270355747840)), (nat_lit 352, Int.ofNat (nat_lit 298937896306560)), (nat_lit 353, Int.ofNat (nat_lit 297051845428800)), (nat_lit 354, Int.ofNat (nat_lit 320423596416000)), (nat_lit 355, Int.ofNat (nat_lit 262910161067400)), (nat_lit 356, Int.ofNat (nat_lit 266247131673600)), (nat_lit 357, Int.ofNat (nat_lit 203948449689600)), (nat_lit 358, Int.ofNat (nat_lit 163012699899000)), (nat_lit 359, Int.ofNat (nat_lit 150660684682200)), (nat_lit 375, Int.ofNat (nat_lit 185418634867200)), (nat_lit 376, Int.ofNat (nat_lit 335715348810240)), (nat_lit 377, Int.ofNat (nat_lit 309666780864000)), (nat_lit 378, Int.ofNat (nat_lit 331449735052800)), (nat_lit 379, Int.ofNat (nat_lit 269855932147200)), (nat_lit 380, Int.ofNat (nat_lit 278367314803200)), (nat_lit 381, Int.ofNat (nat_lit 216773511897600)), (nat_lit 382, Int.ofNat (nat_lit 154848692880000)), (nat_lit 383, Int.ofNat (nat_lit 139633710451200)), (nat_lit 400, Int.ofNat (nat_lit 190423018598400)), (nat_lit 401, Int.ofNat (nat_lit 337110459571200)), (nat_lit 402, Int.ofNat (nat_lit 339520246128000)), (nat_lit 403, Int.ofNat (nat_lit 272720067177600)), (nat_lit 404, Int.ofNat (nat_lit 269798105001600)), (nat_lit 405, Int.ofNat (nat_lit 202997926051200)), (nat_lit 406, Int.ofNat (nat_lit 129247858454400)), (nat_lit 407, Int.ofNat (nat_lit 121733228937600)), (nat_lit 425, Int.ofNat (nat_lit 187597703462400)), (nat_lit 426, Int.ofNat (nat_lit 350073941817600)), (nat_lit 427, Int.ofNat (nat_lit 283033756051200)), (nat_lit 428, Int.ofNat (nat_lit 278611187500800)), (nat_lit 429, Int.ofNat (nat_lit 211571001734400)), (nat_lit 430, Int.ofNat (nat_lit 135196644844800)), (nat_lit 431, Int.ofNat (nat_lit 126181408953600)), (nat_lit 450, Int.ofNat (nat_lit 194082719846400)), (nat_lit 451, Int.ofNat (nat_lit 329949128678400)), (nat_lit 452, Int.ofNat (nat_lit 342153716889600)), (nat_lit 453, Int.ofNat (nat_lit 283937405875200)), (nat_lit 454, Int.ofNat (nat_lit 163805135155200)), (nat_lit 455, Int.ofNat (nat_lit 171417056025600)), (nat_lit 475, Int.ofNat (nat_lit 137682213419520)), (nat_lit 476, Int.ofNat (nat_lit 278791917465600)), (nat_lit 477, Int.ofNat (nat_lit 292017098419200)), (nat_lit 478, Int.ofNat (nat_lit 172905420441600)), (nat_lit 479, Int.ofNat (nat_lit 181537934054400)), (nat_lit 500, Int.ofNat (nat_lit 142925508633600)), (nat_lit 501, Int.ofNat (nat_lit 300096790963200)), (nat_lit 502, Int.ofNat (nat_lit 182005705728000)), (nat_lit 503, Int.ofNat (nat_lit 167207110963200)), (nat_lit 525, Int.ofNat (nat_lit 154088241753600)), (nat_lit 526, Int.ofNat (nat_lit 191105991014400)), (nat_lit 527, Int.ofNat (nat_lit 177327988992000)), (nat_lit 550, Int.ofNat (nat_lit 22316002884000)), (nat_lit 551, Int.ofNat (nat_lit 35848320076800)), (nat_lit 602, Int.ofNat (nat_lit 43587815040000)), (nat_lit 603, Int.ofNat (nat_lit 38442326630400)), (nat_lit 604, Int.ofNat (nat_lit 33296838220800)), (nat_lit 605, Int.ofNat (nat_lit 35034243552000)), (nat_lit 606, Int.ofNat (nat_lit 23005861401600)), (nat_lit 607, Int.ofNat (nat_lit 17860372992000)), (nat_lit 608, Int.ofNat (nat_lit 12714884582400)), (nat_lit 609, Int.ofNat (nat_lit 13581177218928)), (nat_lit 610, Int.ofNat (nat_lit 26079185843568)), (nat_lit 611, Int.ofNat (nat_lit 36938767228704)), (nat_lit 612, Int.ofNat (nat_lit 59715261042624)), (nat_lit 613, Int.ofNat (nat_lit 45908642102400)), (nat_lit 614, Int.ofNat (nat_lit 28427760345600)), (nat_lit 615, Int.ofNat (nat_lit 25733885184000)), (nat_lit 616, Int.ofNat (nat_lit 11217499776000)), (nat_lit 617, Int.ofNat (nat_lit 6633852825600)), (nat_lit 618, Int.ofNat (nat_lit 29512140134400)), (nat_lit 620, Int.ofNat (nat_lit 6208605849600)), (nat_lit 626, Int.ofNat (nat_lit 85347068083200)), (nat_lit 627, Int.ofNat (nat_lit 162444344832000)), (nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
theorem block008_data_flat158_step : block008_data_flat158 = (CoefficientMerge.fastMerge block008_data_flat078 block008_data_flat157) := by decide +kernel
theorem block008_data_flat158_original : block008_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded)))))))) := by
  rw [block008_data_flat158_step, block008_data_flat078_original, block008_data_flat157_original]
def block008_data_flat159 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 280362100233600)), (nat_lit 332, Int.ofNat (nat_lit 283858818566400)), (nat_lit 333, Int.ofNat (nat_lit 220539543840000)), (nat_lit 334, Int.ofNat (nat_lit 165174808478400)), (nat_lit 335, Int.ofNat (nat_lit 153751952692800)), (nat_lit 350, Int.ofNat (nat_lit 180207265392000)), (nat_lit 351, Int.ofNat (nat_lit 326270355747840)), (nat_lit 352, Int.ofNat (nat_lit 298937896306560)), (nat_lit 353, Int.ofNat (nat_lit 297051845428800)), (nat_lit 354, Int.ofNat (nat_lit 320423596416000)), (nat_lit 355, Int.ofNat (nat_lit 262910161067400)), (nat_lit 356, Int.ofNat (nat_lit 266247131673600)), (nat_lit 357, Int.ofNat (nat_lit 203948449689600)), (nat_lit 358, Int.ofNat (nat_lit 163012699899000)), (nat_lit 359, Int.ofNat (nat_lit 150660684682200)), (nat_lit 375, Int.ofNat (nat_lit 185418634867200)), (nat_lit 376, Int.ofNat (nat_lit 335715348810240)), (nat_lit 377, Int.ofNat (nat_lit 309666780864000)), (nat_lit 378, Int.ofNat (nat_lit 331449735052800)), (nat_lit 379, Int.ofNat (nat_lit 269855932147200)), (nat_lit 380, Int.ofNat (nat_lit 278367314803200)), (nat_lit 381, Int.ofNat (nat_lit 216773511897600)), (nat_lit 382, Int.ofNat (nat_lit 154848692880000)), (nat_lit 383, Int.ofNat (nat_lit 139633710451200)), (nat_lit 400, Int.ofNat (nat_lit 190423018598400)), (nat_lit 401, Int.ofNat (nat_lit 337110459571200)), (nat_lit 402, Int.ofNat (nat_lit 339520246128000)), (nat_lit 403, Int.ofNat (nat_lit 272720067177600)), (nat_lit 404, Int.ofNat (nat_lit 269798105001600)), (nat_lit 405, Int.ofNat (nat_lit 202997926051200)), (nat_lit 406, Int.ofNat (nat_lit 129247858454400)), (nat_lit 407, Int.ofNat (nat_lit 121733228937600)), (nat_lit 425, Int.ofNat (nat_lit 187597703462400)), (nat_lit 426, Int.ofNat (nat_lit 350073941817600)), (nat_lit 427, Int.ofNat (nat_lit 283033756051200)), (nat_lit 428, Int.ofNat (nat_lit 278611187500800)), (nat_lit 429, Int.ofNat (nat_lit 211571001734400)), (nat_lit 430, Int.ofNat (nat_lit 135196644844800)), (nat_lit 431, Int.ofNat (nat_lit 126181408953600)), (nat_lit 450, Int.ofNat (nat_lit 194082719846400)), (nat_lit 451, Int.ofNat (nat_lit 329949128678400)), (nat_lit 452, Int.ofNat (nat_lit 342153716889600)), (nat_lit 453, Int.ofNat (nat_lit 283937405875200)), (nat_lit 454, Int.ofNat (nat_lit 163805135155200)), (nat_lit 455, Int.ofNat (nat_lit 171417056025600)), (nat_lit 475, Int.ofNat (nat_lit 137682213419520)), (nat_lit 476, Int.ofNat (nat_lit 278791917465600)), (nat_lit 477, Int.ofNat (nat_lit 292017098419200)), (nat_lit 478, Int.ofNat (nat_lit 172905420441600)), (nat_lit 479, Int.ofNat (nat_lit 181537934054400)), (nat_lit 500, Int.ofNat (nat_lit 142925508633600)), (nat_lit 501, Int.ofNat (nat_lit 300096790963200)), (nat_lit 502, Int.ofNat (nat_lit 182005705728000)), (nat_lit 503, Int.ofNat (nat_lit 167207110963200)), (nat_lit 525, Int.ofNat (nat_lit 154088241753600)), (nat_lit 526, Int.ofNat (nat_lit 191105991014400)), (nat_lit 527, Int.ofNat (nat_lit 177327988992000)), (nat_lit 550, Int.ofNat (nat_lit 22316002884000)), (nat_lit 551, Int.ofNat (nat_lit 35848320076800)), (nat_lit 602, Int.ofNat (nat_lit 43587815040000)), (nat_lit 603, Int.ofNat (nat_lit 38442326630400)), (nat_lit 604, Int.ofNat (nat_lit 33296838220800)), (nat_lit 605, Int.ofNat (nat_lit 35034243552000)), (nat_lit 606, Int.ofNat (nat_lit 23005861401600)), (nat_lit 607, Int.ofNat (nat_lit 17860372992000)), (nat_lit 608, Int.ofNat (nat_lit 12714884582400)), (nat_lit 609, Int.ofNat (nat_lit 13581177218928)), (nat_lit 610, Int.ofNat (nat_lit 26079185843568)), (nat_lit 611, Int.ofNat (nat_lit 36938767228704)), (nat_lit 612, Int.ofNat (nat_lit 59715261042624)), (nat_lit 613, Int.ofNat (nat_lit 45908642102400)), (nat_lit 614, Int.ofNat (nat_lit 28427760345600)), (nat_lit 615, Int.ofNat (nat_lit 25733885184000)), (nat_lit 616, Int.ofNat (nat_lit 11217499776000)), (nat_lit 617, Int.ofNat (nat_lit 6633852825600)), (nat_lit 618, Int.ofNat (nat_lit 29512140134400)), (nat_lit 620, Int.ofNat (nat_lit 6208605849600)), (nat_lit 626, Int.ofNat (nat_lit 85347068083200)), (nat_lit 627, Int.ofNat (nat_lit 162444344832000)), (nat_lit 628, Int.ofNat (nat_lit 154194553497600))]
theorem block008_data_flat159_step : block008_data_flat159 = (CoefficientMerge.trim block008_data_flat158) := by decide +kernel
theorem block008_data_flat159_original : block008_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded))))))))) := by
  rw [block008_data_flat159_step, block008_data_flat158_original]
theorem block008_data : block008 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (280362100233600 : Int) atom0449Coded) (CoefficientMerge.scale (283858818566400 : Int) atom0450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220539543840000 : Int) atom0451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165174808478400 : Int) atom0452Coded) (CoefficientMerge.scale (153751952692800 : Int) atom0453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180207265392000 : Int) atom0454Coded) (CoefficientMerge.scale (326270355747840 : Int) atom0455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298937896306560 : Int) atom0456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (297051845428800 : Int) atom0457Coded) (CoefficientMerge.scale (320423596416000 : Int) atom0458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262910161067400 : Int) atom0459Coded) (CoefficientMerge.scale (266247131673600 : Int) atom0460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203948449689600 : Int) atom0461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163012699899000 : Int) atom0462Coded) (CoefficientMerge.scale (150660684682200 : Int) atom0463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (185418634867200 : Int) atom0464Coded) (CoefficientMerge.scale (335715348810240 : Int) atom0465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (309666780864000 : Int) atom0466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (331449735052800 : Int) atom0467Coded) (CoefficientMerge.scale (269855932147200 : Int) atom0468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278367314803200 : Int) atom0469Coded) (CoefficientMerge.scale (216773511897600 : Int) atom0470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154848692880000 : Int) atom0471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139633710451200 : Int) atom0472Coded) (CoefficientMerge.scale (190423018598400 : Int) atom0473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337110459571200 : Int) atom0474Coded) (CoefficientMerge.scale (339520246128000 : Int) atom0475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (272720067177600 : Int) atom0476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269798105001600 : Int) atom0477Coded) (CoefficientMerge.scale (202997926051200 : Int) atom0478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129247858454400 : Int) atom0479Coded) (CoefficientMerge.scale (121733228937600 : Int) atom0480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (187597703462400 : Int) atom0481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (350073941817600 : Int) atom0482Coded) (CoefficientMerge.scale (283033756051200 : Int) atom0483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (278611187500800 : Int) atom0484Coded) (CoefficientMerge.scale (211571001734400 : Int) atom0485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135196644844800 : Int) atom0486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126181408953600 : Int) atom0487Coded) (CoefficientMerge.scale (194082719846400 : Int) atom0488Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (329949128678400 : Int) atom0489Coded) (CoefficientMerge.scale (342153716889600 : Int) atom0490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283937405875200 : Int) atom0491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (163805135155200 : Int) atom0492Coded) (CoefficientMerge.scale (171417056025600 : Int) atom0493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (137682213419520 : Int) atom0494Coded) (CoefficientMerge.scale (278791917465600 : Int) atom0495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292017098419200 : Int) atom0496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172905420441600 : Int) atom0497Coded) (CoefficientMerge.scale (181537934054400 : Int) atom0498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142925508633600 : Int) atom0499Coded) (CoefficientMerge.scale (300096790963200 : Int) atom0500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182005705728000 : Int) atom0501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (167207110963200 : Int) atom0502Coded) (CoefficientMerge.scale (154088241753600 : Int) atom0503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191105991014400 : Int) atom0504Coded) (CoefficientMerge.scale (177327988992000 : Int) atom0505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22316002884000 : Int) atom0506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35848320076800 : Int) atom0507Coded) (CoefficientMerge.scale (43587815040000 : Int) atom0508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38442326630400 : Int) atom0509Coded) (CoefficientMerge.scale (33296838220800 : Int) atom0510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35034243552000 : Int) atom0511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23005861401600 : Int) atom0512Coded) (CoefficientMerge.scale (17860372992000 : Int) atom0513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12714884582400 : Int) atom0514Coded) (CoefficientMerge.scale (13581177218928 : Int) atom0515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26079185843568 : Int) atom0516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36938767228704 : Int) atom0517Coded) (CoefficientMerge.scale (59715261042624 : Int) atom0518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45908642102400 : Int) atom0519Coded) (CoefficientMerge.scale (28427760345600 : Int) atom0520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25733885184000 : Int) atom0521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11217499776000 : Int) atom0522Coded) (CoefficientMerge.scale (6633852825600 : Int) atom0523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29512140134400 : Int) atom0524Coded) (CoefficientMerge.scale (6208605849600 : Int) atom0525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85347068083200 : Int) atom0526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (162444344832000 : Int) atom0527Coded) (CoefficientMerge.scale (154194553497600 : Int) atom0528Coded)))))))) := by
  have h : block008 = block008_data_flat159 := by decide +kernel
  exact h.trans block008_data_flat159_original
theorem block008_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block008 := by
  rw [block008_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0449Coded_nonneg g hg hA hB) (atom0450Coded_nonneg g hg hA hB)) (add_nonneg (atom0451Coded_nonneg g hg hA hB) (add_nonneg (atom0452Coded_nonneg g hg hA hB) (atom0453Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0454Coded_nonneg g hg hA hB) (atom0455Coded_nonneg g hg hA hB)) (add_nonneg (atom0456Coded_nonneg g hg hA hB) (add_nonneg (atom0457Coded_nonneg g hg hA hB) (atom0458Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0459Coded_nonneg g hg hA hB) (atom0460Coded_nonneg g hg hA hB)) (add_nonneg (atom0461Coded_nonneg g hg hA hB) (add_nonneg (atom0462Coded_nonneg g hg hA hB) (atom0463Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0464Coded_nonneg g hg hA hB) (atom0465Coded_nonneg g hg hA hB)) (add_nonneg (atom0466Coded_nonneg g hg hA hB) (add_nonneg (atom0467Coded_nonneg g hg hA hB) (atom0468Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0469Coded_nonneg g hg hA hB) (atom0470Coded_nonneg g hg hA hB)) (add_nonneg (atom0471Coded_nonneg g hg hA hB) (add_nonneg (atom0472Coded_nonneg g hg hA hB) (atom0473Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0474Coded_nonneg g hg hA hB) (atom0475Coded_nonneg g hg hA hB)) (add_nonneg (atom0476Coded_nonneg g hg hA hB) (add_nonneg (atom0477Coded_nonneg g hg hA hB) (atom0478Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0479Coded_nonneg g hg hA hB) (atom0480Coded_nonneg g hg hA hB)) (add_nonneg (atom0481Coded_nonneg g hg hA hB) (add_nonneg (atom0482Coded_nonneg g hg hA hB) (atom0483Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0484Coded_nonneg g hg hA hB) (atom0485Coded_nonneg g hg hA hB)) (add_nonneg (atom0486Coded_nonneg g hg hA hB) (add_nonneg (atom0487Coded_nonneg g hg hA hB) (atom0488Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0489Coded_nonneg g hg hA hB) (atom0490Coded_nonneg g hg hA hB)) (add_nonneg (atom0491Coded_nonneg g hg hA hB) (add_nonneg (atom0492Coded_nonneg g hg hA hB) (atom0493Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0494Coded_nonneg g hg hA hB) (atom0495Coded_nonneg g hg hA hB)) (add_nonneg (atom0496Coded_nonneg g hg hA hB) (add_nonneg (atom0497Coded_nonneg g hg hA hB) (atom0498Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0499Coded_nonneg g hg hA hB) (atom0500Coded_nonneg g hg hA hB)) (add_nonneg (atom0501Coded_nonneg g hg hA hB) (add_nonneg (atom0502Coded_nonneg g hg hA hB) (atom0503Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0504Coded_nonneg g hg hA hB) (atom0505Coded_nonneg g hg hA hB)) (add_nonneg (atom0506Coded_nonneg g hg hA hB) (add_nonneg (atom0507Coded_nonneg g hg hA hB) (atom0508Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0509Coded_nonneg g hg hA hB) (atom0510Coded_nonneg g hg hA hB)) (add_nonneg (atom0511Coded_nonneg g hg hA hB) (add_nonneg (atom0512Coded_nonneg g hg hA hB) (atom0513Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0514Coded_nonneg g hg hA hB) (atom0515Coded_nonneg g hg hA hB)) (add_nonneg (atom0516Coded_nonneg g hg hA hB) (add_nonneg (atom0517Coded_nonneg g hg hA hB) (atom0518Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0519Coded_nonneg g hg hA hB) (atom0520Coded_nonneg g hg hA hB)) (add_nonneg (atom0521Coded_nonneg g hg hA hB) (add_nonneg (atom0522Coded_nonneg g hg hA hB) (atom0523Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0524Coded_nonneg g hg hA hB) (atom0525Coded_nonneg g hg hA hB)) (add_nonneg (atom0526Coded_nonneg g hg hA hB) (add_nonneg (atom0527Coded_nonneg g hg hA hB) (atom0528Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
