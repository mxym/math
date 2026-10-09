-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2449 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2449 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2449 = ((g 15) * (g 15) * (g 21)) := by
  norm_num [atom2449, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2449_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65163300249600 : Int) atom2449) := by
  rw [SparsePolynomial.eval_scale, eval_atom2449]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2449Coded : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 1))]
theorem atom2449Coded_decode : atom2449 = SparsePolynomial.decodeCubic 24 atom2449Coded := by decide +kernel
theorem atom2449Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) := by
  have h := atom2449_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2449Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2450 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2450 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2450 = ((g 15) * (g 15) * (g 23)) := by
  norm_num [atom2450, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2450_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5211208396800 : Int) atom2450) := by
  rw [SparsePolynomial.eval_scale, eval_atom2450]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2450Coded : CoefficientMerge.Poly := [(nat_lit 9023, Int.ofNat (nat_lit 1))]
theorem atom2450Coded_decode : atom2450 = SparsePolynomial.decodeCubic 24 atom2450Coded := by decide +kernel
theorem atom2450Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded) := by
  have h := atom2450_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2450Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2451 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2451 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2451 = ((g 15) * (g 16) * (g 18)) := by
  norm_num [atom2451, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2451_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24896019778560 : Int) atom2451) := by
  rw [SparsePolynomial.eval_scale, eval_atom2451]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2451Coded : CoefficientMerge.Poly := [(nat_lit 9042, Int.ofNat (nat_lit 1))]
theorem atom2451Coded_decode : atom2451 = SparsePolynomial.decodeCubic 24 atom2451Coded := by decide +kernel
theorem atom2451Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) := by
  have h := atom2451_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2451Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2452 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2452 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2452 = ((g 15) * (g 16) * (g 20)) := by
  norm_num [atom2452, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2452_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (233856198374400 : Int) atom2452) := by
  rw [SparsePolynomial.eval_scale, eval_atom2452]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2452Coded : CoefficientMerge.Poly := [(nat_lit 9044, Int.ofNat (nat_lit 1))]
theorem atom2452Coded_decode : atom2452 = SparsePolynomial.decodeCubic 24 atom2452Coded := by decide +kernel
theorem atom2452Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) := by
  have h := atom2452_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2452Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2453 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2453 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2453 = ((g 15) * (g 16) * (g 21)) := by
  norm_num [atom2453, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2453_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220828821696000 : Int) atom2453) := by
  rw [SparsePolynomial.eval_scale, eval_atom2453]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2453Coded : CoefficientMerge.Poly := [(nat_lit 9045, Int.ofNat (nat_lit 1))]
theorem atom2453Coded_decode : atom2453 = SparsePolynomial.decodeCubic 24 atom2453Coded := by decide +kernel
theorem atom2453Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded) := by
  have h := atom2453_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2453Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2454 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2454 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2454 = ((g 15) * (g 16) * (g 22)) := by
  norm_num [atom2454, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2454_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99469520156160 : Int) atom2454) := by
  rw [SparsePolynomial.eval_scale, eval_atom2454]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2454Coded : CoefficientMerge.Poly := [(nat_lit 9046, Int.ofNat (nat_lit 1))]
theorem atom2454Coded_decode : atom2454 = SparsePolynomial.decodeCubic 24 atom2454Coded := by decide +kernel
theorem atom2454Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) := by
  have h := atom2454_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2454Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2455 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2455 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2455 = ((g 15) * (g 16) * (g 23)) := by
  norm_num [atom2455, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2455_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (259121345414400 : Int) atom2455) := by
  rw [SparsePolynomial.eval_scale, eval_atom2455]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2455Coded : CoefficientMerge.Poly := [(nat_lit 9047, Int.ofNat (nat_lit 1))]
theorem atom2455Coded_decode : atom2455 = SparsePolynomial.decodeCubic 24 atom2455Coded := by decide +kernel
theorem atom2455Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded) := by
  have h := atom2455_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2455Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2456 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2456 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2456 = ((g 15) * (g 17) * (g 17)) := by
  norm_num [atom2456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2456_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8561639116800 : Int) atom2456) := by
  rw [SparsePolynomial.eval_scale, eval_atom2456]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2456Coded : CoefficientMerge.Poly := [(nat_lit 9065, Int.ofNat (nat_lit 1))]
theorem atom2456Coded_decode : atom2456 = SparsePolynomial.decodeCubic 24 atom2456Coded := by decide +kernel
theorem atom2456Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) := by
  have h := atom2456_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2456Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2457 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2457 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2457 = ((g 15) * (g 17) * (g 18)) := by
  norm_num [atom2457, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2457_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35057102976000 : Int) atom2457) := by
  rw [SparsePolynomial.eval_scale, eval_atom2457]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2457Coded : CoefficientMerge.Poly := [(nat_lit 9066, Int.ofNat (nat_lit 1))]
theorem atom2457Coded_decode : atom2457 = SparsePolynomial.decodeCubic 24 atom2457Coded := by decide +kernel
theorem atom2457Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) := by
  have h := atom2457_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2457Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2458 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2458 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2458 = ((g 15) * (g 17) * (g 19)) := by
  norm_num [atom2458, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2458_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40411348992000 : Int) atom2458) := by
  rw [SparsePolynomial.eval_scale, eval_atom2458]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2458Coded : CoefficientMerge.Poly := [(nat_lit 9067, Int.ofNat (nat_lit 1))]
theorem atom2458Coded_decode : atom2458 = SparsePolynomial.decodeCubic 24 atom2458Coded := by decide +kernel
theorem atom2458Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded) := by
  have h := atom2458_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2458Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2459 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2459 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2459 = ((g 15) * (g 17) * (g 20)) := by
  norm_num [atom2459, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2459_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (327449191910400 : Int) atom2459) := by
  rw [SparsePolynomial.eval_scale, eval_atom2459]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2459Coded : CoefficientMerge.Poly := [(nat_lit 9068, Int.ofNat (nat_lit 1))]
theorem atom2459Coded_decode : atom2459 = SparsePolynomial.decodeCubic 24 atom2459Coded := by decide +kernel
theorem atom2459Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) := by
  have h := atom2459_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2459Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2460 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2460 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2460 = ((g 15) * (g 17) * (g 21)) := by
  norm_num [atom2460, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2460_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349177379443200 : Int) atom2460) := by
  rw [SparsePolynomial.eval_scale, eval_atom2460]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2460Coded : CoefficientMerge.Poly := [(nat_lit 9069, Int.ofNat (nat_lit 1))]
theorem atom2460Coded_decode : atom2460 = SparsePolynomial.decodeCubic 24 atom2460Coded := by decide +kernel
theorem atom2460Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded) := by
  have h := atom2460_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2460Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2461 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2461 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2461 = ((g 15) * (g 17) * (g 22)) := by
  norm_num [atom2461, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2461_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (284381337945600 : Int) atom2461) := by
  rw [SparsePolynomial.eval_scale, eval_atom2461]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2461Coded : CoefficientMerge.Poly := [(nat_lit 9070, Int.ofNat (nat_lit 1))]
theorem atom2461Coded_decode : atom2461 = SparsePolynomial.decodeCubic 24 atom2461Coded := by decide +kernel
theorem atom2461Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) := by
  have h := atom2461_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2461Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2462 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2462 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2462 = ((g 15) * (g 17) * (g 23)) := by
  norm_num [atom2462, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2462_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (503972755372800 : Int) atom2462) := by
  rw [SparsePolynomial.eval_scale, eval_atom2462]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2462Coded : CoefficientMerge.Poly := [(nat_lit 9071, Int.ofNat (nat_lit 1))]
theorem atom2462Coded_decode : atom2462 = SparsePolynomial.decodeCubic 24 atom2462Coded := by decide +kernel
theorem atom2462Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) := by
  have h := atom2462_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2462Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2463 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2463 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2463 = ((g 15) * (g 18) * (g 18)) := by
  norm_num [atom2463, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2463_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71490459801600 : Int) atom2463) := by
  rw [SparsePolynomial.eval_scale, eval_atom2463]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2463Coded : CoefficientMerge.Poly := [(nat_lit 9090, Int.ofNat (nat_lit 1))]
theorem atom2463Coded_decode : atom2463 = SparsePolynomial.decodeCubic 24 atom2463Coded := by decide +kernel
theorem atom2463Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded) := by
  have h := atom2463_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2463Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2464 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2464 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2464 = ((g 15) * (g 18) * (g 19)) := by
  norm_num [atom2464, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2464_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (197412532531200 : Int) atom2464) := by
  rw [SparsePolynomial.eval_scale, eval_atom2464]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2464Coded : CoefficientMerge.Poly := [(nat_lit 9091, Int.ofNat (nat_lit 1))]
theorem atom2464Coded_decode : atom2464 = SparsePolynomial.decodeCubic 24 atom2464Coded := by decide +kernel
theorem atom2464Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) := by
  have h := atom2464_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2464Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2465 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2465 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2465 = ((g 15) * (g 18) * (g 20)) := by
  norm_num [atom2465, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2465_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (533527742361600 : Int) atom2465) := by
  rw [SparsePolynomial.eval_scale, eval_atom2465]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2465Coded : CoefficientMerge.Poly := [(nat_lit 9092, Int.ofNat (nat_lit 1))]
theorem atom2465Coded_decode : atom2465 = SparsePolynomial.decodeCubic 24 atom2465Coded := by decide +kernel
theorem atom2465Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded) := by
  have h := atom2465_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2465Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2466 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2466 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2466 = ((g 15) * (g 18) * (g 21)) := by
  norm_num [atom2466, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2466_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (587959355289600 : Int) atom2466) := by
  rw [SparsePolynomial.eval_scale, eval_atom2466]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2466Coded : CoefficientMerge.Poly := [(nat_lit 9093, Int.ofNat (nat_lit 1))]
theorem atom2466Coded_decode : atom2466 = SparsePolynomial.decodeCubic 24 atom2466Coded := by decide +kernel
theorem atom2466Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) := by
  have h := atom2466_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2466Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2467 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2467 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2467 = ((g 15) * (g 18) * (g 22)) := by
  norm_num [atom2467, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2467_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (457214273107200 : Int) atom2467) := by
  rw [SparsePolynomial.eval_scale, eval_atom2467]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2467Coded : CoefficientMerge.Poly := [(nat_lit 9094, Int.ofNat (nat_lit 1))]
theorem atom2467Coded_decode : atom2467 = SparsePolynomial.decodeCubic 24 atom2467Coded := by decide +kernel
theorem atom2467Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) := by
  have h := atom2467_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2467Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2468 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2468 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2468 = ((g 15) * (g 18) * (g 23)) := by
  norm_num [atom2468, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2468_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (739589540659200 : Int) atom2468) := by
  rw [SparsePolynomial.eval_scale, eval_atom2468]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2468Coded : CoefficientMerge.Poly := [(nat_lit 9095, Int.ofNat (nat_lit 1))]
theorem atom2468Coded_decode : atom2468 = SparsePolynomial.decodeCubic 24 atom2468Coded := by decide +kernel
theorem atom2468Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded) := by
  have h := atom2468_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2468Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2469 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2469 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2469 = ((g 15) * (g 19) * (g 19)) := by
  norm_num [atom2469, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2469_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86391113840640 : Int) atom2469) := by
  rw [SparsePolynomial.eval_scale, eval_atom2469]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2469Coded : CoefficientMerge.Poly := [(nat_lit 9115, Int.ofNat (nat_lit 1))]
theorem atom2469Coded_decode : atom2469 = SparsePolynomial.decodeCubic 24 atom2469Coded := by decide +kernel
theorem atom2469Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) := by
  have h := atom2469_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2469Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2470 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2470 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2470 = ((g 15) * (g 19) * (g 20)) := by
  norm_num [atom2470, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2470_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (505631540736000 : Int) atom2470) := by
  rw [SparsePolynomial.eval_scale, eval_atom2470]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2470Coded : CoefficientMerge.Poly := [(nat_lit 9116, Int.ofNat (nat_lit 1))]
theorem atom2470Coded_decode : atom2470 = SparsePolynomial.decodeCubic 24 atom2470Coded := by decide +kernel
theorem atom2470Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded) := by
  have h := atom2470_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2470Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2471 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2471 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2471 = ((g 15) * (g 19) * (g 21)) := by
  norm_num [atom2471, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2471_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (646813536768000 : Int) atom2471) := by
  rw [SparsePolynomial.eval_scale, eval_atom2471]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2471Coded : CoefficientMerge.Poly := [(nat_lit 9117, Int.ofNat (nat_lit 1))]
theorem atom2471Coded_decode : atom2471 = SparsePolynomial.decodeCubic 24 atom2471Coded := by decide +kernel
theorem atom2471Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) := by
  have h := atom2471_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2471Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2472 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2472 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2472 = ((g 15) * (g 19) * (g 22)) := by
  norm_num [atom2472, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2472_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (564551442201600 : Int) atom2472) := by
  rw [SparsePolynomial.eval_scale, eval_atom2472]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2472Coded : CoefficientMerge.Poly := [(nat_lit 9118, Int.ofNat (nat_lit 1))]
theorem atom2472Coded_decode : atom2472 = SparsePolynomial.decodeCubic 24 atom2472Coded := by decide +kernel
theorem atom2472Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) := by
  have h := atom2472_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2472Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2473 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2473 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2473 = ((g 15) * (g 19) * (g 23)) := by
  norm_num [atom2473, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2473_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (760681790668800 : Int) atom2473) := by
  rw [SparsePolynomial.eval_scale, eval_atom2473]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2473Coded : CoefficientMerge.Poly := [(nat_lit 9119, Int.ofNat (nat_lit 1))]
theorem atom2473Coded_decode : atom2473 = SparsePolynomial.decodeCubic 24 atom2473Coded := by decide +kernel
theorem atom2473Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded) := by
  have h := atom2473_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2473Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2474 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2474 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2474 = ((g 15) * (g 20) * (g 20)) := by
  norm_num [atom2474, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2474_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379709468006400 : Int) atom2474) := by
  rw [SparsePolynomial.eval_scale, eval_atom2474]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2474Coded : CoefficientMerge.Poly := [(nat_lit 9140, Int.ofNat (nat_lit 1))]
theorem atom2474Coded_decode : atom2474 = SparsePolynomial.decodeCubic 24 atom2474Coded := by decide +kernel
theorem atom2474Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) := by
  have h := atom2474_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2474Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2475 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2475 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2475 = ((g 15) * (g 20) * (g 21)) := by
  norm_num [atom2475, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2475_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (776088617472000 : Int) atom2475) := by
  rw [SparsePolynomial.eval_scale, eval_atom2475]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2475Coded : CoefficientMerge.Poly := [(nat_lit 9141, Int.ofNat (nat_lit 1))]
theorem atom2475Coded_decode : atom2475 = SparsePolynomial.decodeCubic 24 atom2475Coded := by decide +kernel
theorem atom2475Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded) := by
  have h := atom2475_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2475Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2476 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2476 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2476 = ((g 15) * (g 20) * (g 22)) := by
  norm_num [atom2476, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2476_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (671767480339200 : Int) atom2476) := by
  rw [SparsePolynomial.eval_scale, eval_atom2476]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2476Coded : CoefficientMerge.Poly := [(nat_lit 9142, Int.ofNat (nat_lit 1))]
theorem atom2476Coded_decode : atom2476 = SparsePolynomial.decodeCubic 24 atom2476Coded := by decide +kernel
theorem atom2476Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) := by
  have h := atom2476_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2476Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2477 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2477 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2477 = ((g 15) * (g 20) * (g 23)) := by
  norm_num [atom2477, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2477_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (726466161254400 : Int) atom2477) := by
  rw [SparsePolynomial.eval_scale, eval_atom2477]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2477Coded : CoefficientMerge.Poly := [(nat_lit 9143, Int.ofNat (nat_lit 1))]
theorem atom2477Coded_decode : atom2477 = SparsePolynomial.decodeCubic 24 atom2477Coded := by decide +kernel
theorem atom2477Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) := by
  have h := atom2477_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2477Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2478 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2478 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2478 = ((g 15) * (g 21) * (g 21)) := by
  norm_num [atom2478, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2478_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347050500249600 : Int) atom2478) := by
  rw [SparsePolynomial.eval_scale, eval_atom2478]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2478Coded : CoefficientMerge.Poly := [(nat_lit 9165, Int.ofNat (nat_lit 1))]
theorem atom2478Coded_decode : atom2478 = SparsePolynomial.decodeCubic 24 atom2478Coded := by decide +kernel
theorem atom2478Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded) := by
  have h := atom2478_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2478Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2479 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2479 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2479 = ((g 15) * (g 21) * (g 22)) := by
  norm_num [atom2479, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2479_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (657396548726400 : Int) atom2479) := by
  rw [SparsePolynomial.eval_scale, eval_atom2479]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2479Coded : CoefficientMerge.Poly := [(nat_lit 9166, Int.ofNat (nat_lit 1))]
theorem atom2479Coded_decode : atom2479 = SparsePolynomial.decodeCubic 24 atom2479Coded := by decide +kernel
theorem atom2479Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) := by
  have h := atom2479_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2479Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2480 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2480 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2480 = ((g 15) * (g 21) * (g 23)) := by
  norm_num [atom2480, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2480_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (747558411264000 : Int) atom2480) := by
  rw [SparsePolynomial.eval_scale, eval_atom2480]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2480Coded : CoefficientMerge.Poly := [(nat_lit 9167, Int.ofNat (nat_lit 1))]
theorem atom2480Coded_decode : atom2480 = SparsePolynomial.decodeCubic 24 atom2480Coded := by decide +kernel
theorem atom2480Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded) := by
  have h := atom2480_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2480Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2481 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 22, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2481 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2481 = ((g 15) * (g 22) * (g 22)) := by
  norm_num [atom2481, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2481_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276807592656000 : Int) atom2481) := by
  rw [SparsePolynomial.eval_scale, eval_atom2481]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2481Coded : CoefficientMerge.Poly := [(nat_lit 9190, Int.ofNat (nat_lit 1))]
theorem atom2481Coded_decode : atom2481 = SparsePolynomial.decodeCubic 24 atom2481Coded := by decide +kernel
theorem atom2481Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) := by
  have h := atom2481_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2481Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2482 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2482 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2482 = ((g 15) * (g 22) * (g 23)) := by
  norm_num [atom2482, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2482_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (682549021425600 : Int) atom2482) := by
  rw [SparsePolynomial.eval_scale, eval_atom2482]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2482Coded : CoefficientMerge.Poly := [(nat_lit 9191, Int.ofNat (nat_lit 1))]
theorem atom2482Coded_decode : atom2482 = SparsePolynomial.decodeCubic 24 atom2482Coded := by decide +kernel
theorem atom2482Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) := by
  have h := atom2482_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2482Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2483 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 23, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2483 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2483 = ((g 15) * (g 23) * (g 23)) := by
  norm_num [atom2483, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2483_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (367217515929600 : Int) atom2483) := by
  rw [SparsePolynomial.eval_scale, eval_atom2483]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2483Coded : CoefficientMerge.Poly := [(nat_lit 9215, Int.ofNat (nat_lit 1))]
theorem atom2483Coded_decode : atom2483 = SparsePolynomial.decodeCubic 24 atom2483Coded := by decide +kernel
theorem atom2483Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded) := by
  have h := atom2483_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2483Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2484 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom2484 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2484 = ((g 16) * (g 16) * (g 16)) := by
  norm_num [atom2484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2484_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1027680192000 : Int) atom2484) := by
  rw [SparsePolynomial.eval_scale, eval_atom2484]
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 16) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2484Coded : CoefficientMerge.Poly := [(nat_lit 9616, Int.ofNat (nat_lit 1))]
theorem atom2484Coded_decode : atom2484 = SparsePolynomial.decodeCubic 24 atom2484Coded := by decide +kernel
theorem atom2484Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) := by
  have h := atom2484_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2484Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2485 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2485 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2485 = ((g 16) * (g 16) * (g 18)) := by
  norm_num [atom2485, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2485_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7461795801600 : Int) atom2485) := by
  rw [SparsePolynomial.eval_scale, eval_atom2485]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2485Coded : CoefficientMerge.Poly := [(nat_lit 9618, Int.ofNat (nat_lit 1))]
theorem atom2485Coded_decode : atom2485 = SparsePolynomial.decodeCubic 24 atom2485Coded := by decide +kernel
theorem atom2485Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded) := by
  have h := atom2485_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2485Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2486 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2486 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2486 = ((g 16) * (g 16) * (g 20)) := by
  norm_num [atom2486, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2486_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109950182899200 : Int) atom2486) := by
  rw [SparsePolynomial.eval_scale, eval_atom2486]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2486Coded : CoefficientMerge.Poly := [(nat_lit 9620, Int.ofNat (nat_lit 1))]
theorem atom2486Coded_decode : atom2486 = SparsePolynomial.decodeCubic 24 atom2486Coded := by decide +kernel
theorem atom2486Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) := by
  have h := atom2486_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2486Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2487 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2487 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2487 = ((g 16) * (g 16) * (g 21)) := by
  norm_num [atom2487, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2487_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102488387097600 : Int) atom2487) := by
  rw [SparsePolynomial.eval_scale, eval_atom2487]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2487Coded : CoefficientMerge.Poly := [(nat_lit 9621, Int.ofNat (nat_lit 1))]
theorem atom2487Coded_decode : atom2487 = SparsePolynomial.decodeCubic 24 atom2487Coded := by decide +kernel
theorem atom2487Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) := by
  have h := atom2487_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2487Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2488 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2488 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2488 = ((g 16) * (g 16) * (g 23)) := by
  norm_num [atom2488, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2488_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102213909504000 : Int) atom2488) := by
  rw [SparsePolynomial.eval_scale, eval_atom2488]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2488Coded : CoefficientMerge.Poly := [(nat_lit 9623, Int.ofNat (nat_lit 1))]
theorem atom2488Coded_decode : atom2488 = SparsePolynomial.decodeCubic 24 atom2488Coded := by decide +kernel
theorem atom2488Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded) := by
  have h := atom2488_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2488Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2489 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom2489 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2489 = ((g 16) * (g 17) * (g 17)) := by
  norm_num [atom2489, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2489_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2395557964800 : Int) atom2489) := by
  rw [SparsePolynomial.eval_scale, eval_atom2489]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2489Coded : CoefficientMerge.Poly := [(nat_lit 9641, Int.ofNat (nat_lit 1))]
theorem atom2489Coded_decode : atom2489 = SparsePolynomial.decodeCubic 24 atom2489Coded := by decide +kernel
theorem atom2489Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) := by
  have h := atom2489_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2489Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2490 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2490 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2490 = ((g 16) * (g 17) * (g 19)) := by
  norm_num [atom2490, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2490_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9886777420800 : Int) atom2490) := by
  rw [SparsePolynomial.eval_scale, eval_atom2490]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2490Coded : CoefficientMerge.Poly := [(nat_lit 9643, Int.ofNat (nat_lit 1))]
theorem atom2490Coded_decode : atom2490 = SparsePolynomial.decodeCubic 24 atom2490Coded := by decide +kernel
theorem atom2490Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded) := by
  have h := atom2490_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2490Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2491 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2491 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2491 = ((g 16) * (g 17) * (g 20)) := by
  norm_num [atom2491, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2491_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (292154122444800 : Int) atom2491) := by
  rw [SparsePolynomial.eval_scale, eval_atom2491]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2491Coded : CoefficientMerge.Poly := [(nat_lit 9644, Int.ofNat (nat_lit 1))]
theorem atom2491Coded_decode : atom2491 = SparsePolynomial.decodeCubic 24 atom2491Coded := by decide +kernel
theorem atom2491Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) := by
  have h := atom2491_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2491Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2492 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2492 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2492 = ((g 16) * (g 17) * (g 21)) := by
  norm_num [atom2492, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2492_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (317089058764800 : Int) atom2492) := by
  rw [SparsePolynomial.eval_scale, eval_atom2492]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2492Coded : CoefficientMerge.Poly := [(nat_lit 9645, Int.ofNat (nat_lit 1))]
theorem atom2492Coded_decode : atom2492 = SparsePolynomial.decodeCubic 24 atom2492Coded := by decide +kernel
theorem atom2492Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) := by
  have h := atom2492_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2492Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2493 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2493 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2493 = ((g 16) * (g 17) * (g 22)) := by
  norm_num [atom2493, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2493_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188403739776000 : Int) atom2493) := by
  rw [SparsePolynomial.eval_scale, eval_atom2493]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2493Coded : CoefficientMerge.Poly := [(nat_lit 9646, Int.ofNat (nat_lit 1))]
theorem atom2493Coded_decode : atom2493 = SparsePolynomial.decodeCubic 24 atom2493Coded := by decide +kernel
theorem atom2493Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded) := by
  have h := atom2493_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2493Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2494 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2494 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2494 = ((g 16) * (g 17) * (g 23)) := by
  norm_num [atom2494, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2494_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (477770776358400 : Int) atom2494) := by
  rw [SparsePolynomial.eval_scale, eval_atom2494]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2494Coded : CoefficientMerge.Poly := [(nat_lit 9647, Int.ofNat (nat_lit 1))]
theorem atom2494Coded_decode : atom2494 = SparsePolynomial.decodeCubic 24 atom2494Coded := by decide +kernel
theorem atom2494Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) := by
  have h := atom2494_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2494Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2495 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2495 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2495 = ((g 16) * (g 18) * (g 18)) := by
  norm_num [atom2495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2495_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41516346816000 : Int) atom2495) := by
  rw [SparsePolynomial.eval_scale, eval_atom2495]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2495Coded : CoefficientMerge.Poly := [(nat_lit 9666, Int.ofNat (nat_lit 1))]
theorem atom2495Coded_decode : atom2495 = SparsePolynomial.decodeCubic 24 atom2495Coded := by decide +kernel
theorem atom2495Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded) := by
  have h := atom2495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2496 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2496 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2496 = ((g 16) * (g 18) * (g 19)) := by
  norm_num [atom2496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2496_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149668894771200 : Int) atom2496) := by
  rw [SparsePolynomial.eval_scale, eval_atom2496]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2496Coded : CoefficientMerge.Poly := [(nat_lit 9667, Int.ofNat (nat_lit 1))]
theorem atom2496Coded_decode : atom2496 = SparsePolynomial.decodeCubic 24 atom2496Coded := by decide +kernel
theorem atom2496Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) := by
  have h := atom2496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2497 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2497 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2497 = ((g 16) * (g 18) * (g 20)) := by
  norm_num [atom2497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2497_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (497988692812800 : Int) atom2497) := by
  rw [SparsePolynomial.eval_scale, eval_atom2497]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2497Coded : CoefficientMerge.Poly := [(nat_lit 9668, Int.ofNat (nat_lit 1))]
theorem atom2497Coded_decode : atom2497 = SparsePolynomial.decodeCubic 24 atom2497Coded := by decide +kernel
theorem atom2497Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) := by
  have h := atom2497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2498 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2498 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2498 = ((g 16) * (g 18) * (g 21)) := by
  norm_num [atom2498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2498_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (564624893952000 : Int) atom2498) := by
  rw [SparsePolynomial.eval_scale, eval_atom2498]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2498Coded : CoefficientMerge.Poly := [(nat_lit 9669, Int.ofNat (nat_lit 1))]
theorem atom2498Coded_decode : atom2498 = SparsePolynomial.decodeCubic 24 atom2498Coded := by decide +kernel
theorem atom2498Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded) := by
  have h := atom2498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2499 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2499 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2499 = ((g 16) * (g 18) * (g 22)) := by
  norm_num [atom2499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2499_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (426558798489600 : Int) atom2499) := by
  rw [SparsePolynomial.eval_scale, eval_atom2499]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2499Coded : CoefficientMerge.Poly := [(nat_lit 9670, Int.ofNat (nat_lit 1))]
theorem atom2499Coded_decode : atom2499 = SparsePolynomial.decodeCubic 24 atom2499Coded := by decide +kernel
theorem atom2499Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) := by
  have h := atom2499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2500 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2500 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2500 = ((g 16) * (g 18) * (g 23)) := by
  norm_num [atom2500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2500_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (759406049740800 : Int) atom2500) := by
  rw [SparsePolynomial.eval_scale, eval_atom2500]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2500Coded : CoefficientMerge.Poly := [(nat_lit 9671, Int.ofNat (nat_lit 1))]
theorem atom2500Coded_decode : atom2500 = SparsePolynomial.decodeCubic 24 atom2500Coded := by decide +kernel
theorem atom2500Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded) := by
  have h := atom2500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2501 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2501 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2501 = ((g 16) * (g 19) * (g 19)) := by
  norm_num [atom2501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2501_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65538548490240 : Int) atom2501) := by
  rw [SparsePolynomial.eval_scale, eval_atom2501]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2501Coded : CoefficientMerge.Poly := [(nat_lit 9691, Int.ofNat (nat_lit 1))]
theorem atom2501Coded_decode : atom2501 = SparsePolynomial.decodeCubic 24 atom2501Coded := by decide +kernel
theorem atom2501Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) := by
  have h := atom2501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2502 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2502 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2502 = ((g 16) * (g 19) * (g 20)) := by
  norm_num [atom2502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2502_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (477151590988800 : Int) atom2502) := by
  rw [SparsePolynomial.eval_scale, eval_atom2502]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2502Coded : CoefficientMerge.Poly := [(nat_lit 9692, Int.ofNat (nat_lit 1))]
theorem atom2502Coded_decode : atom2502 = SparsePolynomial.decodeCubic 24 atom2502Coded := by decide +kernel
theorem atom2502Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) := by
  have h := atom2502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2503 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2503 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2503 = ((g 16) * (g 19) * (g 21)) := by
  norm_num [atom2503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2503_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (631558767974400 : Int) atom2503) := by
  rw [SparsePolynomial.eval_scale, eval_atom2503]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2503Coded : CoefficientMerge.Poly := [(nat_lit 9693, Int.ofNat (nat_lit 1))]
theorem atom2503Coded_decode : atom2503 = SparsePolynomial.decodeCubic 24 atom2503Coded := by decide +kernel
theorem atom2503Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded) := by
  have h := atom2503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2504 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2504 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2504 = ((g 16) * (g 19) * (g 22)) := by
  norm_num [atom2504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2504_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (581263648358400 : Int) atom2504) := by
  rw [SparsePolynomial.eval_scale, eval_atom2504]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2504Coded : CoefficientMerge.Poly := [(nat_lit 9694, Int.ofNat (nat_lit 1))]
theorem atom2504Coded_decode : atom2504 = SparsePolynomial.decodeCubic 24 atom2504Coded := by decide +kernel
theorem atom2504Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) := by
  have h := atom2504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2505 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2505 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2505 = ((g 16) * (g 19) * (g 23)) := by
  norm_num [atom2505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2505_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (790619177779200 : Int) atom2505) := by
  rw [SparsePolynomial.eval_scale, eval_atom2505]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2505Coded : CoefficientMerge.Poly := [(nat_lit 9695, Int.ofNat (nat_lit 1))]
theorem atom2505Coded_decode : atom2505 = SparsePolynomial.decodeCubic 24 atom2505Coded := by decide +kernel
theorem atom2505Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded) := by
  have h := atom2505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2506 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2506 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2506 = ((g 16) * (g 20) * (g 20)) := by
  norm_num [atom2506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2506_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (368999043033600 : Int) atom2506) := by
  rw [SparsePolynomial.eval_scale, eval_atom2506]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2506Coded : CoefficientMerge.Poly := [(nat_lit 9716, Int.ofNat (nat_lit 1))]
theorem atom2506Coded_decode : atom2506 = SparsePolynomial.decodeCubic 24 atom2506Coded := by decide +kernel
theorem atom2506Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) := by
  have h := atom2506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2507 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2507 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2507 = ((g 16) * (g 20) * (g 21)) := by
  norm_num [atom2507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2507_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (768913541222400 : Int) atom2507) := by
  rw [SparsePolynomial.eval_scale, eval_atom2507]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2507Coded : CoefficientMerge.Poly := [(nat_lit 9717, Int.ofNat (nat_lit 1))]
theorem atom2507Coded_decode : atom2507 = SparsePolynomial.decodeCubic 24 atom2507Coded := by decide +kernel
theorem atom2507Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) := by
  have h := atom2507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2508 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2508 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2508 = ((g 16) * (g 20) * (g 22)) := by
  norm_num [atom2508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2508_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (735847367270400 : Int) atom2508) := by
  rw [SparsePolynomial.eval_scale, eval_atom2508]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2508Coded : CoefficientMerge.Poly := [(nat_lit 9718, Int.ofNat (nat_lit 1))]
theorem atom2508Coded_decode : atom2508 = SparsePolynomial.decodeCubic 24 atom2508Coded := by decide +kernel
theorem atom2508Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded) := by
  have h := atom2508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2509 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2509 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2509 = ((g 16) * (g 20) * (g 23)) := by
  norm_num [atom2509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2509_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (804008014387200 : Int) atom2509) := by
  rw [SparsePolynomial.eval_scale, eval_atom2509]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2509Coded : CoefficientMerge.Poly := [(nat_lit 9719, Int.ofNat (nat_lit 1))]
theorem atom2509Coded_decode : atom2509 = SparsePolynomial.decodeCubic 24 atom2509Coded := by decide +kernel
theorem atom2509Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) := by
  have h := atom2509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2510 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2510 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2510 = ((g 16) * (g 21) * (g 21)) := by
  norm_num [atom2510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2510_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347502808396800 : Int) atom2510) := by
  rw [SparsePolynomial.eval_scale, eval_atom2510]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2510Coded : CoefficientMerge.Poly := [(nat_lit 9741, Int.ofNat (nat_lit 1))]
theorem atom2510Coded_decode : atom2510 = SparsePolynomial.decodeCubic 24 atom2510Coded := by decide +kernel
theorem atom2510Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded) := by
  have h := atom2510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2511 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2511 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2511 = ((g 16) * (g 21) * (g 22)) := by
  norm_num [atom2511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2511_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (749710418688000 : Int) atom2511) := by
  rw [SparsePolynomial.eval_scale, eval_atom2511]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2511Coded : CoefficientMerge.Poly := [(nat_lit 9742, Int.ofNat (nat_lit 1))]
theorem atom2511Coded_decode : atom2511 = SparsePolynomial.decodeCubic 24 atom2511Coded := by decide +kernel
theorem atom2511Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) := by
  have h := atom2511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2512 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2512 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2512 = ((g 16) * (g 21) * (g 23)) := by
  norm_num [atom2512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2512_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (835221142425600 : Int) atom2512) := by
  rw [SparsePolynomial.eval_scale, eval_atom2512]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2512Coded : CoefficientMerge.Poly := [(nat_lit 9743, Int.ofNat (nat_lit 1))]
theorem atom2512Coded_decode : atom2512 = SparsePolynomial.decodeCubic 24 atom2512Coded := by decide +kernel
theorem atom2512Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) := by
  have h := atom2512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2513 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 22, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2513 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2513 = ((g 16) * (g 22) * (g 22)) := by
  norm_num [atom2513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2513_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (375348914640000 : Int) atom2513) := by
  rw [SparsePolynomial.eval_scale, eval_atom2513]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2513Coded : CoefficientMerge.Poly := [(nat_lit 9766, Int.ofNat (nat_lit 1))]
theorem atom2513Coded_decode : atom2513 = SparsePolynomial.decodeCubic 24 atom2513Coded := by decide +kernel
theorem atom2513Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded) := by
  have h := atom2513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2514 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2514 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2514 = ((g 16) * (g 22) * (g 23)) := by
  norm_num [atom2514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2514_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (866434270464000 : Int) atom2514) := by
  rw [SparsePolynomial.eval_scale, eval_atom2514]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2514Coded : CoefficientMerge.Poly := [(nat_lit 9767, Int.ofNat (nat_lit 1))]
theorem atom2514Coded_decode : atom2514 = SparsePolynomial.decodeCubic 24 atom2514Coded := by decide +kernel
theorem atom2514Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) := by
  have h := atom2514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2515 : SparsePolynomial.Poly := [([nat_lit 16, nat_lit 23, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2515 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2515 = ((g 16) * (g 23) * (g 23)) := by
  norm_num [atom2515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2515_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (439911553536000 : Int) atom2515) := by
  rw [SparsePolynomial.eval_scale, eval_atom2515]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2515Coded : CoefficientMerge.Poly := [(nat_lit 9791, Int.ofNat (nat_lit 1))]
theorem atom2515Coded_decode : atom2515 = SparsePolynomial.decodeCubic 24 atom2515Coded := by decide +kernel
theorem atom2515Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded) := by
  have h := atom2515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2516 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2516 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2516 = ((g 17) * (g 17) * (g 19)) := by
  norm_num [atom2516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2516_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14841119462400 : Int) atom2516) := by
  rw [SparsePolynomial.eval_scale, eval_atom2516]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2516Coded : CoefficientMerge.Poly := [(nat_lit 10219, Int.ofNat (nat_lit 1))]
theorem atom2516Coded_decode : atom2516 = SparsePolynomial.decodeCubic 24 atom2516Coded := by decide +kernel
theorem atom2516Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) := by
  have h := atom2516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2517 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2517 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2517 = ((g 17) * (g 17) * (g 20)) := by
  norm_num [atom2517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2517_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155130096844800 : Int) atom2517) := by
  rw [SparsePolynomial.eval_scale, eval_atom2517]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2517Coded : CoefficientMerge.Poly := [(nat_lit 10220, Int.ofNat (nat_lit 1))]
theorem atom2517Coded_decode : atom2517 = SparsePolynomial.decodeCubic 24 atom2517Coded := by decide +kernel
theorem atom2517Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) := by
  have h := atom2517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2518 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2518 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2518 = ((g 17) * (g 17) * (g 21)) := by
  norm_num [atom2518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2518_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (169971216307200 : Int) atom2518) := by
  rw [SparsePolynomial.eval_scale, eval_atom2518]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2518Coded : CoefficientMerge.Poly := [(nat_lit 10221, Int.ofNat (nat_lit 1))]
theorem atom2518Coded_decode : atom2518 = SparsePolynomial.decodeCubic 24 atom2518Coded := by decide +kernel
theorem atom2518Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded) := by
  have h := atom2518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2519 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2519 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2519 = ((g 17) * (g 17) * (g 22)) := by
  norm_num [atom2519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2519_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96697940774400 : Int) atom2519) := by
  rw [SparsePolynomial.eval_scale, eval_atom2519]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2519Coded : CoefficientMerge.Poly := [(nat_lit 10222, Int.ofNat (nat_lit 1))]
theorem atom2519Coded_decode : atom2519 = SparsePolynomial.decodeCubic 24 atom2519Coded := by decide +kernel
theorem atom2519Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) := by
  have h := atom2519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2520 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2520 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2520 = ((g 17) * (g 17) * (g 23)) := by
  norm_num [atom2520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2520_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229250644761600 : Int) atom2520) := by
  rw [SparsePolynomial.eval_scale, eval_atom2520]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2520Coded : CoefficientMerge.Poly := [(nat_lit 10223, Int.ofNat (nat_lit 1))]
theorem atom2520Coded_decode : atom2520 = SparsePolynomial.decodeCubic 24 atom2520Coded := by decide +kernel
theorem atom2520Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded) := by
  have h := atom2520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2521 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom2521 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2521 = ((g 17) * (g 18) * (g 18)) := by
  norm_num [atom2521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2521_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21474972288000 : Int) atom2521) := by
  rw [SparsePolynomial.eval_scale, eval_atom2521]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 17) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2521Coded : CoefficientMerge.Poly := [(nat_lit 10242, Int.ofNat (nat_lit 1))]
theorem atom2521Coded_decode : atom2521 = SparsePolynomial.decodeCubic 24 atom2521Coded := by decide +kernel
theorem atom2521Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) := by
  have h := atom2521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2522 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2522 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2522 = ((g 17) * (g 18) * (g 19)) := by
  norm_num [atom2522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2522_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121790733926400 : Int) atom2522) := by
  rw [SparsePolynomial.eval_scale, eval_atom2522]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2522Coded : CoefficientMerge.Poly := [(nat_lit 10243, Int.ofNat (nat_lit 1))]
theorem atom2522Coded_decode : atom2522 = SparsePolynomial.decodeCubic 24 atom2522Coded := by decide +kernel
theorem atom2522Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) := by
  have h := atom2522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2523 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2523 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2523 = ((g 17) * (g 18) * (g 20)) := by
  norm_num [atom2523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2523_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (482315120179200 : Int) atom2523) := by
  rw [SparsePolynomial.eval_scale, eval_atom2523]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2523Coded : CoefficientMerge.Poly := [(nat_lit 10244, Int.ofNat (nat_lit 1))]
theorem atom2523Coded_decode : atom2523 = SparsePolynomial.decodeCubic 24 atom2523Coded := by decide +kernel
theorem atom2523Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded) := by
  have h := atom2523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2524 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom2524 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2524 = ((g 17) * (g 18) * (g 21)) := by
  norm_num [atom2524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2524_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (561155909529600 : Int) atom2524) := by
  rw [SparsePolynomial.eval_scale, eval_atom2524]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2524Coded : CoefficientMerge.Poly := [(nat_lit 10245, Int.ofNat (nat_lit 1))]
theorem atom2524Coded_decode : atom2524 = SparsePolynomial.decodeCubic 24 atom2524Coded := by decide +kernel
theorem atom2524Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) := by
  have h := atom2524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2525 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom2525 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2525 = ((g 17) * (g 18) * (g 22)) := by
  norm_num [atom2525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2525_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (434170719360000 : Int) atom2525) := by
  rw [SparsePolynomial.eval_scale, eval_atom2525]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2525Coded : CoefficientMerge.Poly := [(nat_lit 10246, Int.ofNat (nat_lit 1))]
theorem atom2525Coded_decode : atom2525 = SparsePolynomial.decodeCubic 24 atom2525Coded := by decide +kernel
theorem atom2525Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded) := by
  have h := atom2525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2526 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom2526 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2526 = ((g 17) * (g 18) * (g 23)) := by
  norm_num [atom2526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2526_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (779222558822400 : Int) atom2526) := by
  rw [SparsePolynomial.eval_scale, eval_atom2526]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2526Coded : CoefficientMerge.Poly := [(nat_lit 10247, Int.ofNat (nat_lit 1))]
theorem atom2526Coded_decode : atom2526 = SparsePolynomial.decodeCubic 24 atom2526Coded := by decide +kernel
theorem atom2526Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) := by
  have h := atom2526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2527 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom2527 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2527 = ((g 17) * (g 19) * (g 19)) := by
  norm_num [atom2527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2527_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54618721597440 : Int) atom2527) := by
  rw [SparsePolynomial.eval_scale, eval_atom2527]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2527Coded : CoefficientMerge.Poly := [(nat_lit 10267, Int.ofNat (nat_lit 1))]
theorem atom2527Coded_decode : atom2527 = SparsePolynomial.decodeCubic 24 atom2527Coded := by decide +kernel
theorem atom2527Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) := by
  have h := atom2527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2528 : SparsePolynomial.Poly := [([nat_lit 17, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom2528 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2528 = ((g 17) * (g 19) * (g 20)) := by
  norm_num [atom2528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2528_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (468537118156800 : Int) atom2528) := by
  rw [SparsePolynomial.eval_scale, eval_atom2528]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2528Coded : CoefficientMerge.Poly := [(nat_lit 10268, Int.ofNat (nat_lit 1))]
theorem atom2528Coded_decode : atom2528 = SparsePolynomial.decodeCubic 24 atom2528Coded := by decide +kernel
theorem atom2528Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded) := by
  have h := atom2528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block033 : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 65163300249600)), (nat_lit 9023, Int.ofNat (nat_lit 5211208396800)), (nat_lit 9042, Int.ofNat (nat_lit 24896019778560)), (nat_lit 9044, Int.ofNat (nat_lit 233856198374400)), (nat_lit 9045, Int.ofNat (nat_lit 220828821696000)), (nat_lit 9046, Int.ofNat (nat_lit 99469520156160)), (nat_lit 9047, Int.ofNat (nat_lit 259121345414400)), (nat_lit 9065, Int.ofNat (nat_lit 8561639116800)), (nat_lit 9066, Int.ofNat (nat_lit 35057102976000)), (nat_lit 9067, Int.ofNat (nat_lit 40411348992000)), (nat_lit 9068, Int.ofNat (nat_lit 327449191910400)), (nat_lit 9069, Int.ofNat (nat_lit 349177379443200)), (nat_lit 9070, Int.ofNat (nat_lit 284381337945600)), (nat_lit 9071, Int.ofNat (nat_lit 503972755372800)), (nat_lit 9090, Int.ofNat (nat_lit 71490459801600)), (nat_lit 9091, Int.ofNat (nat_lit 197412532531200)), (nat_lit 9092, Int.ofNat (nat_lit 533527742361600)), (nat_lit 9093, Int.ofNat (nat_lit 587959355289600)), (nat_lit 9094, Int.ofNat (nat_lit 457214273107200)), (nat_lit 9095, Int.ofNat (nat_lit 739589540659200)), (nat_lit 9115, Int.ofNat (nat_lit 86391113840640)), (nat_lit 9116, Int.ofNat (nat_lit 505631540736000)), (nat_lit 9117, Int.ofNat (nat_lit 646813536768000)), (nat_lit 9118, Int.ofNat (nat_lit 564551442201600)), (nat_lit 9119, Int.ofNat (nat_lit 760681790668800)), (nat_lit 9140, Int.ofNat (nat_lit 379709468006400)), (nat_lit 9141, Int.ofNat (nat_lit 776088617472000)), (nat_lit 9142, Int.ofNat (nat_lit 671767480339200)), (nat_lit 9143, Int.ofNat (nat_lit 726466161254400)), (nat_lit 9165, Int.ofNat (nat_lit 347050500249600)), (nat_lit 9166, Int.ofNat (nat_lit 657396548726400)), (nat_lit 9167, Int.ofNat (nat_lit 747558411264000)), (nat_lit 9190, Int.ofNat (nat_lit 276807592656000)), (nat_lit 9191, Int.ofNat (nat_lit 682549021425600)), (nat_lit 9215, Int.ofNat (nat_lit 367217515929600)), (nat_lit 9616, Int.ofNat (nat_lit 1027680192000)), (nat_lit 9618, Int.ofNat (nat_lit 7461795801600)), (nat_lit 9620, Int.ofNat (nat_lit 109950182899200)), (nat_lit 9621, Int.ofNat (nat_lit 102488387097600)), (nat_lit 9623, Int.ofNat (nat_lit 102213909504000)), (nat_lit 9641, Int.ofNat (nat_lit 2395557964800)), (nat_lit 9643, Int.ofNat (nat_lit 9886777420800)), (nat_lit 9644, Int.ofNat (nat_lit 292154122444800)), (nat_lit 9645, Int.ofNat (nat_lit 317089058764800)), (nat_lit 9646, Int.ofNat (nat_lit 188403739776000)), (nat_lit 9647, Int.ofNat (nat_lit 477770776358400)), (nat_lit 9666, Int.ofNat (nat_lit 41516346816000)), (nat_lit 9667, Int.ofNat (nat_lit 149668894771200)), (nat_lit 9668, Int.ofNat (nat_lit 497988692812800)), (nat_lit 9669, Int.ofNat (nat_lit 564624893952000)), (nat_lit 9670, Int.ofNat (nat_lit 426558798489600)), (nat_lit 9671, Int.ofNat (nat_lit 759406049740800)), (nat_lit 9691, Int.ofNat (nat_lit 65538548490240)), (nat_lit 9692, Int.ofNat (nat_lit 477151590988800)), (nat_lit 9693, Int.ofNat (nat_lit 631558767974400)), (nat_lit 9694, Int.ofNat (nat_lit 581263648358400)), (nat_lit 9695, Int.ofNat (nat_lit 790619177779200)), (nat_lit 9716, Int.ofNat (nat_lit 368999043033600)), (nat_lit 9717, Int.ofNat (nat_lit 768913541222400)), (nat_lit 9718, Int.ofNat (nat_lit 735847367270400)), (nat_lit 9719, Int.ofNat (nat_lit 804008014387200)), (nat_lit 9741, Int.ofNat (nat_lit 347502808396800)), (nat_lit 9742, Int.ofNat (nat_lit 749710418688000)), (nat_lit 9743, Int.ofNat (nat_lit 835221142425600)), (nat_lit 9766, Int.ofNat (nat_lit 375348914640000)), (nat_lit 9767, Int.ofNat (nat_lit 866434270464000)), (nat_lit 9791, Int.ofNat (nat_lit 439911553536000)), (nat_lit 10219, Int.ofNat (nat_lit 14841119462400)), (nat_lit 10220, Int.ofNat (nat_lit 155130096844800)), (nat_lit 10221, Int.ofNat (nat_lit 169971216307200)), (nat_lit 10222, Int.ofNat (nat_lit 96697940774400)), (nat_lit 10223, Int.ofNat (nat_lit 229250644761600)), (nat_lit 10242, Int.ofNat (nat_lit 21474972288000)), (nat_lit 10243, Int.ofNat (nat_lit 121790733926400)), (nat_lit 10244, Int.ofNat (nat_lit 482315120179200)), (nat_lit 10245, Int.ofNat (nat_lit 561155909529600)), (nat_lit 10246, Int.ofNat (nat_lit 434170719360000)), (nat_lit 10247, Int.ofNat (nat_lit 779222558822400)), (nat_lit 10267, Int.ofNat (nat_lit 54618721597440)), (nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
def block033_data_flat000 : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 65163300249600))]
theorem block033_data_flat000_step : block033_data_flat000 = (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) := by decide +kernel
theorem block033_data_flat000_original : block033_data_flat000 = (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) := by
  rw [block033_data_flat000_step]
def block033_data_flat001 : CoefficientMerge.Poly := [(nat_lit 9023, Int.ofNat (nat_lit 5211208396800))]
theorem block033_data_flat001_step : block033_data_flat001 = (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded) := by decide +kernel
theorem block033_data_flat001_original : block033_data_flat001 = (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded) := by
  rw [block033_data_flat001_step]
def block033_data_flat002 : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 65163300249600)), (nat_lit 9023, Int.ofNat (nat_lit 5211208396800))]
theorem block033_data_flat002_step : block033_data_flat002 = (CoefficientMerge.fastMerge block033_data_flat000 block033_data_flat001) := by decide +kernel
theorem block033_data_flat002_original : block033_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded)) := by
  rw [block033_data_flat002_step, block033_data_flat000_original, block033_data_flat001_original]
def block033_data_flat003 : CoefficientMerge.Poly := [(nat_lit 9042, Int.ofNat (nat_lit 24896019778560))]
theorem block033_data_flat003_step : block033_data_flat003 = (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) := by decide +kernel
theorem block033_data_flat003_original : block033_data_flat003 = (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) := by
  rw [block033_data_flat003_step]
def block033_data_flat004 : CoefficientMerge.Poly := [(nat_lit 9044, Int.ofNat (nat_lit 233856198374400))]
theorem block033_data_flat004_step : block033_data_flat004 = (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) := by decide +kernel
theorem block033_data_flat004_original : block033_data_flat004 = (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) := by
  rw [block033_data_flat004_step]
def block033_data_flat005 : CoefficientMerge.Poly := [(nat_lit 9045, Int.ofNat (nat_lit 220828821696000))]
theorem block033_data_flat005_step : block033_data_flat005 = (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded) := by decide +kernel
theorem block033_data_flat005_original : block033_data_flat005 = (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded) := by
  rw [block033_data_flat005_step]
def block033_data_flat006 : CoefficientMerge.Poly := [(nat_lit 9044, Int.ofNat (nat_lit 233856198374400)), (nat_lit 9045, Int.ofNat (nat_lit 220828821696000))]
theorem block033_data_flat006_step : block033_data_flat006 = (CoefficientMerge.fastMerge block033_data_flat004 block033_data_flat005) := by decide +kernel
theorem block033_data_flat006_original : block033_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded)) := by
  rw [block033_data_flat006_step, block033_data_flat004_original, block033_data_flat005_original]
def block033_data_flat007 : CoefficientMerge.Poly := [(nat_lit 9042, Int.ofNat (nat_lit 24896019778560)), (nat_lit 9044, Int.ofNat (nat_lit 233856198374400)), (nat_lit 9045, Int.ofNat (nat_lit 220828821696000))]
theorem block033_data_flat007_step : block033_data_flat007 = (CoefficientMerge.fastMerge block033_data_flat003 block033_data_flat006) := by decide +kernel
theorem block033_data_flat007_original : block033_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded))) := by
  rw [block033_data_flat007_step, block033_data_flat003_original, block033_data_flat006_original]
def block033_data_flat008 : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 65163300249600)), (nat_lit 9023, Int.ofNat (nat_lit 5211208396800)), (nat_lit 9042, Int.ofNat (nat_lit 24896019778560)), (nat_lit 9044, Int.ofNat (nat_lit 233856198374400)), (nat_lit 9045, Int.ofNat (nat_lit 220828821696000))]
theorem block033_data_flat008_step : block033_data_flat008 = (CoefficientMerge.fastMerge block033_data_flat002 block033_data_flat007) := by decide +kernel
theorem block033_data_flat008_original : block033_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded)))) := by
  rw [block033_data_flat008_step, block033_data_flat002_original, block033_data_flat007_original]
def block033_data_flat009 : CoefficientMerge.Poly := [(nat_lit 9046, Int.ofNat (nat_lit 99469520156160))]
theorem block033_data_flat009_step : block033_data_flat009 = (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) := by decide +kernel
theorem block033_data_flat009_original : block033_data_flat009 = (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) := by
  rw [block033_data_flat009_step]
def block033_data_flat010 : CoefficientMerge.Poly := [(nat_lit 9047, Int.ofNat (nat_lit 259121345414400))]
theorem block033_data_flat010_step : block033_data_flat010 = (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded) := by decide +kernel
theorem block033_data_flat010_original : block033_data_flat010 = (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded) := by
  rw [block033_data_flat010_step]
def block033_data_flat011 : CoefficientMerge.Poly := [(nat_lit 9046, Int.ofNat (nat_lit 99469520156160)), (nat_lit 9047, Int.ofNat (nat_lit 259121345414400))]
theorem block033_data_flat011_step : block033_data_flat011 = (CoefficientMerge.fastMerge block033_data_flat009 block033_data_flat010) := by decide +kernel
theorem block033_data_flat011_original : block033_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded)) := by
  rw [block033_data_flat011_step, block033_data_flat009_original, block033_data_flat010_original]
def block033_data_flat012 : CoefficientMerge.Poly := [(nat_lit 9065, Int.ofNat (nat_lit 8561639116800))]
theorem block033_data_flat012_step : block033_data_flat012 = (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) := by decide +kernel
theorem block033_data_flat012_original : block033_data_flat012 = (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) := by
  rw [block033_data_flat012_step]
def block033_data_flat013 : CoefficientMerge.Poly := [(nat_lit 9066, Int.ofNat (nat_lit 35057102976000))]
theorem block033_data_flat013_step : block033_data_flat013 = (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) := by decide +kernel
theorem block033_data_flat013_original : block033_data_flat013 = (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) := by
  rw [block033_data_flat013_step]
def block033_data_flat014 : CoefficientMerge.Poly := [(nat_lit 9067, Int.ofNat (nat_lit 40411348992000))]
theorem block033_data_flat014_step : block033_data_flat014 = (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded) := by decide +kernel
theorem block033_data_flat014_original : block033_data_flat014 = (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded) := by
  rw [block033_data_flat014_step]
def block033_data_flat015 : CoefficientMerge.Poly := [(nat_lit 9066, Int.ofNat (nat_lit 35057102976000)), (nat_lit 9067, Int.ofNat (nat_lit 40411348992000))]
theorem block033_data_flat015_step : block033_data_flat015 = (CoefficientMerge.fastMerge block033_data_flat013 block033_data_flat014) := by decide +kernel
theorem block033_data_flat015_original : block033_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded)) := by
  rw [block033_data_flat015_step, block033_data_flat013_original, block033_data_flat014_original]
def block033_data_flat016 : CoefficientMerge.Poly := [(nat_lit 9065, Int.ofNat (nat_lit 8561639116800)), (nat_lit 9066, Int.ofNat (nat_lit 35057102976000)), (nat_lit 9067, Int.ofNat (nat_lit 40411348992000))]
theorem block033_data_flat016_step : block033_data_flat016 = (CoefficientMerge.fastMerge block033_data_flat012 block033_data_flat015) := by decide +kernel
theorem block033_data_flat016_original : block033_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded))) := by
  rw [block033_data_flat016_step, block033_data_flat012_original, block033_data_flat015_original]
def block033_data_flat017 : CoefficientMerge.Poly := [(nat_lit 9046, Int.ofNat (nat_lit 99469520156160)), (nat_lit 9047, Int.ofNat (nat_lit 259121345414400)), (nat_lit 9065, Int.ofNat (nat_lit 8561639116800)), (nat_lit 9066, Int.ofNat (nat_lit 35057102976000)), (nat_lit 9067, Int.ofNat (nat_lit 40411348992000))]
theorem block033_data_flat017_step : block033_data_flat017 = (CoefficientMerge.fastMerge block033_data_flat011 block033_data_flat016) := by decide +kernel
theorem block033_data_flat017_original : block033_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded)))) := by
  rw [block033_data_flat017_step, block033_data_flat011_original, block033_data_flat016_original]
def block033_data_flat018 : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 65163300249600)), (nat_lit 9023, Int.ofNat (nat_lit 5211208396800)), (nat_lit 9042, Int.ofNat (nat_lit 24896019778560)), (nat_lit 9044, Int.ofNat (nat_lit 233856198374400)), (nat_lit 9045, Int.ofNat (nat_lit 220828821696000)), (nat_lit 9046, Int.ofNat (nat_lit 99469520156160)), (nat_lit 9047, Int.ofNat (nat_lit 259121345414400)), (nat_lit 9065, Int.ofNat (nat_lit 8561639116800)), (nat_lit 9066, Int.ofNat (nat_lit 35057102976000)), (nat_lit 9067, Int.ofNat (nat_lit 40411348992000))]
theorem block033_data_flat018_step : block033_data_flat018 = (CoefficientMerge.fastMerge block033_data_flat008 block033_data_flat017) := by decide +kernel
theorem block033_data_flat018_original : block033_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded))))) := by
  rw [block033_data_flat018_step, block033_data_flat008_original, block033_data_flat017_original]
def block033_data_flat019 : CoefficientMerge.Poly := [(nat_lit 9068, Int.ofNat (nat_lit 327449191910400))]
theorem block033_data_flat019_step : block033_data_flat019 = (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) := by decide +kernel
theorem block033_data_flat019_original : block033_data_flat019 = (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) := by
  rw [block033_data_flat019_step]
def block033_data_flat020 : CoefficientMerge.Poly := [(nat_lit 9069, Int.ofNat (nat_lit 349177379443200))]
theorem block033_data_flat020_step : block033_data_flat020 = (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded) := by decide +kernel
theorem block033_data_flat020_original : block033_data_flat020 = (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded) := by
  rw [block033_data_flat020_step]
def block033_data_flat021 : CoefficientMerge.Poly := [(nat_lit 9068, Int.ofNat (nat_lit 327449191910400)), (nat_lit 9069, Int.ofNat (nat_lit 349177379443200))]
theorem block033_data_flat021_step : block033_data_flat021 = (CoefficientMerge.fastMerge block033_data_flat019 block033_data_flat020) := by decide +kernel
theorem block033_data_flat021_original : block033_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded)) := by
  rw [block033_data_flat021_step, block033_data_flat019_original, block033_data_flat020_original]
def block033_data_flat022 : CoefficientMerge.Poly := [(nat_lit 9070, Int.ofNat (nat_lit 284381337945600))]
theorem block033_data_flat022_step : block033_data_flat022 = (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) := by decide +kernel
theorem block033_data_flat022_original : block033_data_flat022 = (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) := by
  rw [block033_data_flat022_step]
def block033_data_flat023 : CoefficientMerge.Poly := [(nat_lit 9071, Int.ofNat (nat_lit 503972755372800))]
theorem block033_data_flat023_step : block033_data_flat023 = (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) := by decide +kernel
theorem block033_data_flat023_original : block033_data_flat023 = (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) := by
  rw [block033_data_flat023_step]
def block033_data_flat024 : CoefficientMerge.Poly := [(nat_lit 9090, Int.ofNat (nat_lit 71490459801600))]
theorem block033_data_flat024_step : block033_data_flat024 = (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded) := by decide +kernel
theorem block033_data_flat024_original : block033_data_flat024 = (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded) := by
  rw [block033_data_flat024_step]
def block033_data_flat025 : CoefficientMerge.Poly := [(nat_lit 9071, Int.ofNat (nat_lit 503972755372800)), (nat_lit 9090, Int.ofNat (nat_lit 71490459801600))]
theorem block033_data_flat025_step : block033_data_flat025 = (CoefficientMerge.fastMerge block033_data_flat023 block033_data_flat024) := by decide +kernel
theorem block033_data_flat025_original : block033_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded)) := by
  rw [block033_data_flat025_step, block033_data_flat023_original, block033_data_flat024_original]
def block033_data_flat026 : CoefficientMerge.Poly := [(nat_lit 9070, Int.ofNat (nat_lit 284381337945600)), (nat_lit 9071, Int.ofNat (nat_lit 503972755372800)), (nat_lit 9090, Int.ofNat (nat_lit 71490459801600))]
theorem block033_data_flat026_step : block033_data_flat026 = (CoefficientMerge.fastMerge block033_data_flat022 block033_data_flat025) := by decide +kernel
theorem block033_data_flat026_original : block033_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded))) := by
  rw [block033_data_flat026_step, block033_data_flat022_original, block033_data_flat025_original]
def block033_data_flat027 : CoefficientMerge.Poly := [(nat_lit 9068, Int.ofNat (nat_lit 327449191910400)), (nat_lit 9069, Int.ofNat (nat_lit 349177379443200)), (nat_lit 9070, Int.ofNat (nat_lit 284381337945600)), (nat_lit 9071, Int.ofNat (nat_lit 503972755372800)), (nat_lit 9090, Int.ofNat (nat_lit 71490459801600))]
theorem block033_data_flat027_step : block033_data_flat027 = (CoefficientMerge.fastMerge block033_data_flat021 block033_data_flat026) := by decide +kernel
theorem block033_data_flat027_original : block033_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded)))) := by
  rw [block033_data_flat027_step, block033_data_flat021_original, block033_data_flat026_original]
def block033_data_flat028 : CoefficientMerge.Poly := [(nat_lit 9091, Int.ofNat (nat_lit 197412532531200))]
theorem block033_data_flat028_step : block033_data_flat028 = (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) := by decide +kernel
theorem block033_data_flat028_original : block033_data_flat028 = (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) := by
  rw [block033_data_flat028_step]
def block033_data_flat029 : CoefficientMerge.Poly := [(nat_lit 9092, Int.ofNat (nat_lit 533527742361600))]
theorem block033_data_flat029_step : block033_data_flat029 = (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded) := by decide +kernel
theorem block033_data_flat029_original : block033_data_flat029 = (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded) := by
  rw [block033_data_flat029_step]
def block033_data_flat030 : CoefficientMerge.Poly := [(nat_lit 9091, Int.ofNat (nat_lit 197412532531200)), (nat_lit 9092, Int.ofNat (nat_lit 533527742361600))]
theorem block033_data_flat030_step : block033_data_flat030 = (CoefficientMerge.fastMerge block033_data_flat028 block033_data_flat029) := by decide +kernel
theorem block033_data_flat030_original : block033_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded)) := by
  rw [block033_data_flat030_step, block033_data_flat028_original, block033_data_flat029_original]
def block033_data_flat031 : CoefficientMerge.Poly := [(nat_lit 9093, Int.ofNat (nat_lit 587959355289600))]
theorem block033_data_flat031_step : block033_data_flat031 = (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) := by decide +kernel
theorem block033_data_flat031_original : block033_data_flat031 = (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) := by
  rw [block033_data_flat031_step]
def block033_data_flat032 : CoefficientMerge.Poly := [(nat_lit 9094, Int.ofNat (nat_lit 457214273107200))]
theorem block033_data_flat032_step : block033_data_flat032 = (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) := by decide +kernel
theorem block033_data_flat032_original : block033_data_flat032 = (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) := by
  rw [block033_data_flat032_step]
def block033_data_flat033 : CoefficientMerge.Poly := [(nat_lit 9095, Int.ofNat (nat_lit 739589540659200))]
theorem block033_data_flat033_step : block033_data_flat033 = (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded) := by decide +kernel
theorem block033_data_flat033_original : block033_data_flat033 = (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded) := by
  rw [block033_data_flat033_step]
def block033_data_flat034 : CoefficientMerge.Poly := [(nat_lit 9094, Int.ofNat (nat_lit 457214273107200)), (nat_lit 9095, Int.ofNat (nat_lit 739589540659200))]
theorem block033_data_flat034_step : block033_data_flat034 = (CoefficientMerge.fastMerge block033_data_flat032 block033_data_flat033) := by decide +kernel
theorem block033_data_flat034_original : block033_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded)) := by
  rw [block033_data_flat034_step, block033_data_flat032_original, block033_data_flat033_original]
def block033_data_flat035 : CoefficientMerge.Poly := [(nat_lit 9093, Int.ofNat (nat_lit 587959355289600)), (nat_lit 9094, Int.ofNat (nat_lit 457214273107200)), (nat_lit 9095, Int.ofNat (nat_lit 739589540659200))]
theorem block033_data_flat035_step : block033_data_flat035 = (CoefficientMerge.fastMerge block033_data_flat031 block033_data_flat034) := by decide +kernel
theorem block033_data_flat035_original : block033_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded))) := by
  rw [block033_data_flat035_step, block033_data_flat031_original, block033_data_flat034_original]
def block033_data_flat036 : CoefficientMerge.Poly := [(nat_lit 9091, Int.ofNat (nat_lit 197412532531200)), (nat_lit 9092, Int.ofNat (nat_lit 533527742361600)), (nat_lit 9093, Int.ofNat (nat_lit 587959355289600)), (nat_lit 9094, Int.ofNat (nat_lit 457214273107200)), (nat_lit 9095, Int.ofNat (nat_lit 739589540659200))]
theorem block033_data_flat036_step : block033_data_flat036 = (CoefficientMerge.fastMerge block033_data_flat030 block033_data_flat035) := by decide +kernel
theorem block033_data_flat036_original : block033_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded)))) := by
  rw [block033_data_flat036_step, block033_data_flat030_original, block033_data_flat035_original]
def block033_data_flat037 : CoefficientMerge.Poly := [(nat_lit 9068, Int.ofNat (nat_lit 327449191910400)), (nat_lit 9069, Int.ofNat (nat_lit 349177379443200)), (nat_lit 9070, Int.ofNat (nat_lit 284381337945600)), (nat_lit 9071, Int.ofNat (nat_lit 503972755372800)), (nat_lit 9090, Int.ofNat (nat_lit 71490459801600)), (nat_lit 9091, Int.ofNat (nat_lit 197412532531200)), (nat_lit 9092, Int.ofNat (nat_lit 533527742361600)), (nat_lit 9093, Int.ofNat (nat_lit 587959355289600)), (nat_lit 9094, Int.ofNat (nat_lit 457214273107200)), (nat_lit 9095, Int.ofNat (nat_lit 739589540659200))]
theorem block033_data_flat037_step : block033_data_flat037 = (CoefficientMerge.fastMerge block033_data_flat027 block033_data_flat036) := by decide +kernel
theorem block033_data_flat037_original : block033_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded))))) := by
  rw [block033_data_flat037_step, block033_data_flat027_original, block033_data_flat036_original]
def block033_data_flat038 : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 65163300249600)), (nat_lit 9023, Int.ofNat (nat_lit 5211208396800)), (nat_lit 9042, Int.ofNat (nat_lit 24896019778560)), (nat_lit 9044, Int.ofNat (nat_lit 233856198374400)), (nat_lit 9045, Int.ofNat (nat_lit 220828821696000)), (nat_lit 9046, Int.ofNat (nat_lit 99469520156160)), (nat_lit 9047, Int.ofNat (nat_lit 259121345414400)), (nat_lit 9065, Int.ofNat (nat_lit 8561639116800)), (nat_lit 9066, Int.ofNat (nat_lit 35057102976000)), (nat_lit 9067, Int.ofNat (nat_lit 40411348992000)), (nat_lit 9068, Int.ofNat (nat_lit 327449191910400)), (nat_lit 9069, Int.ofNat (nat_lit 349177379443200)), (nat_lit 9070, Int.ofNat (nat_lit 284381337945600)), (nat_lit 9071, Int.ofNat (nat_lit 503972755372800)), (nat_lit 9090, Int.ofNat (nat_lit 71490459801600)), (nat_lit 9091, Int.ofNat (nat_lit 197412532531200)), (nat_lit 9092, Int.ofNat (nat_lit 533527742361600)), (nat_lit 9093, Int.ofNat (nat_lit 587959355289600)), (nat_lit 9094, Int.ofNat (nat_lit 457214273107200)), (nat_lit 9095, Int.ofNat (nat_lit 739589540659200))]
theorem block033_data_flat038_step : block033_data_flat038 = (CoefficientMerge.fastMerge block033_data_flat018 block033_data_flat037) := by decide +kernel
theorem block033_data_flat038_original : block033_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded)))))) := by
  rw [block033_data_flat038_step, block033_data_flat018_original, block033_data_flat037_original]
def block033_data_flat039 : CoefficientMerge.Poly := [(nat_lit 9115, Int.ofNat (nat_lit 86391113840640))]
theorem block033_data_flat039_step : block033_data_flat039 = (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) := by decide +kernel
theorem block033_data_flat039_original : block033_data_flat039 = (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) := by
  rw [block033_data_flat039_step]
def block033_data_flat040 : CoefficientMerge.Poly := [(nat_lit 9116, Int.ofNat (nat_lit 505631540736000))]
theorem block033_data_flat040_step : block033_data_flat040 = (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded) := by decide +kernel
theorem block033_data_flat040_original : block033_data_flat040 = (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded) := by
  rw [block033_data_flat040_step]
def block033_data_flat041 : CoefficientMerge.Poly := [(nat_lit 9115, Int.ofNat (nat_lit 86391113840640)), (nat_lit 9116, Int.ofNat (nat_lit 505631540736000))]
theorem block033_data_flat041_step : block033_data_flat041 = (CoefficientMerge.fastMerge block033_data_flat039 block033_data_flat040) := by decide +kernel
theorem block033_data_flat041_original : block033_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded)) := by
  rw [block033_data_flat041_step, block033_data_flat039_original, block033_data_flat040_original]
def block033_data_flat042 : CoefficientMerge.Poly := [(nat_lit 9117, Int.ofNat (nat_lit 646813536768000))]
theorem block033_data_flat042_step : block033_data_flat042 = (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) := by decide +kernel
theorem block033_data_flat042_original : block033_data_flat042 = (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) := by
  rw [block033_data_flat042_step]
def block033_data_flat043 : CoefficientMerge.Poly := [(nat_lit 9118, Int.ofNat (nat_lit 564551442201600))]
theorem block033_data_flat043_step : block033_data_flat043 = (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) := by decide +kernel
theorem block033_data_flat043_original : block033_data_flat043 = (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) := by
  rw [block033_data_flat043_step]
def block033_data_flat044 : CoefficientMerge.Poly := [(nat_lit 9119, Int.ofNat (nat_lit 760681790668800))]
theorem block033_data_flat044_step : block033_data_flat044 = (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded) := by decide +kernel
theorem block033_data_flat044_original : block033_data_flat044 = (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded) := by
  rw [block033_data_flat044_step]
def block033_data_flat045 : CoefficientMerge.Poly := [(nat_lit 9118, Int.ofNat (nat_lit 564551442201600)), (nat_lit 9119, Int.ofNat (nat_lit 760681790668800))]
theorem block033_data_flat045_step : block033_data_flat045 = (CoefficientMerge.fastMerge block033_data_flat043 block033_data_flat044) := by decide +kernel
theorem block033_data_flat045_original : block033_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded)) := by
  rw [block033_data_flat045_step, block033_data_flat043_original, block033_data_flat044_original]
def block033_data_flat046 : CoefficientMerge.Poly := [(nat_lit 9117, Int.ofNat (nat_lit 646813536768000)), (nat_lit 9118, Int.ofNat (nat_lit 564551442201600)), (nat_lit 9119, Int.ofNat (nat_lit 760681790668800))]
theorem block033_data_flat046_step : block033_data_flat046 = (CoefficientMerge.fastMerge block033_data_flat042 block033_data_flat045) := by decide +kernel
theorem block033_data_flat046_original : block033_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded))) := by
  rw [block033_data_flat046_step, block033_data_flat042_original, block033_data_flat045_original]
def block033_data_flat047 : CoefficientMerge.Poly := [(nat_lit 9115, Int.ofNat (nat_lit 86391113840640)), (nat_lit 9116, Int.ofNat (nat_lit 505631540736000)), (nat_lit 9117, Int.ofNat (nat_lit 646813536768000)), (nat_lit 9118, Int.ofNat (nat_lit 564551442201600)), (nat_lit 9119, Int.ofNat (nat_lit 760681790668800))]
theorem block033_data_flat047_step : block033_data_flat047 = (CoefficientMerge.fastMerge block033_data_flat041 block033_data_flat046) := by decide +kernel
theorem block033_data_flat047_original : block033_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded)))) := by
  rw [block033_data_flat047_step, block033_data_flat041_original, block033_data_flat046_original]
def block033_data_flat048 : CoefficientMerge.Poly := [(nat_lit 9140, Int.ofNat (nat_lit 379709468006400))]
theorem block033_data_flat048_step : block033_data_flat048 = (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) := by decide +kernel
theorem block033_data_flat048_original : block033_data_flat048 = (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) := by
  rw [block033_data_flat048_step]
def block033_data_flat049 : CoefficientMerge.Poly := [(nat_lit 9141, Int.ofNat (nat_lit 776088617472000))]
theorem block033_data_flat049_step : block033_data_flat049 = (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded) := by decide +kernel
theorem block033_data_flat049_original : block033_data_flat049 = (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded) := by
  rw [block033_data_flat049_step]
def block033_data_flat050 : CoefficientMerge.Poly := [(nat_lit 9140, Int.ofNat (nat_lit 379709468006400)), (nat_lit 9141, Int.ofNat (nat_lit 776088617472000))]
theorem block033_data_flat050_step : block033_data_flat050 = (CoefficientMerge.fastMerge block033_data_flat048 block033_data_flat049) := by decide +kernel
theorem block033_data_flat050_original : block033_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded)) := by
  rw [block033_data_flat050_step, block033_data_flat048_original, block033_data_flat049_original]
def block033_data_flat051 : CoefficientMerge.Poly := [(nat_lit 9142, Int.ofNat (nat_lit 671767480339200))]
theorem block033_data_flat051_step : block033_data_flat051 = (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) := by decide +kernel
theorem block033_data_flat051_original : block033_data_flat051 = (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) := by
  rw [block033_data_flat051_step]
def block033_data_flat052 : CoefficientMerge.Poly := [(nat_lit 9143, Int.ofNat (nat_lit 726466161254400))]
theorem block033_data_flat052_step : block033_data_flat052 = (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) := by decide +kernel
theorem block033_data_flat052_original : block033_data_flat052 = (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) := by
  rw [block033_data_flat052_step]
def block033_data_flat053 : CoefficientMerge.Poly := [(nat_lit 9165, Int.ofNat (nat_lit 347050500249600))]
theorem block033_data_flat053_step : block033_data_flat053 = (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded) := by decide +kernel
theorem block033_data_flat053_original : block033_data_flat053 = (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded) := by
  rw [block033_data_flat053_step]
def block033_data_flat054 : CoefficientMerge.Poly := [(nat_lit 9143, Int.ofNat (nat_lit 726466161254400)), (nat_lit 9165, Int.ofNat (nat_lit 347050500249600))]
theorem block033_data_flat054_step : block033_data_flat054 = (CoefficientMerge.fastMerge block033_data_flat052 block033_data_flat053) := by decide +kernel
theorem block033_data_flat054_original : block033_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded)) := by
  rw [block033_data_flat054_step, block033_data_flat052_original, block033_data_flat053_original]
def block033_data_flat055 : CoefficientMerge.Poly := [(nat_lit 9142, Int.ofNat (nat_lit 671767480339200)), (nat_lit 9143, Int.ofNat (nat_lit 726466161254400)), (nat_lit 9165, Int.ofNat (nat_lit 347050500249600))]
theorem block033_data_flat055_step : block033_data_flat055 = (CoefficientMerge.fastMerge block033_data_flat051 block033_data_flat054) := by decide +kernel
theorem block033_data_flat055_original : block033_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded))) := by
  rw [block033_data_flat055_step, block033_data_flat051_original, block033_data_flat054_original]
def block033_data_flat056 : CoefficientMerge.Poly := [(nat_lit 9140, Int.ofNat (nat_lit 379709468006400)), (nat_lit 9141, Int.ofNat (nat_lit 776088617472000)), (nat_lit 9142, Int.ofNat (nat_lit 671767480339200)), (nat_lit 9143, Int.ofNat (nat_lit 726466161254400)), (nat_lit 9165, Int.ofNat (nat_lit 347050500249600))]
theorem block033_data_flat056_step : block033_data_flat056 = (CoefficientMerge.fastMerge block033_data_flat050 block033_data_flat055) := by decide +kernel
theorem block033_data_flat056_original : block033_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded)))) := by
  rw [block033_data_flat056_step, block033_data_flat050_original, block033_data_flat055_original]
def block033_data_flat057 : CoefficientMerge.Poly := [(nat_lit 9115, Int.ofNat (nat_lit 86391113840640)), (nat_lit 9116, Int.ofNat (nat_lit 505631540736000)), (nat_lit 9117, Int.ofNat (nat_lit 646813536768000)), (nat_lit 9118, Int.ofNat (nat_lit 564551442201600)), (nat_lit 9119, Int.ofNat (nat_lit 760681790668800)), (nat_lit 9140, Int.ofNat (nat_lit 379709468006400)), (nat_lit 9141, Int.ofNat (nat_lit 776088617472000)), (nat_lit 9142, Int.ofNat (nat_lit 671767480339200)), (nat_lit 9143, Int.ofNat (nat_lit 726466161254400)), (nat_lit 9165, Int.ofNat (nat_lit 347050500249600))]
theorem block033_data_flat057_step : block033_data_flat057 = (CoefficientMerge.fastMerge block033_data_flat047 block033_data_flat056) := by decide +kernel
theorem block033_data_flat057_original : block033_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded))))) := by
  rw [block033_data_flat057_step, block033_data_flat047_original, block033_data_flat056_original]
def block033_data_flat058 : CoefficientMerge.Poly := [(nat_lit 9166, Int.ofNat (nat_lit 657396548726400))]
theorem block033_data_flat058_step : block033_data_flat058 = (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) := by decide +kernel
theorem block033_data_flat058_original : block033_data_flat058 = (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) := by
  rw [block033_data_flat058_step]
def block033_data_flat059 : CoefficientMerge.Poly := [(nat_lit 9167, Int.ofNat (nat_lit 747558411264000))]
theorem block033_data_flat059_step : block033_data_flat059 = (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded) := by decide +kernel
theorem block033_data_flat059_original : block033_data_flat059 = (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded) := by
  rw [block033_data_flat059_step]
def block033_data_flat060 : CoefficientMerge.Poly := [(nat_lit 9166, Int.ofNat (nat_lit 657396548726400)), (nat_lit 9167, Int.ofNat (nat_lit 747558411264000))]
theorem block033_data_flat060_step : block033_data_flat060 = (CoefficientMerge.fastMerge block033_data_flat058 block033_data_flat059) := by decide +kernel
theorem block033_data_flat060_original : block033_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded)) := by
  rw [block033_data_flat060_step, block033_data_flat058_original, block033_data_flat059_original]
def block033_data_flat061 : CoefficientMerge.Poly := [(nat_lit 9190, Int.ofNat (nat_lit 276807592656000))]
theorem block033_data_flat061_step : block033_data_flat061 = (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) := by decide +kernel
theorem block033_data_flat061_original : block033_data_flat061 = (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) := by
  rw [block033_data_flat061_step]
def block033_data_flat062 : CoefficientMerge.Poly := [(nat_lit 9191, Int.ofNat (nat_lit 682549021425600))]
theorem block033_data_flat062_step : block033_data_flat062 = (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) := by decide +kernel
theorem block033_data_flat062_original : block033_data_flat062 = (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) := by
  rw [block033_data_flat062_step]
def block033_data_flat063 : CoefficientMerge.Poly := [(nat_lit 9215, Int.ofNat (nat_lit 367217515929600))]
theorem block033_data_flat063_step : block033_data_flat063 = (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded) := by decide +kernel
theorem block033_data_flat063_original : block033_data_flat063 = (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded) := by
  rw [block033_data_flat063_step]
def block033_data_flat064 : CoefficientMerge.Poly := [(nat_lit 9191, Int.ofNat (nat_lit 682549021425600)), (nat_lit 9215, Int.ofNat (nat_lit 367217515929600))]
theorem block033_data_flat064_step : block033_data_flat064 = (CoefficientMerge.fastMerge block033_data_flat062 block033_data_flat063) := by decide +kernel
theorem block033_data_flat064_original : block033_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded)) := by
  rw [block033_data_flat064_step, block033_data_flat062_original, block033_data_flat063_original]
def block033_data_flat065 : CoefficientMerge.Poly := [(nat_lit 9190, Int.ofNat (nat_lit 276807592656000)), (nat_lit 9191, Int.ofNat (nat_lit 682549021425600)), (nat_lit 9215, Int.ofNat (nat_lit 367217515929600))]
theorem block033_data_flat065_step : block033_data_flat065 = (CoefficientMerge.fastMerge block033_data_flat061 block033_data_flat064) := by decide +kernel
theorem block033_data_flat065_original : block033_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded))) := by
  rw [block033_data_flat065_step, block033_data_flat061_original, block033_data_flat064_original]
def block033_data_flat066 : CoefficientMerge.Poly := [(nat_lit 9166, Int.ofNat (nat_lit 657396548726400)), (nat_lit 9167, Int.ofNat (nat_lit 747558411264000)), (nat_lit 9190, Int.ofNat (nat_lit 276807592656000)), (nat_lit 9191, Int.ofNat (nat_lit 682549021425600)), (nat_lit 9215, Int.ofNat (nat_lit 367217515929600))]
theorem block033_data_flat066_step : block033_data_flat066 = (CoefficientMerge.fastMerge block033_data_flat060 block033_data_flat065) := by decide +kernel
theorem block033_data_flat066_original : block033_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded)))) := by
  rw [block033_data_flat066_step, block033_data_flat060_original, block033_data_flat065_original]
def block033_data_flat067 : CoefficientMerge.Poly := [(nat_lit 9616, Int.ofNat (nat_lit 1027680192000))]
theorem block033_data_flat067_step : block033_data_flat067 = (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) := by decide +kernel
theorem block033_data_flat067_original : block033_data_flat067 = (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) := by
  rw [block033_data_flat067_step]
def block033_data_flat068 : CoefficientMerge.Poly := [(nat_lit 9618, Int.ofNat (nat_lit 7461795801600))]
theorem block033_data_flat068_step : block033_data_flat068 = (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded) := by decide +kernel
theorem block033_data_flat068_original : block033_data_flat068 = (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded) := by
  rw [block033_data_flat068_step]
def block033_data_flat069 : CoefficientMerge.Poly := [(nat_lit 9616, Int.ofNat (nat_lit 1027680192000)), (nat_lit 9618, Int.ofNat (nat_lit 7461795801600))]
theorem block033_data_flat069_step : block033_data_flat069 = (CoefficientMerge.fastMerge block033_data_flat067 block033_data_flat068) := by decide +kernel
theorem block033_data_flat069_original : block033_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded)) := by
  rw [block033_data_flat069_step, block033_data_flat067_original, block033_data_flat068_original]
def block033_data_flat070 : CoefficientMerge.Poly := [(nat_lit 9620, Int.ofNat (nat_lit 109950182899200))]
theorem block033_data_flat070_step : block033_data_flat070 = (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) := by decide +kernel
theorem block033_data_flat070_original : block033_data_flat070 = (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) := by
  rw [block033_data_flat070_step]
def block033_data_flat071 : CoefficientMerge.Poly := [(nat_lit 9621, Int.ofNat (nat_lit 102488387097600))]
theorem block033_data_flat071_step : block033_data_flat071 = (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) := by decide +kernel
theorem block033_data_flat071_original : block033_data_flat071 = (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) := by
  rw [block033_data_flat071_step]
def block033_data_flat072 : CoefficientMerge.Poly := [(nat_lit 9623, Int.ofNat (nat_lit 102213909504000))]
theorem block033_data_flat072_step : block033_data_flat072 = (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded) := by decide +kernel
theorem block033_data_flat072_original : block033_data_flat072 = (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded) := by
  rw [block033_data_flat072_step]
def block033_data_flat073 : CoefficientMerge.Poly := [(nat_lit 9621, Int.ofNat (nat_lit 102488387097600)), (nat_lit 9623, Int.ofNat (nat_lit 102213909504000))]
theorem block033_data_flat073_step : block033_data_flat073 = (CoefficientMerge.fastMerge block033_data_flat071 block033_data_flat072) := by decide +kernel
theorem block033_data_flat073_original : block033_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded)) := by
  rw [block033_data_flat073_step, block033_data_flat071_original, block033_data_flat072_original]
def block033_data_flat074 : CoefficientMerge.Poly := [(nat_lit 9620, Int.ofNat (nat_lit 109950182899200)), (nat_lit 9621, Int.ofNat (nat_lit 102488387097600)), (nat_lit 9623, Int.ofNat (nat_lit 102213909504000))]
theorem block033_data_flat074_step : block033_data_flat074 = (CoefficientMerge.fastMerge block033_data_flat070 block033_data_flat073) := by decide +kernel
theorem block033_data_flat074_original : block033_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded))) := by
  rw [block033_data_flat074_step, block033_data_flat070_original, block033_data_flat073_original]
def block033_data_flat075 : CoefficientMerge.Poly := [(nat_lit 9616, Int.ofNat (nat_lit 1027680192000)), (nat_lit 9618, Int.ofNat (nat_lit 7461795801600)), (nat_lit 9620, Int.ofNat (nat_lit 109950182899200)), (nat_lit 9621, Int.ofNat (nat_lit 102488387097600)), (nat_lit 9623, Int.ofNat (nat_lit 102213909504000))]
theorem block033_data_flat075_step : block033_data_flat075 = (CoefficientMerge.fastMerge block033_data_flat069 block033_data_flat074) := by decide +kernel
theorem block033_data_flat075_original : block033_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded)))) := by
  rw [block033_data_flat075_step, block033_data_flat069_original, block033_data_flat074_original]
def block033_data_flat076 : CoefficientMerge.Poly := [(nat_lit 9166, Int.ofNat (nat_lit 657396548726400)), (nat_lit 9167, Int.ofNat (nat_lit 747558411264000)), (nat_lit 9190, Int.ofNat (nat_lit 276807592656000)), (nat_lit 9191, Int.ofNat (nat_lit 682549021425600)), (nat_lit 9215, Int.ofNat (nat_lit 367217515929600)), (nat_lit 9616, Int.ofNat (nat_lit 1027680192000)), (nat_lit 9618, Int.ofNat (nat_lit 7461795801600)), (nat_lit 9620, Int.ofNat (nat_lit 109950182899200)), (nat_lit 9621, Int.ofNat (nat_lit 102488387097600)), (nat_lit 9623, Int.ofNat (nat_lit 102213909504000))]
theorem block033_data_flat076_step : block033_data_flat076 = (CoefficientMerge.fastMerge block033_data_flat066 block033_data_flat075) := by decide +kernel
theorem block033_data_flat076_original : block033_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded))))) := by
  rw [block033_data_flat076_step, block033_data_flat066_original, block033_data_flat075_original]
def block033_data_flat077 : CoefficientMerge.Poly := [(nat_lit 9115, Int.ofNat (nat_lit 86391113840640)), (nat_lit 9116, Int.ofNat (nat_lit 505631540736000)), (nat_lit 9117, Int.ofNat (nat_lit 646813536768000)), (nat_lit 9118, Int.ofNat (nat_lit 564551442201600)), (nat_lit 9119, Int.ofNat (nat_lit 760681790668800)), (nat_lit 9140, Int.ofNat (nat_lit 379709468006400)), (nat_lit 9141, Int.ofNat (nat_lit 776088617472000)), (nat_lit 9142, Int.ofNat (nat_lit 671767480339200)), (nat_lit 9143, Int.ofNat (nat_lit 726466161254400)), (nat_lit 9165, Int.ofNat (nat_lit 347050500249600)), (nat_lit 9166, Int.ofNat (nat_lit 657396548726400)), (nat_lit 9167, Int.ofNat (nat_lit 747558411264000)), (nat_lit 9190, Int.ofNat (nat_lit 276807592656000)), (nat_lit 9191, Int.ofNat (nat_lit 682549021425600)), (nat_lit 9215, Int.ofNat (nat_lit 367217515929600)), (nat_lit 9616, Int.ofNat (nat_lit 1027680192000)), (nat_lit 9618, Int.ofNat (nat_lit 7461795801600)), (nat_lit 9620, Int.ofNat (nat_lit 109950182899200)), (nat_lit 9621, Int.ofNat (nat_lit 102488387097600)), (nat_lit 9623, Int.ofNat (nat_lit 102213909504000))]
theorem block033_data_flat077_step : block033_data_flat077 = (CoefficientMerge.fastMerge block033_data_flat057 block033_data_flat076) := by decide +kernel
theorem block033_data_flat077_original : block033_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded)))))) := by
  rw [block033_data_flat077_step, block033_data_flat057_original, block033_data_flat076_original]
def block033_data_flat078 : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 65163300249600)), (nat_lit 9023, Int.ofNat (nat_lit 5211208396800)), (nat_lit 9042, Int.ofNat (nat_lit 24896019778560)), (nat_lit 9044, Int.ofNat (nat_lit 233856198374400)), (nat_lit 9045, Int.ofNat (nat_lit 220828821696000)), (nat_lit 9046, Int.ofNat (nat_lit 99469520156160)), (nat_lit 9047, Int.ofNat (nat_lit 259121345414400)), (nat_lit 9065, Int.ofNat (nat_lit 8561639116800)), (nat_lit 9066, Int.ofNat (nat_lit 35057102976000)), (nat_lit 9067, Int.ofNat (nat_lit 40411348992000)), (nat_lit 9068, Int.ofNat (nat_lit 327449191910400)), (nat_lit 9069, Int.ofNat (nat_lit 349177379443200)), (nat_lit 9070, Int.ofNat (nat_lit 284381337945600)), (nat_lit 9071, Int.ofNat (nat_lit 503972755372800)), (nat_lit 9090, Int.ofNat (nat_lit 71490459801600)), (nat_lit 9091, Int.ofNat (nat_lit 197412532531200)), (nat_lit 9092, Int.ofNat (nat_lit 533527742361600)), (nat_lit 9093, Int.ofNat (nat_lit 587959355289600)), (nat_lit 9094, Int.ofNat (nat_lit 457214273107200)), (nat_lit 9095, Int.ofNat (nat_lit 739589540659200)), (nat_lit 9115, Int.ofNat (nat_lit 86391113840640)), (nat_lit 9116, Int.ofNat (nat_lit 505631540736000)), (nat_lit 9117, Int.ofNat (nat_lit 646813536768000)), (nat_lit 9118, Int.ofNat (nat_lit 564551442201600)), (nat_lit 9119, Int.ofNat (nat_lit 760681790668800)), (nat_lit 9140, Int.ofNat (nat_lit 379709468006400)), (nat_lit 9141, Int.ofNat (nat_lit 776088617472000)), (nat_lit 9142, Int.ofNat (nat_lit 671767480339200)), (nat_lit 9143, Int.ofNat (nat_lit 726466161254400)), (nat_lit 9165, Int.ofNat (nat_lit 347050500249600)), (nat_lit 9166, Int.ofNat (nat_lit 657396548726400)), (nat_lit 9167, Int.ofNat (nat_lit 747558411264000)), (nat_lit 9190, Int.ofNat (nat_lit 276807592656000)), (nat_lit 9191, Int.ofNat (nat_lit 682549021425600)), (nat_lit 9215, Int.ofNat (nat_lit 367217515929600)), (nat_lit 9616, Int.ofNat (nat_lit 1027680192000)), (nat_lit 9618, Int.ofNat (nat_lit 7461795801600)), (nat_lit 9620, Int.ofNat (nat_lit 109950182899200)), (nat_lit 9621, Int.ofNat (nat_lit 102488387097600)), (nat_lit 9623, Int.ofNat (nat_lit 102213909504000))]
theorem block033_data_flat078_step : block033_data_flat078 = (CoefficientMerge.fastMerge block033_data_flat038 block033_data_flat077) := by decide +kernel
theorem block033_data_flat078_original : block033_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded))))))) := by
  rw [block033_data_flat078_step, block033_data_flat038_original, block033_data_flat077_original]
def block033_data_flat079 : CoefficientMerge.Poly := [(nat_lit 9641, Int.ofNat (nat_lit 2395557964800))]
theorem block033_data_flat079_step : block033_data_flat079 = (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) := by decide +kernel
theorem block033_data_flat079_original : block033_data_flat079 = (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) := by
  rw [block033_data_flat079_step]
def block033_data_flat080 : CoefficientMerge.Poly := [(nat_lit 9643, Int.ofNat (nat_lit 9886777420800))]
theorem block033_data_flat080_step : block033_data_flat080 = (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded) := by decide +kernel
theorem block033_data_flat080_original : block033_data_flat080 = (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded) := by
  rw [block033_data_flat080_step]
def block033_data_flat081 : CoefficientMerge.Poly := [(nat_lit 9641, Int.ofNat (nat_lit 2395557964800)), (nat_lit 9643, Int.ofNat (nat_lit 9886777420800))]
theorem block033_data_flat081_step : block033_data_flat081 = (CoefficientMerge.fastMerge block033_data_flat079 block033_data_flat080) := by decide +kernel
theorem block033_data_flat081_original : block033_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded)) := by
  rw [block033_data_flat081_step, block033_data_flat079_original, block033_data_flat080_original]
def block033_data_flat082 : CoefficientMerge.Poly := [(nat_lit 9644, Int.ofNat (nat_lit 292154122444800))]
theorem block033_data_flat082_step : block033_data_flat082 = (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) := by decide +kernel
theorem block033_data_flat082_original : block033_data_flat082 = (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) := by
  rw [block033_data_flat082_step]
def block033_data_flat083 : CoefficientMerge.Poly := [(nat_lit 9645, Int.ofNat (nat_lit 317089058764800))]
theorem block033_data_flat083_step : block033_data_flat083 = (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) := by decide +kernel
theorem block033_data_flat083_original : block033_data_flat083 = (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) := by
  rw [block033_data_flat083_step]
def block033_data_flat084 : CoefficientMerge.Poly := [(nat_lit 9646, Int.ofNat (nat_lit 188403739776000))]
theorem block033_data_flat084_step : block033_data_flat084 = (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded) := by decide +kernel
theorem block033_data_flat084_original : block033_data_flat084 = (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded) := by
  rw [block033_data_flat084_step]
def block033_data_flat085 : CoefficientMerge.Poly := [(nat_lit 9645, Int.ofNat (nat_lit 317089058764800)), (nat_lit 9646, Int.ofNat (nat_lit 188403739776000))]
theorem block033_data_flat085_step : block033_data_flat085 = (CoefficientMerge.fastMerge block033_data_flat083 block033_data_flat084) := by decide +kernel
theorem block033_data_flat085_original : block033_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded)) := by
  rw [block033_data_flat085_step, block033_data_flat083_original, block033_data_flat084_original]
def block033_data_flat086 : CoefficientMerge.Poly := [(nat_lit 9644, Int.ofNat (nat_lit 292154122444800)), (nat_lit 9645, Int.ofNat (nat_lit 317089058764800)), (nat_lit 9646, Int.ofNat (nat_lit 188403739776000))]
theorem block033_data_flat086_step : block033_data_flat086 = (CoefficientMerge.fastMerge block033_data_flat082 block033_data_flat085) := by decide +kernel
theorem block033_data_flat086_original : block033_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded))) := by
  rw [block033_data_flat086_step, block033_data_flat082_original, block033_data_flat085_original]
def block033_data_flat087 : CoefficientMerge.Poly := [(nat_lit 9641, Int.ofNat (nat_lit 2395557964800)), (nat_lit 9643, Int.ofNat (nat_lit 9886777420800)), (nat_lit 9644, Int.ofNat (nat_lit 292154122444800)), (nat_lit 9645, Int.ofNat (nat_lit 317089058764800)), (nat_lit 9646, Int.ofNat (nat_lit 188403739776000))]
theorem block033_data_flat087_step : block033_data_flat087 = (CoefficientMerge.fastMerge block033_data_flat081 block033_data_flat086) := by decide +kernel
theorem block033_data_flat087_original : block033_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded)))) := by
  rw [block033_data_flat087_step, block033_data_flat081_original, block033_data_flat086_original]
def block033_data_flat088 : CoefficientMerge.Poly := [(nat_lit 9647, Int.ofNat (nat_lit 477770776358400))]
theorem block033_data_flat088_step : block033_data_flat088 = (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) := by decide +kernel
theorem block033_data_flat088_original : block033_data_flat088 = (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) := by
  rw [block033_data_flat088_step]
def block033_data_flat089 : CoefficientMerge.Poly := [(nat_lit 9666, Int.ofNat (nat_lit 41516346816000))]
theorem block033_data_flat089_step : block033_data_flat089 = (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded) := by decide +kernel
theorem block033_data_flat089_original : block033_data_flat089 = (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded) := by
  rw [block033_data_flat089_step]
def block033_data_flat090 : CoefficientMerge.Poly := [(nat_lit 9647, Int.ofNat (nat_lit 477770776358400)), (nat_lit 9666, Int.ofNat (nat_lit 41516346816000))]
theorem block033_data_flat090_step : block033_data_flat090 = (CoefficientMerge.fastMerge block033_data_flat088 block033_data_flat089) := by decide +kernel
theorem block033_data_flat090_original : block033_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded)) := by
  rw [block033_data_flat090_step, block033_data_flat088_original, block033_data_flat089_original]
def block033_data_flat091 : CoefficientMerge.Poly := [(nat_lit 9667, Int.ofNat (nat_lit 149668894771200))]
theorem block033_data_flat091_step : block033_data_flat091 = (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) := by decide +kernel
theorem block033_data_flat091_original : block033_data_flat091 = (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) := by
  rw [block033_data_flat091_step]
def block033_data_flat092 : CoefficientMerge.Poly := [(nat_lit 9668, Int.ofNat (nat_lit 497988692812800))]
theorem block033_data_flat092_step : block033_data_flat092 = (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) := by decide +kernel
theorem block033_data_flat092_original : block033_data_flat092 = (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) := by
  rw [block033_data_flat092_step]
def block033_data_flat093 : CoefficientMerge.Poly := [(nat_lit 9669, Int.ofNat (nat_lit 564624893952000))]
theorem block033_data_flat093_step : block033_data_flat093 = (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded) := by decide +kernel
theorem block033_data_flat093_original : block033_data_flat093 = (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded) := by
  rw [block033_data_flat093_step]
def block033_data_flat094 : CoefficientMerge.Poly := [(nat_lit 9668, Int.ofNat (nat_lit 497988692812800)), (nat_lit 9669, Int.ofNat (nat_lit 564624893952000))]
theorem block033_data_flat094_step : block033_data_flat094 = (CoefficientMerge.fastMerge block033_data_flat092 block033_data_flat093) := by decide +kernel
theorem block033_data_flat094_original : block033_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded)) := by
  rw [block033_data_flat094_step, block033_data_flat092_original, block033_data_flat093_original]
def block033_data_flat095 : CoefficientMerge.Poly := [(nat_lit 9667, Int.ofNat (nat_lit 149668894771200)), (nat_lit 9668, Int.ofNat (nat_lit 497988692812800)), (nat_lit 9669, Int.ofNat (nat_lit 564624893952000))]
theorem block033_data_flat095_step : block033_data_flat095 = (CoefficientMerge.fastMerge block033_data_flat091 block033_data_flat094) := by decide +kernel
theorem block033_data_flat095_original : block033_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded))) := by
  rw [block033_data_flat095_step, block033_data_flat091_original, block033_data_flat094_original]
def block033_data_flat096 : CoefficientMerge.Poly := [(nat_lit 9647, Int.ofNat (nat_lit 477770776358400)), (nat_lit 9666, Int.ofNat (nat_lit 41516346816000)), (nat_lit 9667, Int.ofNat (nat_lit 149668894771200)), (nat_lit 9668, Int.ofNat (nat_lit 497988692812800)), (nat_lit 9669, Int.ofNat (nat_lit 564624893952000))]
theorem block033_data_flat096_step : block033_data_flat096 = (CoefficientMerge.fastMerge block033_data_flat090 block033_data_flat095) := by decide +kernel
theorem block033_data_flat096_original : block033_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded)))) := by
  rw [block033_data_flat096_step, block033_data_flat090_original, block033_data_flat095_original]
def block033_data_flat097 : CoefficientMerge.Poly := [(nat_lit 9641, Int.ofNat (nat_lit 2395557964800)), (nat_lit 9643, Int.ofNat (nat_lit 9886777420800)), (nat_lit 9644, Int.ofNat (nat_lit 292154122444800)), (nat_lit 9645, Int.ofNat (nat_lit 317089058764800)), (nat_lit 9646, Int.ofNat (nat_lit 188403739776000)), (nat_lit 9647, Int.ofNat (nat_lit 477770776358400)), (nat_lit 9666, Int.ofNat (nat_lit 41516346816000)), (nat_lit 9667, Int.ofNat (nat_lit 149668894771200)), (nat_lit 9668, Int.ofNat (nat_lit 497988692812800)), (nat_lit 9669, Int.ofNat (nat_lit 564624893952000))]
theorem block033_data_flat097_step : block033_data_flat097 = (CoefficientMerge.fastMerge block033_data_flat087 block033_data_flat096) := by decide +kernel
theorem block033_data_flat097_original : block033_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded))))) := by
  rw [block033_data_flat097_step, block033_data_flat087_original, block033_data_flat096_original]
def block033_data_flat098 : CoefficientMerge.Poly := [(nat_lit 9670, Int.ofNat (nat_lit 426558798489600))]
theorem block033_data_flat098_step : block033_data_flat098 = (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) := by decide +kernel
theorem block033_data_flat098_original : block033_data_flat098 = (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) := by
  rw [block033_data_flat098_step]
def block033_data_flat099 : CoefficientMerge.Poly := [(nat_lit 9671, Int.ofNat (nat_lit 759406049740800))]
theorem block033_data_flat099_step : block033_data_flat099 = (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded) := by decide +kernel
theorem block033_data_flat099_original : block033_data_flat099 = (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded) := by
  rw [block033_data_flat099_step]
def block033_data_flat100 : CoefficientMerge.Poly := [(nat_lit 9670, Int.ofNat (nat_lit 426558798489600)), (nat_lit 9671, Int.ofNat (nat_lit 759406049740800))]
theorem block033_data_flat100_step : block033_data_flat100 = (CoefficientMerge.fastMerge block033_data_flat098 block033_data_flat099) := by decide +kernel
theorem block033_data_flat100_original : block033_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded)) := by
  rw [block033_data_flat100_step, block033_data_flat098_original, block033_data_flat099_original]
def block033_data_flat101 : CoefficientMerge.Poly := [(nat_lit 9691, Int.ofNat (nat_lit 65538548490240))]
theorem block033_data_flat101_step : block033_data_flat101 = (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) := by decide +kernel
theorem block033_data_flat101_original : block033_data_flat101 = (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) := by
  rw [block033_data_flat101_step]
def block033_data_flat102 : CoefficientMerge.Poly := [(nat_lit 9692, Int.ofNat (nat_lit 477151590988800))]
theorem block033_data_flat102_step : block033_data_flat102 = (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) := by decide +kernel
theorem block033_data_flat102_original : block033_data_flat102 = (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) := by
  rw [block033_data_flat102_step]
def block033_data_flat103 : CoefficientMerge.Poly := [(nat_lit 9693, Int.ofNat (nat_lit 631558767974400))]
theorem block033_data_flat103_step : block033_data_flat103 = (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded) := by decide +kernel
theorem block033_data_flat103_original : block033_data_flat103 = (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded) := by
  rw [block033_data_flat103_step]
def block033_data_flat104 : CoefficientMerge.Poly := [(nat_lit 9692, Int.ofNat (nat_lit 477151590988800)), (nat_lit 9693, Int.ofNat (nat_lit 631558767974400))]
theorem block033_data_flat104_step : block033_data_flat104 = (CoefficientMerge.fastMerge block033_data_flat102 block033_data_flat103) := by decide +kernel
theorem block033_data_flat104_original : block033_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded)) := by
  rw [block033_data_flat104_step, block033_data_flat102_original, block033_data_flat103_original]
def block033_data_flat105 : CoefficientMerge.Poly := [(nat_lit 9691, Int.ofNat (nat_lit 65538548490240)), (nat_lit 9692, Int.ofNat (nat_lit 477151590988800)), (nat_lit 9693, Int.ofNat (nat_lit 631558767974400))]
theorem block033_data_flat105_step : block033_data_flat105 = (CoefficientMerge.fastMerge block033_data_flat101 block033_data_flat104) := by decide +kernel
theorem block033_data_flat105_original : block033_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded))) := by
  rw [block033_data_flat105_step, block033_data_flat101_original, block033_data_flat104_original]
def block033_data_flat106 : CoefficientMerge.Poly := [(nat_lit 9670, Int.ofNat (nat_lit 426558798489600)), (nat_lit 9671, Int.ofNat (nat_lit 759406049740800)), (nat_lit 9691, Int.ofNat (nat_lit 65538548490240)), (nat_lit 9692, Int.ofNat (nat_lit 477151590988800)), (nat_lit 9693, Int.ofNat (nat_lit 631558767974400))]
theorem block033_data_flat106_step : block033_data_flat106 = (CoefficientMerge.fastMerge block033_data_flat100 block033_data_flat105) := by decide +kernel
theorem block033_data_flat106_original : block033_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded)))) := by
  rw [block033_data_flat106_step, block033_data_flat100_original, block033_data_flat105_original]
def block033_data_flat107 : CoefficientMerge.Poly := [(nat_lit 9694, Int.ofNat (nat_lit 581263648358400))]
theorem block033_data_flat107_step : block033_data_flat107 = (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) := by decide +kernel
theorem block033_data_flat107_original : block033_data_flat107 = (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) := by
  rw [block033_data_flat107_step]
def block033_data_flat108 : CoefficientMerge.Poly := [(nat_lit 9695, Int.ofNat (nat_lit 790619177779200))]
theorem block033_data_flat108_step : block033_data_flat108 = (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded) := by decide +kernel
theorem block033_data_flat108_original : block033_data_flat108 = (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded) := by
  rw [block033_data_flat108_step]
def block033_data_flat109 : CoefficientMerge.Poly := [(nat_lit 9694, Int.ofNat (nat_lit 581263648358400)), (nat_lit 9695, Int.ofNat (nat_lit 790619177779200))]
theorem block033_data_flat109_step : block033_data_flat109 = (CoefficientMerge.fastMerge block033_data_flat107 block033_data_flat108) := by decide +kernel
theorem block033_data_flat109_original : block033_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded)) := by
  rw [block033_data_flat109_step, block033_data_flat107_original, block033_data_flat108_original]
def block033_data_flat110 : CoefficientMerge.Poly := [(nat_lit 9716, Int.ofNat (nat_lit 368999043033600))]
theorem block033_data_flat110_step : block033_data_flat110 = (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) := by decide +kernel
theorem block033_data_flat110_original : block033_data_flat110 = (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) := by
  rw [block033_data_flat110_step]
def block033_data_flat111 : CoefficientMerge.Poly := [(nat_lit 9717, Int.ofNat (nat_lit 768913541222400))]
theorem block033_data_flat111_step : block033_data_flat111 = (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) := by decide +kernel
theorem block033_data_flat111_original : block033_data_flat111 = (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) := by
  rw [block033_data_flat111_step]
def block033_data_flat112 : CoefficientMerge.Poly := [(nat_lit 9718, Int.ofNat (nat_lit 735847367270400))]
theorem block033_data_flat112_step : block033_data_flat112 = (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded) := by decide +kernel
theorem block033_data_flat112_original : block033_data_flat112 = (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded) := by
  rw [block033_data_flat112_step]
def block033_data_flat113 : CoefficientMerge.Poly := [(nat_lit 9717, Int.ofNat (nat_lit 768913541222400)), (nat_lit 9718, Int.ofNat (nat_lit 735847367270400))]
theorem block033_data_flat113_step : block033_data_flat113 = (CoefficientMerge.fastMerge block033_data_flat111 block033_data_flat112) := by decide +kernel
theorem block033_data_flat113_original : block033_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded)) := by
  rw [block033_data_flat113_step, block033_data_flat111_original, block033_data_flat112_original]
def block033_data_flat114 : CoefficientMerge.Poly := [(nat_lit 9716, Int.ofNat (nat_lit 368999043033600)), (nat_lit 9717, Int.ofNat (nat_lit 768913541222400)), (nat_lit 9718, Int.ofNat (nat_lit 735847367270400))]
theorem block033_data_flat114_step : block033_data_flat114 = (CoefficientMerge.fastMerge block033_data_flat110 block033_data_flat113) := by decide +kernel
theorem block033_data_flat114_original : block033_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded))) := by
  rw [block033_data_flat114_step, block033_data_flat110_original, block033_data_flat113_original]
def block033_data_flat115 : CoefficientMerge.Poly := [(nat_lit 9694, Int.ofNat (nat_lit 581263648358400)), (nat_lit 9695, Int.ofNat (nat_lit 790619177779200)), (nat_lit 9716, Int.ofNat (nat_lit 368999043033600)), (nat_lit 9717, Int.ofNat (nat_lit 768913541222400)), (nat_lit 9718, Int.ofNat (nat_lit 735847367270400))]
theorem block033_data_flat115_step : block033_data_flat115 = (CoefficientMerge.fastMerge block033_data_flat109 block033_data_flat114) := by decide +kernel
theorem block033_data_flat115_original : block033_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded)))) := by
  rw [block033_data_flat115_step, block033_data_flat109_original, block033_data_flat114_original]
def block033_data_flat116 : CoefficientMerge.Poly := [(nat_lit 9670, Int.ofNat (nat_lit 426558798489600)), (nat_lit 9671, Int.ofNat (nat_lit 759406049740800)), (nat_lit 9691, Int.ofNat (nat_lit 65538548490240)), (nat_lit 9692, Int.ofNat (nat_lit 477151590988800)), (nat_lit 9693, Int.ofNat (nat_lit 631558767974400)), (nat_lit 9694, Int.ofNat (nat_lit 581263648358400)), (nat_lit 9695, Int.ofNat (nat_lit 790619177779200)), (nat_lit 9716, Int.ofNat (nat_lit 368999043033600)), (nat_lit 9717, Int.ofNat (nat_lit 768913541222400)), (nat_lit 9718, Int.ofNat (nat_lit 735847367270400))]
theorem block033_data_flat116_step : block033_data_flat116 = (CoefficientMerge.fastMerge block033_data_flat106 block033_data_flat115) := by decide +kernel
theorem block033_data_flat116_original : block033_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded))))) := by
  rw [block033_data_flat116_step, block033_data_flat106_original, block033_data_flat115_original]
def block033_data_flat117 : CoefficientMerge.Poly := [(nat_lit 9641, Int.ofNat (nat_lit 2395557964800)), (nat_lit 9643, Int.ofNat (nat_lit 9886777420800)), (nat_lit 9644, Int.ofNat (nat_lit 292154122444800)), (nat_lit 9645, Int.ofNat (nat_lit 317089058764800)), (nat_lit 9646, Int.ofNat (nat_lit 188403739776000)), (nat_lit 9647, Int.ofNat (nat_lit 477770776358400)), (nat_lit 9666, Int.ofNat (nat_lit 41516346816000)), (nat_lit 9667, Int.ofNat (nat_lit 149668894771200)), (nat_lit 9668, Int.ofNat (nat_lit 497988692812800)), (nat_lit 9669, Int.ofNat (nat_lit 564624893952000)), (nat_lit 9670, Int.ofNat (nat_lit 426558798489600)), (nat_lit 9671, Int.ofNat (nat_lit 759406049740800)), (nat_lit 9691, Int.ofNat (nat_lit 65538548490240)), (nat_lit 9692, Int.ofNat (nat_lit 477151590988800)), (nat_lit 9693, Int.ofNat (nat_lit 631558767974400)), (nat_lit 9694, Int.ofNat (nat_lit 581263648358400)), (nat_lit 9695, Int.ofNat (nat_lit 790619177779200)), (nat_lit 9716, Int.ofNat (nat_lit 368999043033600)), (nat_lit 9717, Int.ofNat (nat_lit 768913541222400)), (nat_lit 9718, Int.ofNat (nat_lit 735847367270400))]
theorem block033_data_flat117_step : block033_data_flat117 = (CoefficientMerge.fastMerge block033_data_flat097 block033_data_flat116) := by decide +kernel
theorem block033_data_flat117_original : block033_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded)))))) := by
  rw [block033_data_flat117_step, block033_data_flat097_original, block033_data_flat116_original]
def block033_data_flat118 : CoefficientMerge.Poly := [(nat_lit 9719, Int.ofNat (nat_lit 804008014387200))]
theorem block033_data_flat118_step : block033_data_flat118 = (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) := by decide +kernel
theorem block033_data_flat118_original : block033_data_flat118 = (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) := by
  rw [block033_data_flat118_step]
def block033_data_flat119 : CoefficientMerge.Poly := [(nat_lit 9741, Int.ofNat (nat_lit 347502808396800))]
theorem block033_data_flat119_step : block033_data_flat119 = (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded) := by decide +kernel
theorem block033_data_flat119_original : block033_data_flat119 = (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded) := by
  rw [block033_data_flat119_step]
def block033_data_flat120 : CoefficientMerge.Poly := [(nat_lit 9719, Int.ofNat (nat_lit 804008014387200)), (nat_lit 9741, Int.ofNat (nat_lit 347502808396800))]
theorem block033_data_flat120_step : block033_data_flat120 = (CoefficientMerge.fastMerge block033_data_flat118 block033_data_flat119) := by decide +kernel
theorem block033_data_flat120_original : block033_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded)) := by
  rw [block033_data_flat120_step, block033_data_flat118_original, block033_data_flat119_original]
def block033_data_flat121 : CoefficientMerge.Poly := [(nat_lit 9742, Int.ofNat (nat_lit 749710418688000))]
theorem block033_data_flat121_step : block033_data_flat121 = (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) := by decide +kernel
theorem block033_data_flat121_original : block033_data_flat121 = (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) := by
  rw [block033_data_flat121_step]
def block033_data_flat122 : CoefficientMerge.Poly := [(nat_lit 9743, Int.ofNat (nat_lit 835221142425600))]
theorem block033_data_flat122_step : block033_data_flat122 = (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) := by decide +kernel
theorem block033_data_flat122_original : block033_data_flat122 = (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) := by
  rw [block033_data_flat122_step]
def block033_data_flat123 : CoefficientMerge.Poly := [(nat_lit 9766, Int.ofNat (nat_lit 375348914640000))]
theorem block033_data_flat123_step : block033_data_flat123 = (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded) := by decide +kernel
theorem block033_data_flat123_original : block033_data_flat123 = (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded) := by
  rw [block033_data_flat123_step]
def block033_data_flat124 : CoefficientMerge.Poly := [(nat_lit 9743, Int.ofNat (nat_lit 835221142425600)), (nat_lit 9766, Int.ofNat (nat_lit 375348914640000))]
theorem block033_data_flat124_step : block033_data_flat124 = (CoefficientMerge.fastMerge block033_data_flat122 block033_data_flat123) := by decide +kernel
theorem block033_data_flat124_original : block033_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded)) := by
  rw [block033_data_flat124_step, block033_data_flat122_original, block033_data_flat123_original]
def block033_data_flat125 : CoefficientMerge.Poly := [(nat_lit 9742, Int.ofNat (nat_lit 749710418688000)), (nat_lit 9743, Int.ofNat (nat_lit 835221142425600)), (nat_lit 9766, Int.ofNat (nat_lit 375348914640000))]
theorem block033_data_flat125_step : block033_data_flat125 = (CoefficientMerge.fastMerge block033_data_flat121 block033_data_flat124) := by decide +kernel
theorem block033_data_flat125_original : block033_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded))) := by
  rw [block033_data_flat125_step, block033_data_flat121_original, block033_data_flat124_original]
def block033_data_flat126 : CoefficientMerge.Poly := [(nat_lit 9719, Int.ofNat (nat_lit 804008014387200)), (nat_lit 9741, Int.ofNat (nat_lit 347502808396800)), (nat_lit 9742, Int.ofNat (nat_lit 749710418688000)), (nat_lit 9743, Int.ofNat (nat_lit 835221142425600)), (nat_lit 9766, Int.ofNat (nat_lit 375348914640000))]
theorem block033_data_flat126_step : block033_data_flat126 = (CoefficientMerge.fastMerge block033_data_flat120 block033_data_flat125) := by decide +kernel
theorem block033_data_flat126_original : block033_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded)))) := by
  rw [block033_data_flat126_step, block033_data_flat120_original, block033_data_flat125_original]
def block033_data_flat127 : CoefficientMerge.Poly := [(nat_lit 9767, Int.ofNat (nat_lit 866434270464000))]
theorem block033_data_flat127_step : block033_data_flat127 = (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) := by decide +kernel
theorem block033_data_flat127_original : block033_data_flat127 = (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) := by
  rw [block033_data_flat127_step]
def block033_data_flat128 : CoefficientMerge.Poly := [(nat_lit 9791, Int.ofNat (nat_lit 439911553536000))]
theorem block033_data_flat128_step : block033_data_flat128 = (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded) := by decide +kernel
theorem block033_data_flat128_original : block033_data_flat128 = (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded) := by
  rw [block033_data_flat128_step]
def block033_data_flat129 : CoefficientMerge.Poly := [(nat_lit 9767, Int.ofNat (nat_lit 866434270464000)), (nat_lit 9791, Int.ofNat (nat_lit 439911553536000))]
theorem block033_data_flat129_step : block033_data_flat129 = (CoefficientMerge.fastMerge block033_data_flat127 block033_data_flat128) := by decide +kernel
theorem block033_data_flat129_original : block033_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded)) := by
  rw [block033_data_flat129_step, block033_data_flat127_original, block033_data_flat128_original]
def block033_data_flat130 : CoefficientMerge.Poly := [(nat_lit 10219, Int.ofNat (nat_lit 14841119462400))]
theorem block033_data_flat130_step : block033_data_flat130 = (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) := by decide +kernel
theorem block033_data_flat130_original : block033_data_flat130 = (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) := by
  rw [block033_data_flat130_step]
def block033_data_flat131 : CoefficientMerge.Poly := [(nat_lit 10220, Int.ofNat (nat_lit 155130096844800))]
theorem block033_data_flat131_step : block033_data_flat131 = (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) := by decide +kernel
theorem block033_data_flat131_original : block033_data_flat131 = (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) := by
  rw [block033_data_flat131_step]
def block033_data_flat132 : CoefficientMerge.Poly := [(nat_lit 10221, Int.ofNat (nat_lit 169971216307200))]
theorem block033_data_flat132_step : block033_data_flat132 = (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded) := by decide +kernel
theorem block033_data_flat132_original : block033_data_flat132 = (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded) := by
  rw [block033_data_flat132_step]
def block033_data_flat133 : CoefficientMerge.Poly := [(nat_lit 10220, Int.ofNat (nat_lit 155130096844800)), (nat_lit 10221, Int.ofNat (nat_lit 169971216307200))]
theorem block033_data_flat133_step : block033_data_flat133 = (CoefficientMerge.fastMerge block033_data_flat131 block033_data_flat132) := by decide +kernel
theorem block033_data_flat133_original : block033_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded)) := by
  rw [block033_data_flat133_step, block033_data_flat131_original, block033_data_flat132_original]
def block033_data_flat134 : CoefficientMerge.Poly := [(nat_lit 10219, Int.ofNat (nat_lit 14841119462400)), (nat_lit 10220, Int.ofNat (nat_lit 155130096844800)), (nat_lit 10221, Int.ofNat (nat_lit 169971216307200))]
theorem block033_data_flat134_step : block033_data_flat134 = (CoefficientMerge.fastMerge block033_data_flat130 block033_data_flat133) := by decide +kernel
theorem block033_data_flat134_original : block033_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded))) := by
  rw [block033_data_flat134_step, block033_data_flat130_original, block033_data_flat133_original]
def block033_data_flat135 : CoefficientMerge.Poly := [(nat_lit 9767, Int.ofNat (nat_lit 866434270464000)), (nat_lit 9791, Int.ofNat (nat_lit 439911553536000)), (nat_lit 10219, Int.ofNat (nat_lit 14841119462400)), (nat_lit 10220, Int.ofNat (nat_lit 155130096844800)), (nat_lit 10221, Int.ofNat (nat_lit 169971216307200))]
theorem block033_data_flat135_step : block033_data_flat135 = (CoefficientMerge.fastMerge block033_data_flat129 block033_data_flat134) := by decide +kernel
theorem block033_data_flat135_original : block033_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded)))) := by
  rw [block033_data_flat135_step, block033_data_flat129_original, block033_data_flat134_original]
def block033_data_flat136 : CoefficientMerge.Poly := [(nat_lit 9719, Int.ofNat (nat_lit 804008014387200)), (nat_lit 9741, Int.ofNat (nat_lit 347502808396800)), (nat_lit 9742, Int.ofNat (nat_lit 749710418688000)), (nat_lit 9743, Int.ofNat (nat_lit 835221142425600)), (nat_lit 9766, Int.ofNat (nat_lit 375348914640000)), (nat_lit 9767, Int.ofNat (nat_lit 866434270464000)), (nat_lit 9791, Int.ofNat (nat_lit 439911553536000)), (nat_lit 10219, Int.ofNat (nat_lit 14841119462400)), (nat_lit 10220, Int.ofNat (nat_lit 155130096844800)), (nat_lit 10221, Int.ofNat (nat_lit 169971216307200))]
theorem block033_data_flat136_step : block033_data_flat136 = (CoefficientMerge.fastMerge block033_data_flat126 block033_data_flat135) := by decide +kernel
theorem block033_data_flat136_original : block033_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded))))) := by
  rw [block033_data_flat136_step, block033_data_flat126_original, block033_data_flat135_original]
def block033_data_flat137 : CoefficientMerge.Poly := [(nat_lit 10222, Int.ofNat (nat_lit 96697940774400))]
theorem block033_data_flat137_step : block033_data_flat137 = (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) := by decide +kernel
theorem block033_data_flat137_original : block033_data_flat137 = (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) := by
  rw [block033_data_flat137_step]
def block033_data_flat138 : CoefficientMerge.Poly := [(nat_lit 10223, Int.ofNat (nat_lit 229250644761600))]
theorem block033_data_flat138_step : block033_data_flat138 = (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded) := by decide +kernel
theorem block033_data_flat138_original : block033_data_flat138 = (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded) := by
  rw [block033_data_flat138_step]
def block033_data_flat139 : CoefficientMerge.Poly := [(nat_lit 10222, Int.ofNat (nat_lit 96697940774400)), (nat_lit 10223, Int.ofNat (nat_lit 229250644761600))]
theorem block033_data_flat139_step : block033_data_flat139 = (CoefficientMerge.fastMerge block033_data_flat137 block033_data_flat138) := by decide +kernel
theorem block033_data_flat139_original : block033_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded)) := by
  rw [block033_data_flat139_step, block033_data_flat137_original, block033_data_flat138_original]
def block033_data_flat140 : CoefficientMerge.Poly := [(nat_lit 10242, Int.ofNat (nat_lit 21474972288000))]
theorem block033_data_flat140_step : block033_data_flat140 = (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) := by decide +kernel
theorem block033_data_flat140_original : block033_data_flat140 = (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) := by
  rw [block033_data_flat140_step]
def block033_data_flat141 : CoefficientMerge.Poly := [(nat_lit 10243, Int.ofNat (nat_lit 121790733926400))]
theorem block033_data_flat141_step : block033_data_flat141 = (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) := by decide +kernel
theorem block033_data_flat141_original : block033_data_flat141 = (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) := by
  rw [block033_data_flat141_step]
def block033_data_flat142 : CoefficientMerge.Poly := [(nat_lit 10244, Int.ofNat (nat_lit 482315120179200))]
theorem block033_data_flat142_step : block033_data_flat142 = (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded) := by decide +kernel
theorem block033_data_flat142_original : block033_data_flat142 = (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded) := by
  rw [block033_data_flat142_step]
def block033_data_flat143 : CoefficientMerge.Poly := [(nat_lit 10243, Int.ofNat (nat_lit 121790733926400)), (nat_lit 10244, Int.ofNat (nat_lit 482315120179200))]
theorem block033_data_flat143_step : block033_data_flat143 = (CoefficientMerge.fastMerge block033_data_flat141 block033_data_flat142) := by decide +kernel
theorem block033_data_flat143_original : block033_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded)) := by
  rw [block033_data_flat143_step, block033_data_flat141_original, block033_data_flat142_original]
def block033_data_flat144 : CoefficientMerge.Poly := [(nat_lit 10242, Int.ofNat (nat_lit 21474972288000)), (nat_lit 10243, Int.ofNat (nat_lit 121790733926400)), (nat_lit 10244, Int.ofNat (nat_lit 482315120179200))]
theorem block033_data_flat144_step : block033_data_flat144 = (CoefficientMerge.fastMerge block033_data_flat140 block033_data_flat143) := by decide +kernel
theorem block033_data_flat144_original : block033_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded))) := by
  rw [block033_data_flat144_step, block033_data_flat140_original, block033_data_flat143_original]
def block033_data_flat145 : CoefficientMerge.Poly := [(nat_lit 10222, Int.ofNat (nat_lit 96697940774400)), (nat_lit 10223, Int.ofNat (nat_lit 229250644761600)), (nat_lit 10242, Int.ofNat (nat_lit 21474972288000)), (nat_lit 10243, Int.ofNat (nat_lit 121790733926400)), (nat_lit 10244, Int.ofNat (nat_lit 482315120179200))]
theorem block033_data_flat145_step : block033_data_flat145 = (CoefficientMerge.fastMerge block033_data_flat139 block033_data_flat144) := by decide +kernel
theorem block033_data_flat145_original : block033_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded)))) := by
  rw [block033_data_flat145_step, block033_data_flat139_original, block033_data_flat144_original]
def block033_data_flat146 : CoefficientMerge.Poly := [(nat_lit 10245, Int.ofNat (nat_lit 561155909529600))]
theorem block033_data_flat146_step : block033_data_flat146 = (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) := by decide +kernel
theorem block033_data_flat146_original : block033_data_flat146 = (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) := by
  rw [block033_data_flat146_step]
def block033_data_flat147 : CoefficientMerge.Poly := [(nat_lit 10246, Int.ofNat (nat_lit 434170719360000))]
theorem block033_data_flat147_step : block033_data_flat147 = (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded) := by decide +kernel
theorem block033_data_flat147_original : block033_data_flat147 = (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded) := by
  rw [block033_data_flat147_step]
def block033_data_flat148 : CoefficientMerge.Poly := [(nat_lit 10245, Int.ofNat (nat_lit 561155909529600)), (nat_lit 10246, Int.ofNat (nat_lit 434170719360000))]
theorem block033_data_flat148_step : block033_data_flat148 = (CoefficientMerge.fastMerge block033_data_flat146 block033_data_flat147) := by decide +kernel
theorem block033_data_flat148_original : block033_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded)) := by
  rw [block033_data_flat148_step, block033_data_flat146_original, block033_data_flat147_original]
def block033_data_flat149 : CoefficientMerge.Poly := [(nat_lit 10247, Int.ofNat (nat_lit 779222558822400))]
theorem block033_data_flat149_step : block033_data_flat149 = (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) := by decide +kernel
theorem block033_data_flat149_original : block033_data_flat149 = (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) := by
  rw [block033_data_flat149_step]
def block033_data_flat150 : CoefficientMerge.Poly := [(nat_lit 10267, Int.ofNat (nat_lit 54618721597440))]
theorem block033_data_flat150_step : block033_data_flat150 = (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) := by decide +kernel
theorem block033_data_flat150_original : block033_data_flat150 = (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) := by
  rw [block033_data_flat150_step]
def block033_data_flat151 : CoefficientMerge.Poly := [(nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
theorem block033_data_flat151_step : block033_data_flat151 = (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded) := by decide +kernel
theorem block033_data_flat151_original : block033_data_flat151 = (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded) := by
  rw [block033_data_flat151_step]
def block033_data_flat152 : CoefficientMerge.Poly := [(nat_lit 10267, Int.ofNat (nat_lit 54618721597440)), (nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
theorem block033_data_flat152_step : block033_data_flat152 = (CoefficientMerge.fastMerge block033_data_flat150 block033_data_flat151) := by decide +kernel
theorem block033_data_flat152_original : block033_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded)) := by
  rw [block033_data_flat152_step, block033_data_flat150_original, block033_data_flat151_original]
def block033_data_flat153 : CoefficientMerge.Poly := [(nat_lit 10247, Int.ofNat (nat_lit 779222558822400)), (nat_lit 10267, Int.ofNat (nat_lit 54618721597440)), (nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
theorem block033_data_flat153_step : block033_data_flat153 = (CoefficientMerge.fastMerge block033_data_flat149 block033_data_flat152) := by decide +kernel
theorem block033_data_flat153_original : block033_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded))) := by
  rw [block033_data_flat153_step, block033_data_flat149_original, block033_data_flat152_original]
def block033_data_flat154 : CoefficientMerge.Poly := [(nat_lit 10245, Int.ofNat (nat_lit 561155909529600)), (nat_lit 10246, Int.ofNat (nat_lit 434170719360000)), (nat_lit 10247, Int.ofNat (nat_lit 779222558822400)), (nat_lit 10267, Int.ofNat (nat_lit 54618721597440)), (nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
theorem block033_data_flat154_step : block033_data_flat154 = (CoefficientMerge.fastMerge block033_data_flat148 block033_data_flat153) := by decide +kernel
theorem block033_data_flat154_original : block033_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded)))) := by
  rw [block033_data_flat154_step, block033_data_flat148_original, block033_data_flat153_original]
def block033_data_flat155 : CoefficientMerge.Poly := [(nat_lit 10222, Int.ofNat (nat_lit 96697940774400)), (nat_lit 10223, Int.ofNat (nat_lit 229250644761600)), (nat_lit 10242, Int.ofNat (nat_lit 21474972288000)), (nat_lit 10243, Int.ofNat (nat_lit 121790733926400)), (nat_lit 10244, Int.ofNat (nat_lit 482315120179200)), (nat_lit 10245, Int.ofNat (nat_lit 561155909529600)), (nat_lit 10246, Int.ofNat (nat_lit 434170719360000)), (nat_lit 10247, Int.ofNat (nat_lit 779222558822400)), (nat_lit 10267, Int.ofNat (nat_lit 54618721597440)), (nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
theorem block033_data_flat155_step : block033_data_flat155 = (CoefficientMerge.fastMerge block033_data_flat145 block033_data_flat154) := by decide +kernel
theorem block033_data_flat155_original : block033_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded))))) := by
  rw [block033_data_flat155_step, block033_data_flat145_original, block033_data_flat154_original]
def block033_data_flat156 : CoefficientMerge.Poly := [(nat_lit 9719, Int.ofNat (nat_lit 804008014387200)), (nat_lit 9741, Int.ofNat (nat_lit 347502808396800)), (nat_lit 9742, Int.ofNat (nat_lit 749710418688000)), (nat_lit 9743, Int.ofNat (nat_lit 835221142425600)), (nat_lit 9766, Int.ofNat (nat_lit 375348914640000)), (nat_lit 9767, Int.ofNat (nat_lit 866434270464000)), (nat_lit 9791, Int.ofNat (nat_lit 439911553536000)), (nat_lit 10219, Int.ofNat (nat_lit 14841119462400)), (nat_lit 10220, Int.ofNat (nat_lit 155130096844800)), (nat_lit 10221, Int.ofNat (nat_lit 169971216307200)), (nat_lit 10222, Int.ofNat (nat_lit 96697940774400)), (nat_lit 10223, Int.ofNat (nat_lit 229250644761600)), (nat_lit 10242, Int.ofNat (nat_lit 21474972288000)), (nat_lit 10243, Int.ofNat (nat_lit 121790733926400)), (nat_lit 10244, Int.ofNat (nat_lit 482315120179200)), (nat_lit 10245, Int.ofNat (nat_lit 561155909529600)), (nat_lit 10246, Int.ofNat (nat_lit 434170719360000)), (nat_lit 10247, Int.ofNat (nat_lit 779222558822400)), (nat_lit 10267, Int.ofNat (nat_lit 54618721597440)), (nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
theorem block033_data_flat156_step : block033_data_flat156 = (CoefficientMerge.fastMerge block033_data_flat136 block033_data_flat155) := by decide +kernel
theorem block033_data_flat156_original : block033_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded)))))) := by
  rw [block033_data_flat156_step, block033_data_flat136_original, block033_data_flat155_original]
def block033_data_flat157 : CoefficientMerge.Poly := [(nat_lit 9641, Int.ofNat (nat_lit 2395557964800)), (nat_lit 9643, Int.ofNat (nat_lit 9886777420800)), (nat_lit 9644, Int.ofNat (nat_lit 292154122444800)), (nat_lit 9645, Int.ofNat (nat_lit 317089058764800)), (nat_lit 9646, Int.ofNat (nat_lit 188403739776000)), (nat_lit 9647, Int.ofNat (nat_lit 477770776358400)), (nat_lit 9666, Int.ofNat (nat_lit 41516346816000)), (nat_lit 9667, Int.ofNat (nat_lit 149668894771200)), (nat_lit 9668, Int.ofNat (nat_lit 497988692812800)), (nat_lit 9669, Int.ofNat (nat_lit 564624893952000)), (nat_lit 9670, Int.ofNat (nat_lit 426558798489600)), (nat_lit 9671, Int.ofNat (nat_lit 759406049740800)), (nat_lit 9691, Int.ofNat (nat_lit 65538548490240)), (nat_lit 9692, Int.ofNat (nat_lit 477151590988800)), (nat_lit 9693, Int.ofNat (nat_lit 631558767974400)), (nat_lit 9694, Int.ofNat (nat_lit 581263648358400)), (nat_lit 9695, Int.ofNat (nat_lit 790619177779200)), (nat_lit 9716, Int.ofNat (nat_lit 368999043033600)), (nat_lit 9717, Int.ofNat (nat_lit 768913541222400)), (nat_lit 9718, Int.ofNat (nat_lit 735847367270400)), (nat_lit 9719, Int.ofNat (nat_lit 804008014387200)), (nat_lit 9741, Int.ofNat (nat_lit 347502808396800)), (nat_lit 9742, Int.ofNat (nat_lit 749710418688000)), (nat_lit 9743, Int.ofNat (nat_lit 835221142425600)), (nat_lit 9766, Int.ofNat (nat_lit 375348914640000)), (nat_lit 9767, Int.ofNat (nat_lit 866434270464000)), (nat_lit 9791, Int.ofNat (nat_lit 439911553536000)), (nat_lit 10219, Int.ofNat (nat_lit 14841119462400)), (nat_lit 10220, Int.ofNat (nat_lit 155130096844800)), (nat_lit 10221, Int.ofNat (nat_lit 169971216307200)), (nat_lit 10222, Int.ofNat (nat_lit 96697940774400)), (nat_lit 10223, Int.ofNat (nat_lit 229250644761600)), (nat_lit 10242, Int.ofNat (nat_lit 21474972288000)), (nat_lit 10243, Int.ofNat (nat_lit 121790733926400)), (nat_lit 10244, Int.ofNat (nat_lit 482315120179200)), (nat_lit 10245, Int.ofNat (nat_lit 561155909529600)), (nat_lit 10246, Int.ofNat (nat_lit 434170719360000)), (nat_lit 10247, Int.ofNat (nat_lit 779222558822400)), (nat_lit 10267, Int.ofNat (nat_lit 54618721597440)), (nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
theorem block033_data_flat157_step : block033_data_flat157 = (CoefficientMerge.fastMerge block033_data_flat117 block033_data_flat156) := by decide +kernel
theorem block033_data_flat157_original : block033_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded))))))) := by
  rw [block033_data_flat157_step, block033_data_flat117_original, block033_data_flat156_original]
def block033_data_flat158 : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 65163300249600)), (nat_lit 9023, Int.ofNat (nat_lit 5211208396800)), (nat_lit 9042, Int.ofNat (nat_lit 24896019778560)), (nat_lit 9044, Int.ofNat (nat_lit 233856198374400)), (nat_lit 9045, Int.ofNat (nat_lit 220828821696000)), (nat_lit 9046, Int.ofNat (nat_lit 99469520156160)), (nat_lit 9047, Int.ofNat (nat_lit 259121345414400)), (nat_lit 9065, Int.ofNat (nat_lit 8561639116800)), (nat_lit 9066, Int.ofNat (nat_lit 35057102976000)), (nat_lit 9067, Int.ofNat (nat_lit 40411348992000)), (nat_lit 9068, Int.ofNat (nat_lit 327449191910400)), (nat_lit 9069, Int.ofNat (nat_lit 349177379443200)), (nat_lit 9070, Int.ofNat (nat_lit 284381337945600)), (nat_lit 9071, Int.ofNat (nat_lit 503972755372800)), (nat_lit 9090, Int.ofNat (nat_lit 71490459801600)), (nat_lit 9091, Int.ofNat (nat_lit 197412532531200)), (nat_lit 9092, Int.ofNat (nat_lit 533527742361600)), (nat_lit 9093, Int.ofNat (nat_lit 587959355289600)), (nat_lit 9094, Int.ofNat (nat_lit 457214273107200)), (nat_lit 9095, Int.ofNat (nat_lit 739589540659200)), (nat_lit 9115, Int.ofNat (nat_lit 86391113840640)), (nat_lit 9116, Int.ofNat (nat_lit 505631540736000)), (nat_lit 9117, Int.ofNat (nat_lit 646813536768000)), (nat_lit 9118, Int.ofNat (nat_lit 564551442201600)), (nat_lit 9119, Int.ofNat (nat_lit 760681790668800)), (nat_lit 9140, Int.ofNat (nat_lit 379709468006400)), (nat_lit 9141, Int.ofNat (nat_lit 776088617472000)), (nat_lit 9142, Int.ofNat (nat_lit 671767480339200)), (nat_lit 9143, Int.ofNat (nat_lit 726466161254400)), (nat_lit 9165, Int.ofNat (nat_lit 347050500249600)), (nat_lit 9166, Int.ofNat (nat_lit 657396548726400)), (nat_lit 9167, Int.ofNat (nat_lit 747558411264000)), (nat_lit 9190, Int.ofNat (nat_lit 276807592656000)), (nat_lit 9191, Int.ofNat (nat_lit 682549021425600)), (nat_lit 9215, Int.ofNat (nat_lit 367217515929600)), (nat_lit 9616, Int.ofNat (nat_lit 1027680192000)), (nat_lit 9618, Int.ofNat (nat_lit 7461795801600)), (nat_lit 9620, Int.ofNat (nat_lit 109950182899200)), (nat_lit 9621, Int.ofNat (nat_lit 102488387097600)), (nat_lit 9623, Int.ofNat (nat_lit 102213909504000)), (nat_lit 9641, Int.ofNat (nat_lit 2395557964800)), (nat_lit 9643, Int.ofNat (nat_lit 9886777420800)), (nat_lit 9644, Int.ofNat (nat_lit 292154122444800)), (nat_lit 9645, Int.ofNat (nat_lit 317089058764800)), (nat_lit 9646, Int.ofNat (nat_lit 188403739776000)), (nat_lit 9647, Int.ofNat (nat_lit 477770776358400)), (nat_lit 9666, Int.ofNat (nat_lit 41516346816000)), (nat_lit 9667, Int.ofNat (nat_lit 149668894771200)), (nat_lit 9668, Int.ofNat (nat_lit 497988692812800)), (nat_lit 9669, Int.ofNat (nat_lit 564624893952000)), (nat_lit 9670, Int.ofNat (nat_lit 426558798489600)), (nat_lit 9671, Int.ofNat (nat_lit 759406049740800)), (nat_lit 9691, Int.ofNat (nat_lit 65538548490240)), (nat_lit 9692, Int.ofNat (nat_lit 477151590988800)), (nat_lit 9693, Int.ofNat (nat_lit 631558767974400)), (nat_lit 9694, Int.ofNat (nat_lit 581263648358400)), (nat_lit 9695, Int.ofNat (nat_lit 790619177779200)), (nat_lit 9716, Int.ofNat (nat_lit 368999043033600)), (nat_lit 9717, Int.ofNat (nat_lit 768913541222400)), (nat_lit 9718, Int.ofNat (nat_lit 735847367270400)), (nat_lit 9719, Int.ofNat (nat_lit 804008014387200)), (nat_lit 9741, Int.ofNat (nat_lit 347502808396800)), (nat_lit 9742, Int.ofNat (nat_lit 749710418688000)), (nat_lit 9743, Int.ofNat (nat_lit 835221142425600)), (nat_lit 9766, Int.ofNat (nat_lit 375348914640000)), (nat_lit 9767, Int.ofNat (nat_lit 866434270464000)), (nat_lit 9791, Int.ofNat (nat_lit 439911553536000)), (nat_lit 10219, Int.ofNat (nat_lit 14841119462400)), (nat_lit 10220, Int.ofNat (nat_lit 155130096844800)), (nat_lit 10221, Int.ofNat (nat_lit 169971216307200)), (nat_lit 10222, Int.ofNat (nat_lit 96697940774400)), (nat_lit 10223, Int.ofNat (nat_lit 229250644761600)), (nat_lit 10242, Int.ofNat (nat_lit 21474972288000)), (nat_lit 10243, Int.ofNat (nat_lit 121790733926400)), (nat_lit 10244, Int.ofNat (nat_lit 482315120179200)), (nat_lit 10245, Int.ofNat (nat_lit 561155909529600)), (nat_lit 10246, Int.ofNat (nat_lit 434170719360000)), (nat_lit 10247, Int.ofNat (nat_lit 779222558822400)), (nat_lit 10267, Int.ofNat (nat_lit 54618721597440)), (nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
theorem block033_data_flat158_step : block033_data_flat158 = (CoefficientMerge.fastMerge block033_data_flat078 block033_data_flat157) := by decide +kernel
theorem block033_data_flat158_original : block033_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded)))))))) := by
  rw [block033_data_flat158_step, block033_data_flat078_original, block033_data_flat157_original]
def block033_data_flat159 : CoefficientMerge.Poly := [(nat_lit 9021, Int.ofNat (nat_lit 65163300249600)), (nat_lit 9023, Int.ofNat (nat_lit 5211208396800)), (nat_lit 9042, Int.ofNat (nat_lit 24896019778560)), (nat_lit 9044, Int.ofNat (nat_lit 233856198374400)), (nat_lit 9045, Int.ofNat (nat_lit 220828821696000)), (nat_lit 9046, Int.ofNat (nat_lit 99469520156160)), (nat_lit 9047, Int.ofNat (nat_lit 259121345414400)), (nat_lit 9065, Int.ofNat (nat_lit 8561639116800)), (nat_lit 9066, Int.ofNat (nat_lit 35057102976000)), (nat_lit 9067, Int.ofNat (nat_lit 40411348992000)), (nat_lit 9068, Int.ofNat (nat_lit 327449191910400)), (nat_lit 9069, Int.ofNat (nat_lit 349177379443200)), (nat_lit 9070, Int.ofNat (nat_lit 284381337945600)), (nat_lit 9071, Int.ofNat (nat_lit 503972755372800)), (nat_lit 9090, Int.ofNat (nat_lit 71490459801600)), (nat_lit 9091, Int.ofNat (nat_lit 197412532531200)), (nat_lit 9092, Int.ofNat (nat_lit 533527742361600)), (nat_lit 9093, Int.ofNat (nat_lit 587959355289600)), (nat_lit 9094, Int.ofNat (nat_lit 457214273107200)), (nat_lit 9095, Int.ofNat (nat_lit 739589540659200)), (nat_lit 9115, Int.ofNat (nat_lit 86391113840640)), (nat_lit 9116, Int.ofNat (nat_lit 505631540736000)), (nat_lit 9117, Int.ofNat (nat_lit 646813536768000)), (nat_lit 9118, Int.ofNat (nat_lit 564551442201600)), (nat_lit 9119, Int.ofNat (nat_lit 760681790668800)), (nat_lit 9140, Int.ofNat (nat_lit 379709468006400)), (nat_lit 9141, Int.ofNat (nat_lit 776088617472000)), (nat_lit 9142, Int.ofNat (nat_lit 671767480339200)), (nat_lit 9143, Int.ofNat (nat_lit 726466161254400)), (nat_lit 9165, Int.ofNat (nat_lit 347050500249600)), (nat_lit 9166, Int.ofNat (nat_lit 657396548726400)), (nat_lit 9167, Int.ofNat (nat_lit 747558411264000)), (nat_lit 9190, Int.ofNat (nat_lit 276807592656000)), (nat_lit 9191, Int.ofNat (nat_lit 682549021425600)), (nat_lit 9215, Int.ofNat (nat_lit 367217515929600)), (nat_lit 9616, Int.ofNat (nat_lit 1027680192000)), (nat_lit 9618, Int.ofNat (nat_lit 7461795801600)), (nat_lit 9620, Int.ofNat (nat_lit 109950182899200)), (nat_lit 9621, Int.ofNat (nat_lit 102488387097600)), (nat_lit 9623, Int.ofNat (nat_lit 102213909504000)), (nat_lit 9641, Int.ofNat (nat_lit 2395557964800)), (nat_lit 9643, Int.ofNat (nat_lit 9886777420800)), (nat_lit 9644, Int.ofNat (nat_lit 292154122444800)), (nat_lit 9645, Int.ofNat (nat_lit 317089058764800)), (nat_lit 9646, Int.ofNat (nat_lit 188403739776000)), (nat_lit 9647, Int.ofNat (nat_lit 477770776358400)), (nat_lit 9666, Int.ofNat (nat_lit 41516346816000)), (nat_lit 9667, Int.ofNat (nat_lit 149668894771200)), (nat_lit 9668, Int.ofNat (nat_lit 497988692812800)), (nat_lit 9669, Int.ofNat (nat_lit 564624893952000)), (nat_lit 9670, Int.ofNat (nat_lit 426558798489600)), (nat_lit 9671, Int.ofNat (nat_lit 759406049740800)), (nat_lit 9691, Int.ofNat (nat_lit 65538548490240)), (nat_lit 9692, Int.ofNat (nat_lit 477151590988800)), (nat_lit 9693, Int.ofNat (nat_lit 631558767974400)), (nat_lit 9694, Int.ofNat (nat_lit 581263648358400)), (nat_lit 9695, Int.ofNat (nat_lit 790619177779200)), (nat_lit 9716, Int.ofNat (nat_lit 368999043033600)), (nat_lit 9717, Int.ofNat (nat_lit 768913541222400)), (nat_lit 9718, Int.ofNat (nat_lit 735847367270400)), (nat_lit 9719, Int.ofNat (nat_lit 804008014387200)), (nat_lit 9741, Int.ofNat (nat_lit 347502808396800)), (nat_lit 9742, Int.ofNat (nat_lit 749710418688000)), (nat_lit 9743, Int.ofNat (nat_lit 835221142425600)), (nat_lit 9766, Int.ofNat (nat_lit 375348914640000)), (nat_lit 9767, Int.ofNat (nat_lit 866434270464000)), (nat_lit 9791, Int.ofNat (nat_lit 439911553536000)), (nat_lit 10219, Int.ofNat (nat_lit 14841119462400)), (nat_lit 10220, Int.ofNat (nat_lit 155130096844800)), (nat_lit 10221, Int.ofNat (nat_lit 169971216307200)), (nat_lit 10222, Int.ofNat (nat_lit 96697940774400)), (nat_lit 10223, Int.ofNat (nat_lit 229250644761600)), (nat_lit 10242, Int.ofNat (nat_lit 21474972288000)), (nat_lit 10243, Int.ofNat (nat_lit 121790733926400)), (nat_lit 10244, Int.ofNat (nat_lit 482315120179200)), (nat_lit 10245, Int.ofNat (nat_lit 561155909529600)), (nat_lit 10246, Int.ofNat (nat_lit 434170719360000)), (nat_lit 10247, Int.ofNat (nat_lit 779222558822400)), (nat_lit 10267, Int.ofNat (nat_lit 54618721597440)), (nat_lit 10268, Int.ofNat (nat_lit 468537118156800))]
theorem block033_data_flat159_step : block033_data_flat159 = (CoefficientMerge.trim block033_data_flat158) := by decide +kernel
theorem block033_data_flat159_original : block033_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded))))))))) := by
  rw [block033_data_flat159_step, block033_data_flat158_original]
theorem block033_data : block033 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded)))))))) := by
  have h : block033 = block033_data_flat159 := by decide +kernel
  exact h.trans block033_data_flat159_original
theorem block033_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block033 := by
  rw [block033_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2449Coded_nonneg g hg hA hB) (atom2450Coded_nonneg g hg hA hB)) (add_nonneg (atom2451Coded_nonneg g hg hA hB) (add_nonneg (atom2452Coded_nonneg g hg hA hB) (atom2453Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2454Coded_nonneg g hg hA hB) (atom2455Coded_nonneg g hg hA hB)) (add_nonneg (atom2456Coded_nonneg g hg hA hB) (add_nonneg (atom2457Coded_nonneg g hg hA hB) (atom2458Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2459Coded_nonneg g hg hA hB) (atom2460Coded_nonneg g hg hA hB)) (add_nonneg (atom2461Coded_nonneg g hg hA hB) (add_nonneg (atom2462Coded_nonneg g hg hA hB) (atom2463Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2464Coded_nonneg g hg hA hB) (atom2465Coded_nonneg g hg hA hB)) (add_nonneg (atom2466Coded_nonneg g hg hA hB) (add_nonneg (atom2467Coded_nonneg g hg hA hB) (atom2468Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2469Coded_nonneg g hg hA hB) (atom2470Coded_nonneg g hg hA hB)) (add_nonneg (atom2471Coded_nonneg g hg hA hB) (add_nonneg (atom2472Coded_nonneg g hg hA hB) (atom2473Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2474Coded_nonneg g hg hA hB) (atom2475Coded_nonneg g hg hA hB)) (add_nonneg (atom2476Coded_nonneg g hg hA hB) (add_nonneg (atom2477Coded_nonneg g hg hA hB) (atom2478Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2479Coded_nonneg g hg hA hB) (atom2480Coded_nonneg g hg hA hB)) (add_nonneg (atom2481Coded_nonneg g hg hA hB) (add_nonneg (atom2482Coded_nonneg g hg hA hB) (atom2483Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2484Coded_nonneg g hg hA hB) (atom2485Coded_nonneg g hg hA hB)) (add_nonneg (atom2486Coded_nonneg g hg hA hB) (add_nonneg (atom2487Coded_nonneg g hg hA hB) (atom2488Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2489Coded_nonneg g hg hA hB) (atom2490Coded_nonneg g hg hA hB)) (add_nonneg (atom2491Coded_nonneg g hg hA hB) (add_nonneg (atom2492Coded_nonneg g hg hA hB) (atom2493Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2494Coded_nonneg g hg hA hB) (atom2495Coded_nonneg g hg hA hB)) (add_nonneg (atom2496Coded_nonneg g hg hA hB) (add_nonneg (atom2497Coded_nonneg g hg hA hB) (atom2498Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2499Coded_nonneg g hg hA hB) (atom2500Coded_nonneg g hg hA hB)) (add_nonneg (atom2501Coded_nonneg g hg hA hB) (add_nonneg (atom2502Coded_nonneg g hg hA hB) (atom2503Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2504Coded_nonneg g hg hA hB) (atom2505Coded_nonneg g hg hA hB)) (add_nonneg (atom2506Coded_nonneg g hg hA hB) (add_nonneg (atom2507Coded_nonneg g hg hA hB) (atom2508Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2509Coded_nonneg g hg hA hB) (atom2510Coded_nonneg g hg hA hB)) (add_nonneg (atom2511Coded_nonneg g hg hA hB) (add_nonneg (atom2512Coded_nonneg g hg hA hB) (atom2513Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2514Coded_nonneg g hg hA hB) (atom2515Coded_nonneg g hg hA hB)) (add_nonneg (atom2516Coded_nonneg g hg hA hB) (add_nonneg (atom2517Coded_nonneg g hg hA hB) (atom2518Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2519Coded_nonneg g hg hA hB) (atom2520Coded_nonneg g hg hA hB)) (add_nonneg (atom2521Coded_nonneg g hg hA hB) (add_nonneg (atom2522Coded_nonneg g hg hA hB) (atom2523Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2524Coded_nonneg g hg hA hB) (atom2525Coded_nonneg g hg hA hB)) (add_nonneg (atom2526Coded_nonneg g hg hA hB) (add_nonneg (atom2527Coded_nonneg g hg hA hB) (atom2528Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
