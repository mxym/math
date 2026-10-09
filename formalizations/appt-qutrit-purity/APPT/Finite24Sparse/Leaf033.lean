import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom2449 : SparsePolynomial.Poly := [([15,15,21], 1)]
theorem eval_atom2449 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2449 = ((g 15) * (g 15) * (g 21)) := by
  norm_num [atom2449, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2449_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65163300249600 : Int) atom2449) := by
  rw [SparsePolynomial.eval_scale, eval_atom2449]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2449Coded : CoefficientMerge.Poly := [(9021, 1)]
theorem atom2449Coded_decode : atom2449 = SparsePolynomial.decodeCubic 24 atom2449Coded := by decide +kernel
theorem atom2449Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) := by
  have h := atom2449_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2449Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2450 : SparsePolynomial.Poly := [([15,15,23], 1)]
theorem eval_atom2450 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2450 = ((g 15) * (g 15) * (g 23)) := by
  norm_num [atom2450, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2450_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5211208396800 : Int) atom2450) := by
  rw [SparsePolynomial.eval_scale, eval_atom2450]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2450Coded : CoefficientMerge.Poly := [(9023, 1)]
theorem atom2450Coded_decode : atom2450 = SparsePolynomial.decodeCubic 24 atom2450Coded := by decide +kernel
theorem atom2450Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded) := by
  have h := atom2450_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2450Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2451 : SparsePolynomial.Poly := [([15,16,18], 1)]
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
def atom2451Coded : CoefficientMerge.Poly := [(9042, 1)]
theorem atom2451Coded_decode : atom2451 = SparsePolynomial.decodeCubic 24 atom2451Coded := by decide +kernel
theorem atom2451Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) := by
  have h := atom2451_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2451Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2452 : SparsePolynomial.Poly := [([15,16,20], 1)]
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
def atom2452Coded : CoefficientMerge.Poly := [(9044, 1)]
theorem atom2452Coded_decode : atom2452 = SparsePolynomial.decodeCubic 24 atom2452Coded := by decide +kernel
theorem atom2452Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) := by
  have h := atom2452_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2452Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2453 : SparsePolynomial.Poly := [([15,16,21], 1)]
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
def atom2453Coded : CoefficientMerge.Poly := [(9045, 1)]
theorem atom2453Coded_decode : atom2453 = SparsePolynomial.decodeCubic 24 atom2453Coded := by decide +kernel
theorem atom2453Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded) := by
  have h := atom2453_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2453Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2454 : SparsePolynomial.Poly := [([15,16,22], 1)]
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
def atom2454Coded : CoefficientMerge.Poly := [(9046, 1)]
theorem atom2454Coded_decode : atom2454 = SparsePolynomial.decodeCubic 24 atom2454Coded := by decide +kernel
theorem atom2454Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) := by
  have h := atom2454_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2454Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2455 : SparsePolynomial.Poly := [([15,16,23], 1)]
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
def atom2455Coded : CoefficientMerge.Poly := [(9047, 1)]
theorem atom2455Coded_decode : atom2455 = SparsePolynomial.decodeCubic 24 atom2455Coded := by decide +kernel
theorem atom2455Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded) := by
  have h := atom2455_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2455Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2456 : SparsePolynomial.Poly := [([15,17,17], 1)]
theorem eval_atom2456 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2456 = ((g 15) * (g 17) * (g 17)) := by
  norm_num [atom2456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2456_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8561639116800 : Int) atom2456) := by
  rw [SparsePolynomial.eval_scale, eval_atom2456]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2456Coded : CoefficientMerge.Poly := [(9065, 1)]
theorem atom2456Coded_decode : atom2456 = SparsePolynomial.decodeCubic 24 atom2456Coded := by decide +kernel
theorem atom2456Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) := by
  have h := atom2456_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2456Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2457 : SparsePolynomial.Poly := [([15,17,18], 1)]
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
def atom2457Coded : CoefficientMerge.Poly := [(9066, 1)]
theorem atom2457Coded_decode : atom2457 = SparsePolynomial.decodeCubic 24 atom2457Coded := by decide +kernel
theorem atom2457Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) := by
  have h := atom2457_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2457Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2458 : SparsePolynomial.Poly := [([15,17,19], 1)]
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
def atom2458Coded : CoefficientMerge.Poly := [(9067, 1)]
theorem atom2458Coded_decode : atom2458 = SparsePolynomial.decodeCubic 24 atom2458Coded := by decide +kernel
theorem atom2458Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded) := by
  have h := atom2458_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2458Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2459 : SparsePolynomial.Poly := [([15,17,20], 1)]
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
def atom2459Coded : CoefficientMerge.Poly := [(9068, 1)]
theorem atom2459Coded_decode : atom2459 = SparsePolynomial.decodeCubic 24 atom2459Coded := by decide +kernel
theorem atom2459Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) := by
  have h := atom2459_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2459Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2460 : SparsePolynomial.Poly := [([15,17,21], 1)]
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
def atom2460Coded : CoefficientMerge.Poly := [(9069, 1)]
theorem atom2460Coded_decode : atom2460 = SparsePolynomial.decodeCubic 24 atom2460Coded := by decide +kernel
theorem atom2460Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded) := by
  have h := atom2460_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2460Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2461 : SparsePolynomial.Poly := [([15,17,22], 1)]
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
def atom2461Coded : CoefficientMerge.Poly := [(9070, 1)]
theorem atom2461Coded_decode : atom2461 = SparsePolynomial.decodeCubic 24 atom2461Coded := by decide +kernel
theorem atom2461Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) := by
  have h := atom2461_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2461Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2462 : SparsePolynomial.Poly := [([15,17,23], 1)]
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
def atom2462Coded : CoefficientMerge.Poly := [(9071, 1)]
theorem atom2462Coded_decode : atom2462 = SparsePolynomial.decodeCubic 24 atom2462Coded := by decide +kernel
theorem atom2462Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) := by
  have h := atom2462_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2462Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2463 : SparsePolynomial.Poly := [([15,18,18], 1)]
theorem eval_atom2463 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2463 = ((g 15) * (g 18) * (g 18)) := by
  norm_num [atom2463, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2463_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71490459801600 : Int) atom2463) := by
  rw [SparsePolynomial.eval_scale, eval_atom2463]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 15) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2463Coded : CoefficientMerge.Poly := [(9090, 1)]
theorem atom2463Coded_decode : atom2463 = SparsePolynomial.decodeCubic 24 atom2463Coded := by decide +kernel
theorem atom2463Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded) := by
  have h := atom2463_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2463Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2464 : SparsePolynomial.Poly := [([15,18,19], 1)]
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
def atom2464Coded : CoefficientMerge.Poly := [(9091, 1)]
theorem atom2464Coded_decode : atom2464 = SparsePolynomial.decodeCubic 24 atom2464Coded := by decide +kernel
theorem atom2464Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) := by
  have h := atom2464_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2464Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2465 : SparsePolynomial.Poly := [([15,18,20], 1)]
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
def atom2465Coded : CoefficientMerge.Poly := [(9092, 1)]
theorem atom2465Coded_decode : atom2465 = SparsePolynomial.decodeCubic 24 atom2465Coded := by decide +kernel
theorem atom2465Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded) := by
  have h := atom2465_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2465Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2466 : SparsePolynomial.Poly := [([15,18,21], 1)]
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
def atom2466Coded : CoefficientMerge.Poly := [(9093, 1)]
theorem atom2466Coded_decode : atom2466 = SparsePolynomial.decodeCubic 24 atom2466Coded := by decide +kernel
theorem atom2466Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) := by
  have h := atom2466_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2466Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2467 : SparsePolynomial.Poly := [([15,18,22], 1)]
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
def atom2467Coded : CoefficientMerge.Poly := [(9094, 1)]
theorem atom2467Coded_decode : atom2467 = SparsePolynomial.decodeCubic 24 atom2467Coded := by decide +kernel
theorem atom2467Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) := by
  have h := atom2467_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2467Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2468 : SparsePolynomial.Poly := [([15,18,23], 1)]
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
def atom2468Coded : CoefficientMerge.Poly := [(9095, 1)]
theorem atom2468Coded_decode : atom2468 = SparsePolynomial.decodeCubic 24 atom2468Coded := by decide +kernel
theorem atom2468Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded) := by
  have h := atom2468_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2468Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2469 : SparsePolynomial.Poly := [([15,19,19], 1)]
theorem eval_atom2469 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2469 = ((g 15) * (g 19) * (g 19)) := by
  norm_num [atom2469, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2469_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86391113840640 : Int) atom2469) := by
  rw [SparsePolynomial.eval_scale, eval_atom2469]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 15) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2469Coded : CoefficientMerge.Poly := [(9115, 1)]
theorem atom2469Coded_decode : atom2469 = SparsePolynomial.decodeCubic 24 atom2469Coded := by decide +kernel
theorem atom2469Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) := by
  have h := atom2469_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2469Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2470 : SparsePolynomial.Poly := [([15,19,20], 1)]
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
def atom2470Coded : CoefficientMerge.Poly := [(9116, 1)]
theorem atom2470Coded_decode : atom2470 = SparsePolynomial.decodeCubic 24 atom2470Coded := by decide +kernel
theorem atom2470Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded) := by
  have h := atom2470_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2470Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2471 : SparsePolynomial.Poly := [([15,19,21], 1)]
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
def atom2471Coded : CoefficientMerge.Poly := [(9117, 1)]
theorem atom2471Coded_decode : atom2471 = SparsePolynomial.decodeCubic 24 atom2471Coded := by decide +kernel
theorem atom2471Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) := by
  have h := atom2471_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2471Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2472 : SparsePolynomial.Poly := [([15,19,22], 1)]
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
def atom2472Coded : CoefficientMerge.Poly := [(9118, 1)]
theorem atom2472Coded_decode : atom2472 = SparsePolynomial.decodeCubic 24 atom2472Coded := by decide +kernel
theorem atom2472Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) := by
  have h := atom2472_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2472Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2473 : SparsePolynomial.Poly := [([15,19,23], 1)]
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
def atom2473Coded : CoefficientMerge.Poly := [(9119, 1)]
theorem atom2473Coded_decode : atom2473 = SparsePolynomial.decodeCubic 24 atom2473Coded := by decide +kernel
theorem atom2473Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded) := by
  have h := atom2473_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2473Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2474 : SparsePolynomial.Poly := [([15,20,20], 1)]
theorem eval_atom2474 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2474 = ((g 15) * (g 20) * (g 20)) := by
  norm_num [atom2474, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2474_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379709468006400 : Int) atom2474) := by
  rw [SparsePolynomial.eval_scale, eval_atom2474]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 15) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2474Coded : CoefficientMerge.Poly := [(9140, 1)]
theorem atom2474Coded_decode : atom2474 = SparsePolynomial.decodeCubic 24 atom2474Coded := by decide +kernel
theorem atom2474Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) := by
  have h := atom2474_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2474Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2475 : SparsePolynomial.Poly := [([15,20,21], 1)]
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
def atom2475Coded : CoefficientMerge.Poly := [(9141, 1)]
theorem atom2475Coded_decode : atom2475 = SparsePolynomial.decodeCubic 24 atom2475Coded := by decide +kernel
theorem atom2475Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded) := by
  have h := atom2475_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2475Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2476 : SparsePolynomial.Poly := [([15,20,22], 1)]
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
def atom2476Coded : CoefficientMerge.Poly := [(9142, 1)]
theorem atom2476Coded_decode : atom2476 = SparsePolynomial.decodeCubic 24 atom2476Coded := by decide +kernel
theorem atom2476Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) := by
  have h := atom2476_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2476Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2477 : SparsePolynomial.Poly := [([15,20,23], 1)]
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
def atom2477Coded : CoefficientMerge.Poly := [(9143, 1)]
theorem atom2477Coded_decode : atom2477 = SparsePolynomial.decodeCubic 24 atom2477Coded := by decide +kernel
theorem atom2477Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) := by
  have h := atom2477_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2477Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2478 : SparsePolynomial.Poly := [([15,21,21], 1)]
theorem eval_atom2478 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2478 = ((g 15) * (g 21) * (g 21)) := by
  norm_num [atom2478, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2478_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347050500249600 : Int) atom2478) := by
  rw [SparsePolynomial.eval_scale, eval_atom2478]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 15) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2478Coded : CoefficientMerge.Poly := [(9165, 1)]
theorem atom2478Coded_decode : atom2478 = SparsePolynomial.decodeCubic 24 atom2478Coded := by decide +kernel
theorem atom2478Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded) := by
  have h := atom2478_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2478Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2479 : SparsePolynomial.Poly := [([15,21,22], 1)]
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
def atom2479Coded : CoefficientMerge.Poly := [(9166, 1)]
theorem atom2479Coded_decode : atom2479 = SparsePolynomial.decodeCubic 24 atom2479Coded := by decide +kernel
theorem atom2479Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) := by
  have h := atom2479_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2479Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2480 : SparsePolynomial.Poly := [([15,21,23], 1)]
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
def atom2480Coded : CoefficientMerge.Poly := [(9167, 1)]
theorem atom2480Coded_decode : atom2480 = SparsePolynomial.decodeCubic 24 atom2480Coded := by decide +kernel
theorem atom2480Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded) := by
  have h := atom2480_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2480Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2481 : SparsePolynomial.Poly := [([15,22,22], 1)]
theorem eval_atom2481 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2481 = ((g 15) * (g 22) * (g 22)) := by
  norm_num [atom2481, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2481_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276807592656000 : Int) atom2481) := by
  rw [SparsePolynomial.eval_scale, eval_atom2481]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 15) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2481Coded : CoefficientMerge.Poly := [(9190, 1)]
theorem atom2481Coded_decode : atom2481 = SparsePolynomial.decodeCubic 24 atom2481Coded := by decide +kernel
theorem atom2481Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) := by
  have h := atom2481_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2481Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2482 : SparsePolynomial.Poly := [([15,22,23], 1)]
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
def atom2482Coded : CoefficientMerge.Poly := [(9191, 1)]
theorem atom2482Coded_decode : atom2482 = SparsePolynomial.decodeCubic 24 atom2482Coded := by decide +kernel
theorem atom2482Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) := by
  have h := atom2482_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2482Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2483 : SparsePolynomial.Poly := [([15,23,23], 1)]
theorem eval_atom2483 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2483 = ((g 15) * (g 23) * (g 23)) := by
  norm_num [atom2483, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2483_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (367217515929600 : Int) atom2483) := by
  rw [SparsePolynomial.eval_scale, eval_atom2483]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 15) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2483Coded : CoefficientMerge.Poly := [(9215, 1)]
theorem atom2483Coded_decode : atom2483 = SparsePolynomial.decodeCubic 24 atom2483Coded := by decide +kernel
theorem atom2483Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded) := by
  have h := atom2483_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2483Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2484 : SparsePolynomial.Poly := [([16,16,16], 1)]
theorem eval_atom2484 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2484 = ((g 16) * (g 16) * (g 16)) := by
  norm_num [atom2484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2484_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1027680192000 : Int) atom2484) := by
  rw [SparsePolynomial.eval_scale, eval_atom2484]
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 16) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2484Coded : CoefficientMerge.Poly := [(9616, 1)]
theorem atom2484Coded_decode : atom2484 = SparsePolynomial.decodeCubic 24 atom2484Coded := by decide +kernel
theorem atom2484Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) := by
  have h := atom2484_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2484Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2485 : SparsePolynomial.Poly := [([16,16,18], 1)]
theorem eval_atom2485 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2485 = ((g 16) * (g 16) * (g 18)) := by
  norm_num [atom2485, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2485_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7461795801600 : Int) atom2485) := by
  rw [SparsePolynomial.eval_scale, eval_atom2485]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2485Coded : CoefficientMerge.Poly := [(9618, 1)]
theorem atom2485Coded_decode : atom2485 = SparsePolynomial.decodeCubic 24 atom2485Coded := by decide +kernel
theorem atom2485Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded) := by
  have h := atom2485_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2485Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2486 : SparsePolynomial.Poly := [([16,16,20], 1)]
theorem eval_atom2486 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2486 = ((g 16) * (g 16) * (g 20)) := by
  norm_num [atom2486, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2486_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109950182899200 : Int) atom2486) := by
  rw [SparsePolynomial.eval_scale, eval_atom2486]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2486Coded : CoefficientMerge.Poly := [(9620, 1)]
theorem atom2486Coded_decode : atom2486 = SparsePolynomial.decodeCubic 24 atom2486Coded := by decide +kernel
theorem atom2486Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) := by
  have h := atom2486_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2486Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2487 : SparsePolynomial.Poly := [([16,16,21], 1)]
theorem eval_atom2487 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2487 = ((g 16) * (g 16) * (g 21)) := by
  norm_num [atom2487, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2487_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102488387097600 : Int) atom2487) := by
  rw [SparsePolynomial.eval_scale, eval_atom2487]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2487Coded : CoefficientMerge.Poly := [(9621, 1)]
theorem atom2487Coded_decode : atom2487 = SparsePolynomial.decodeCubic 24 atom2487Coded := by decide +kernel
theorem atom2487Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) := by
  have h := atom2487_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2487Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2488 : SparsePolynomial.Poly := [([16,16,23], 1)]
theorem eval_atom2488 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2488 = ((g 16) * (g 16) * (g 23)) := by
  norm_num [atom2488, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2488_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102213909504000 : Int) atom2488) := by
  rw [SparsePolynomial.eval_scale, eval_atom2488]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2488Coded : CoefficientMerge.Poly := [(9623, 1)]
theorem atom2488Coded_decode : atom2488 = SparsePolynomial.decodeCubic 24 atom2488Coded := by decide +kernel
theorem atom2488Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded) := by
  have h := atom2488_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2488Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2489 : SparsePolynomial.Poly := [([16,17,17], 1)]
theorem eval_atom2489 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2489 = ((g 16) * (g 17) * (g 17)) := by
  norm_num [atom2489, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2489_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2395557964800 : Int) atom2489) := by
  rw [SparsePolynomial.eval_scale, eval_atom2489]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 16) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2489Coded : CoefficientMerge.Poly := [(9641, 1)]
theorem atom2489Coded_decode : atom2489 = SparsePolynomial.decodeCubic 24 atom2489Coded := by decide +kernel
theorem atom2489Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) := by
  have h := atom2489_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2489Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2490 : SparsePolynomial.Poly := [([16,17,19], 1)]
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
def atom2490Coded : CoefficientMerge.Poly := [(9643, 1)]
theorem atom2490Coded_decode : atom2490 = SparsePolynomial.decodeCubic 24 atom2490Coded := by decide +kernel
theorem atom2490Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded) := by
  have h := atom2490_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2490Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2491 : SparsePolynomial.Poly := [([16,17,20], 1)]
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
def atom2491Coded : CoefficientMerge.Poly := [(9644, 1)]
theorem atom2491Coded_decode : atom2491 = SparsePolynomial.decodeCubic 24 atom2491Coded := by decide +kernel
theorem atom2491Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) := by
  have h := atom2491_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2491Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2492 : SparsePolynomial.Poly := [([16,17,21], 1)]
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
def atom2492Coded : CoefficientMerge.Poly := [(9645, 1)]
theorem atom2492Coded_decode : atom2492 = SparsePolynomial.decodeCubic 24 atom2492Coded := by decide +kernel
theorem atom2492Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) := by
  have h := atom2492_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2492Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2493 : SparsePolynomial.Poly := [([16,17,22], 1)]
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
def atom2493Coded : CoefficientMerge.Poly := [(9646, 1)]
theorem atom2493Coded_decode : atom2493 = SparsePolynomial.decodeCubic 24 atom2493Coded := by decide +kernel
theorem atom2493Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded) := by
  have h := atom2493_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2493Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2494 : SparsePolynomial.Poly := [([16,17,23], 1)]
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
def atom2494Coded : CoefficientMerge.Poly := [(9647, 1)]
theorem atom2494Coded_decode : atom2494 = SparsePolynomial.decodeCubic 24 atom2494Coded := by decide +kernel
theorem atom2494Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) := by
  have h := atom2494_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2494Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2495 : SparsePolynomial.Poly := [([16,18,18], 1)]
theorem eval_atom2495 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2495 = ((g 16) * (g 18) * (g 18)) := by
  norm_num [atom2495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2495_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41516346816000 : Int) atom2495) := by
  rw [SparsePolynomial.eval_scale, eval_atom2495]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 16) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2495Coded : CoefficientMerge.Poly := [(9666, 1)]
theorem atom2495Coded_decode : atom2495 = SparsePolynomial.decodeCubic 24 atom2495Coded := by decide +kernel
theorem atom2495Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded) := by
  have h := atom2495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2496 : SparsePolynomial.Poly := [([16,18,19], 1)]
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
def atom2496Coded : CoefficientMerge.Poly := [(9667, 1)]
theorem atom2496Coded_decode : atom2496 = SparsePolynomial.decodeCubic 24 atom2496Coded := by decide +kernel
theorem atom2496Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) := by
  have h := atom2496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2497 : SparsePolynomial.Poly := [([16,18,20], 1)]
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
def atom2497Coded : CoefficientMerge.Poly := [(9668, 1)]
theorem atom2497Coded_decode : atom2497 = SparsePolynomial.decodeCubic 24 atom2497Coded := by decide +kernel
theorem atom2497Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) := by
  have h := atom2497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2498 : SparsePolynomial.Poly := [([16,18,21], 1)]
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
def atom2498Coded : CoefficientMerge.Poly := [(9669, 1)]
theorem atom2498Coded_decode : atom2498 = SparsePolynomial.decodeCubic 24 atom2498Coded := by decide +kernel
theorem atom2498Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded) := by
  have h := atom2498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2499 : SparsePolynomial.Poly := [([16,18,22], 1)]
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
def atom2499Coded : CoefficientMerge.Poly := [(9670, 1)]
theorem atom2499Coded_decode : atom2499 = SparsePolynomial.decodeCubic 24 atom2499Coded := by decide +kernel
theorem atom2499Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) := by
  have h := atom2499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2500 : SparsePolynomial.Poly := [([16,18,23], 1)]
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
def atom2500Coded : CoefficientMerge.Poly := [(9671, 1)]
theorem atom2500Coded_decode : atom2500 = SparsePolynomial.decodeCubic 24 atom2500Coded := by decide +kernel
theorem atom2500Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded) := by
  have h := atom2500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2501 : SparsePolynomial.Poly := [([16,19,19], 1)]
theorem eval_atom2501 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2501 = ((g 16) * (g 19) * (g 19)) := by
  norm_num [atom2501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2501_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65538548490240 : Int) atom2501) := by
  rw [SparsePolynomial.eval_scale, eval_atom2501]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 16) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2501Coded : CoefficientMerge.Poly := [(9691, 1)]
theorem atom2501Coded_decode : atom2501 = SparsePolynomial.decodeCubic 24 atom2501Coded := by decide +kernel
theorem atom2501Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) := by
  have h := atom2501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2502 : SparsePolynomial.Poly := [([16,19,20], 1)]
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
def atom2502Coded : CoefficientMerge.Poly := [(9692, 1)]
theorem atom2502Coded_decode : atom2502 = SparsePolynomial.decodeCubic 24 atom2502Coded := by decide +kernel
theorem atom2502Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) := by
  have h := atom2502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2503 : SparsePolynomial.Poly := [([16,19,21], 1)]
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
def atom2503Coded : CoefficientMerge.Poly := [(9693, 1)]
theorem atom2503Coded_decode : atom2503 = SparsePolynomial.decodeCubic 24 atom2503Coded := by decide +kernel
theorem atom2503Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded) := by
  have h := atom2503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2504 : SparsePolynomial.Poly := [([16,19,22], 1)]
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
def atom2504Coded : CoefficientMerge.Poly := [(9694, 1)]
theorem atom2504Coded_decode : atom2504 = SparsePolynomial.decodeCubic 24 atom2504Coded := by decide +kernel
theorem atom2504Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) := by
  have h := atom2504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2505 : SparsePolynomial.Poly := [([16,19,23], 1)]
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
def atom2505Coded : CoefficientMerge.Poly := [(9695, 1)]
theorem atom2505Coded_decode : atom2505 = SparsePolynomial.decodeCubic 24 atom2505Coded := by decide +kernel
theorem atom2505Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded) := by
  have h := atom2505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2506 : SparsePolynomial.Poly := [([16,20,20], 1)]
theorem eval_atom2506 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2506 = ((g 16) * (g 20) * (g 20)) := by
  norm_num [atom2506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2506_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (368999043033600 : Int) atom2506) := by
  rw [SparsePolynomial.eval_scale, eval_atom2506]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 16) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2506Coded : CoefficientMerge.Poly := [(9716, 1)]
theorem atom2506Coded_decode : atom2506 = SparsePolynomial.decodeCubic 24 atom2506Coded := by decide +kernel
theorem atom2506Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) := by
  have h := atom2506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2507 : SparsePolynomial.Poly := [([16,20,21], 1)]
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
def atom2507Coded : CoefficientMerge.Poly := [(9717, 1)]
theorem atom2507Coded_decode : atom2507 = SparsePolynomial.decodeCubic 24 atom2507Coded := by decide +kernel
theorem atom2507Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) := by
  have h := atom2507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2508 : SparsePolynomial.Poly := [([16,20,22], 1)]
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
def atom2508Coded : CoefficientMerge.Poly := [(9718, 1)]
theorem atom2508Coded_decode : atom2508 = SparsePolynomial.decodeCubic 24 atom2508Coded := by decide +kernel
theorem atom2508Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded) := by
  have h := atom2508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2509 : SparsePolynomial.Poly := [([16,20,23], 1)]
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
def atom2509Coded : CoefficientMerge.Poly := [(9719, 1)]
theorem atom2509Coded_decode : atom2509 = SparsePolynomial.decodeCubic 24 atom2509Coded := by decide +kernel
theorem atom2509Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) := by
  have h := atom2509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2510 : SparsePolynomial.Poly := [([16,21,21], 1)]
theorem eval_atom2510 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2510 = ((g 16) * (g 21) * (g 21)) := by
  norm_num [atom2510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2510_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347502808396800 : Int) atom2510) := by
  rw [SparsePolynomial.eval_scale, eval_atom2510]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 16) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2510Coded : CoefficientMerge.Poly := [(9741, 1)]
theorem atom2510Coded_decode : atom2510 = SparsePolynomial.decodeCubic 24 atom2510Coded := by decide +kernel
theorem atom2510Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded) := by
  have h := atom2510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2511 : SparsePolynomial.Poly := [([16,21,22], 1)]
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
def atom2511Coded : CoefficientMerge.Poly := [(9742, 1)]
theorem atom2511Coded_decode : atom2511 = SparsePolynomial.decodeCubic 24 atom2511Coded := by decide +kernel
theorem atom2511Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) := by
  have h := atom2511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2512 : SparsePolynomial.Poly := [([16,21,23], 1)]
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
def atom2512Coded : CoefficientMerge.Poly := [(9743, 1)]
theorem atom2512Coded_decode : atom2512 = SparsePolynomial.decodeCubic 24 atom2512Coded := by decide +kernel
theorem atom2512Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) := by
  have h := atom2512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2513 : SparsePolynomial.Poly := [([16,22,22], 1)]
theorem eval_atom2513 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2513 = ((g 16) * (g 22) * (g 22)) := by
  norm_num [atom2513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2513_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (375348914640000 : Int) atom2513) := by
  rw [SparsePolynomial.eval_scale, eval_atom2513]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 16) * (g 22) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2513Coded : CoefficientMerge.Poly := [(9766, 1)]
theorem atom2513Coded_decode : atom2513 = SparsePolynomial.decodeCubic 24 atom2513Coded := by decide +kernel
theorem atom2513Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded) := by
  have h := atom2513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2514 : SparsePolynomial.Poly := [([16,22,23], 1)]
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
def atom2514Coded : CoefficientMerge.Poly := [(9767, 1)]
theorem atom2514Coded_decode : atom2514 = SparsePolynomial.decodeCubic 24 atom2514Coded := by decide +kernel
theorem atom2514Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) := by
  have h := atom2514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2515 : SparsePolynomial.Poly := [([16,23,23], 1)]
theorem eval_atom2515 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2515 = ((g 16) * (g 23) * (g 23)) := by
  norm_num [atom2515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2515_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (439911553536000 : Int) atom2515) := by
  rw [SparsePolynomial.eval_scale, eval_atom2515]
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 16) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2515Coded : CoefficientMerge.Poly := [(9791, 1)]
theorem atom2515Coded_decode : atom2515 = SparsePolynomial.decodeCubic 24 atom2515Coded := by decide +kernel
theorem atom2515Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded) := by
  have h := atom2515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2516 : SparsePolynomial.Poly := [([17,17,19], 1)]
theorem eval_atom2516 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2516 = ((g 17) * (g 17) * (g 19)) := by
  norm_num [atom2516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2516_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14841119462400 : Int) atom2516) := by
  rw [SparsePolynomial.eval_scale, eval_atom2516]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2516Coded : CoefficientMerge.Poly := [(10219, 1)]
theorem atom2516Coded_decode : atom2516 = SparsePolynomial.decodeCubic 24 atom2516Coded := by decide +kernel
theorem atom2516Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) := by
  have h := atom2516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2517 : SparsePolynomial.Poly := [([17,17,20], 1)]
theorem eval_atom2517 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2517 = ((g 17) * (g 17) * (g 20)) := by
  norm_num [atom2517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2517_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155130096844800 : Int) atom2517) := by
  rw [SparsePolynomial.eval_scale, eval_atom2517]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 17) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2517Coded : CoefficientMerge.Poly := [(10220, 1)]
theorem atom2517Coded_decode : atom2517 = SparsePolynomial.decodeCubic 24 atom2517Coded := by decide +kernel
theorem atom2517Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) := by
  have h := atom2517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2518 : SparsePolynomial.Poly := [([17,17,21], 1)]
theorem eval_atom2518 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2518 = ((g 17) * (g 17) * (g 21)) := by
  norm_num [atom2518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2518_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (169971216307200 : Int) atom2518) := by
  rw [SparsePolynomial.eval_scale, eval_atom2518]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 17) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2518Coded : CoefficientMerge.Poly := [(10221, 1)]
theorem atom2518Coded_decode : atom2518 = SparsePolynomial.decodeCubic 24 atom2518Coded := by decide +kernel
theorem atom2518Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded) := by
  have h := atom2518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2519 : SparsePolynomial.Poly := [([17,17,22], 1)]
theorem eval_atom2519 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2519 = ((g 17) * (g 17) * (g 22)) := by
  norm_num [atom2519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2519_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96697940774400 : Int) atom2519) := by
  rw [SparsePolynomial.eval_scale, eval_atom2519]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 17) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2519Coded : CoefficientMerge.Poly := [(10222, 1)]
theorem atom2519Coded_decode : atom2519 = SparsePolynomial.decodeCubic 24 atom2519Coded := by decide +kernel
theorem atom2519Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) := by
  have h := atom2519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2520 : SparsePolynomial.Poly := [([17,17,23], 1)]
theorem eval_atom2520 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2520 = ((g 17) * (g 17) * (g 23)) := by
  norm_num [atom2520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2520_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229250644761600 : Int) atom2520) := by
  rw [SparsePolynomial.eval_scale, eval_atom2520]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 17) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2520Coded : CoefficientMerge.Poly := [(10223, 1)]
theorem atom2520Coded_decode : atom2520 = SparsePolynomial.decodeCubic 24 atom2520Coded := by decide +kernel
theorem atom2520Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded) := by
  have h := atom2520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2521 : SparsePolynomial.Poly := [([17,18,18], 1)]
theorem eval_atom2521 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2521 = ((g 17) * (g 18) * (g 18)) := by
  norm_num [atom2521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2521_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21474972288000 : Int) atom2521) := by
  rw [SparsePolynomial.eval_scale, eval_atom2521]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 17) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2521Coded : CoefficientMerge.Poly := [(10242, 1)]
theorem atom2521Coded_decode : atom2521 = SparsePolynomial.decodeCubic 24 atom2521Coded := by decide +kernel
theorem atom2521Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) := by
  have h := atom2521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2522 : SparsePolynomial.Poly := [([17,18,19], 1)]
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
def atom2522Coded : CoefficientMerge.Poly := [(10243, 1)]
theorem atom2522Coded_decode : atom2522 = SparsePolynomial.decodeCubic 24 atom2522Coded := by decide +kernel
theorem atom2522Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) := by
  have h := atom2522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2523 : SparsePolynomial.Poly := [([17,18,20], 1)]
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
def atom2523Coded : CoefficientMerge.Poly := [(10244, 1)]
theorem atom2523Coded_decode : atom2523 = SparsePolynomial.decodeCubic 24 atom2523Coded := by decide +kernel
theorem atom2523Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded) := by
  have h := atom2523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2524 : SparsePolynomial.Poly := [([17,18,21], 1)]
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
def atom2524Coded : CoefficientMerge.Poly := [(10245, 1)]
theorem atom2524Coded_decode : atom2524 = SparsePolynomial.decodeCubic 24 atom2524Coded := by decide +kernel
theorem atom2524Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) := by
  have h := atom2524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2525 : SparsePolynomial.Poly := [([17,18,22], 1)]
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
def atom2525Coded : CoefficientMerge.Poly := [(10246, 1)]
theorem atom2525Coded_decode : atom2525 = SparsePolynomial.decodeCubic 24 atom2525Coded := by decide +kernel
theorem atom2525Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded) := by
  have h := atom2525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2526 : SparsePolynomial.Poly := [([17,18,23], 1)]
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
def atom2526Coded : CoefficientMerge.Poly := [(10247, 1)]
theorem atom2526Coded_decode : atom2526 = SparsePolynomial.decodeCubic 24 atom2526Coded := by decide +kernel
theorem atom2526Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) := by
  have h := atom2526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2527 : SparsePolynomial.Poly := [([17,19,19], 1)]
theorem eval_atom2527 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom2527 = ((g 17) * (g 19) * (g 19)) := by
  norm_num [atom2527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom2527_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54618721597440 : Int) atom2527) := by
  rw [SparsePolynomial.eval_scale, eval_atom2527]
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 17) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom2527Coded : CoefficientMerge.Poly := [(10267, 1)]
theorem atom2527Coded_decode : atom2527 = SparsePolynomial.decodeCubic 24 atom2527Coded := by decide +kernel
theorem atom2527Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) := by
  have h := atom2527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom2528 : SparsePolynomial.Poly := [([17,19,20], 1)]
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
def atom2528Coded : CoefficientMerge.Poly := [(10268, 1)]
theorem atom2528Coded_decode : atom2528 = SparsePolynomial.decodeCubic 24 atom2528Coded := by decide +kernel
theorem atom2528Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded) := by
  have h := atom2528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom2528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block033 : CoefficientMerge.Poly := [(9021, 65163300249600), (9023, 5211208396800), (9042, 24896019778560), (9044, 233856198374400), (9045, 220828821696000), (9046, 99469520156160), (9047, 259121345414400), (9065, 8561639116800), (9066, 35057102976000), (9067, 40411348992000), (9068, 327449191910400), (9069, 349177379443200), (9070, 284381337945600), (9071, 503972755372800), (9090, 71490459801600), (9091, 197412532531200), (9092, 533527742361600), (9093, 587959355289600), (9094, 457214273107200), (9095, 739589540659200), (9115, 86391113840640), (9116, 505631540736000), (9117, 646813536768000), (9118, 564551442201600), (9119, 760681790668800), (9140, 379709468006400), (9141, 776088617472000), (9142, 671767480339200), (9143, 726466161254400), (9165, 347050500249600), (9166, 657396548726400), (9167, 747558411264000), (9190, 276807592656000), (9191, 682549021425600), (9215, 367217515929600), (9616, 1027680192000), (9618, 7461795801600), (9620, 109950182899200), (9621, 102488387097600), (9623, 102213909504000), (9641, 2395557964800), (9643, 9886777420800), (9644, 292154122444800), (9645, 317089058764800), (9646, 188403739776000), (9647, 477770776358400), (9666, 41516346816000), (9667, 149668894771200), (9668, 497988692812800), (9669, 564624893952000), (9670, 426558798489600), (9671, 759406049740800), (9691, 65538548490240), (9692, 477151590988800), (9693, 631558767974400), (9694, 581263648358400), (9695, 790619177779200), (9716, 368999043033600), (9717, 768913541222400), (9718, 735847367270400), (9719, 804008014387200), (9741, 347502808396800), (9742, 749710418688000), (9743, 835221142425600), (9766, 375348914640000), (9767, 866434270464000), (9791, 439911553536000), (10219, 14841119462400), (10220, 155130096844800), (10221, 169971216307200), (10222, 96697940774400), (10223, 229250644761600), (10242, 21474972288000), (10243, 121790733926400), (10244, 482315120179200), (10245, 561155909529600), (10246, 434170719360000), (10247, 779222558822400), (10267, 54618721597440), (10268, 468537118156800)]
theorem block033_data : block033 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65163300249600 : Int) atom2449Coded) (CoefficientMerge.scale (5211208396800 : Int) atom2450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24896019778560 : Int) atom2451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (233856198374400 : Int) atom2452Coded) (CoefficientMerge.scale (220828821696000 : Int) atom2453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99469520156160 : Int) atom2454Coded) (CoefficientMerge.scale (259121345414400 : Int) atom2455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8561639116800 : Int) atom2456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35057102976000 : Int) atom2457Coded) (CoefficientMerge.scale (40411348992000 : Int) atom2458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (327449191910400 : Int) atom2459Coded) (CoefficientMerge.scale (349177379443200 : Int) atom2460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284381337945600 : Int) atom2461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (503972755372800 : Int) atom2462Coded) (CoefficientMerge.scale (71490459801600 : Int) atom2463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (197412532531200 : Int) atom2464Coded) (CoefficientMerge.scale (533527742361600 : Int) atom2465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (587959355289600 : Int) atom2466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457214273107200 : Int) atom2467Coded) (CoefficientMerge.scale (739589540659200 : Int) atom2468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86391113840640 : Int) atom2469Coded) (CoefficientMerge.scale (505631540736000 : Int) atom2470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (646813536768000 : Int) atom2471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (564551442201600 : Int) atom2472Coded) (CoefficientMerge.scale (760681790668800 : Int) atom2473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379709468006400 : Int) atom2474Coded) (CoefficientMerge.scale (776088617472000 : Int) atom2475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (671767480339200 : Int) atom2476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (726466161254400 : Int) atom2477Coded) (CoefficientMerge.scale (347050500249600 : Int) atom2478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (657396548726400 : Int) atom2479Coded) (CoefficientMerge.scale (747558411264000 : Int) atom2480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (276807592656000 : Int) atom2481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (682549021425600 : Int) atom2482Coded) (CoefficientMerge.scale (367217515929600 : Int) atom2483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1027680192000 : Int) atom2484Coded) (CoefficientMerge.scale (7461795801600 : Int) atom2485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109950182899200 : Int) atom2486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (102488387097600 : Int) atom2487Coded) (CoefficientMerge.scale (102213909504000 : Int) atom2488Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2395557964800 : Int) atom2489Coded) (CoefficientMerge.scale (9886777420800 : Int) atom2490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292154122444800 : Int) atom2491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317089058764800 : Int) atom2492Coded) (CoefficientMerge.scale (188403739776000 : Int) atom2493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (477770776358400 : Int) atom2494Coded) (CoefficientMerge.scale (41516346816000 : Int) atom2495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (149668894771200 : Int) atom2496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497988692812800 : Int) atom2497Coded) (CoefficientMerge.scale (564624893952000 : Int) atom2498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (426558798489600 : Int) atom2499Coded) (CoefficientMerge.scale (759406049740800 : Int) atom2500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65538548490240 : Int) atom2501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (477151590988800 : Int) atom2502Coded) (CoefficientMerge.scale (631558767974400 : Int) atom2503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (581263648358400 : Int) atom2504Coded) (CoefficientMerge.scale (790619177779200 : Int) atom2505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (368999043033600 : Int) atom2506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (768913541222400 : Int) atom2507Coded) (CoefficientMerge.scale (735847367270400 : Int) atom2508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (804008014387200 : Int) atom2509Coded) (CoefficientMerge.scale (347502808396800 : Int) atom2510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (749710418688000 : Int) atom2511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (835221142425600 : Int) atom2512Coded) (CoefficientMerge.scale (375348914640000 : Int) atom2513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (866434270464000 : Int) atom2514Coded) (CoefficientMerge.scale (439911553536000 : Int) atom2515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14841119462400 : Int) atom2516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155130096844800 : Int) atom2517Coded) (CoefficientMerge.scale (169971216307200 : Int) atom2518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (96697940774400 : Int) atom2519Coded) (CoefficientMerge.scale (229250644761600 : Int) atom2520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21474972288000 : Int) atom2521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121790733926400 : Int) atom2522Coded) (CoefficientMerge.scale (482315120179200 : Int) atom2523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (561155909529600 : Int) atom2524Coded) (CoefficientMerge.scale (434170719360000 : Int) atom2525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (779222558822400 : Int) atom2526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54618721597440 : Int) atom2527Coded) (CoefficientMerge.scale (468537118156800 : Int) atom2528Coded)))))))) := by decide +kernel
theorem block033_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block033 := by
  rw [block033_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2449Coded_nonneg g hg hA hB) (atom2450Coded_nonneg g hg hA hB)) (add_nonneg (atom2451Coded_nonneg g hg hA hB) (add_nonneg (atom2452Coded_nonneg g hg hA hB) (atom2453Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2454Coded_nonneg g hg hA hB) (atom2455Coded_nonneg g hg hA hB)) (add_nonneg (atom2456Coded_nonneg g hg hA hB) (add_nonneg (atom2457Coded_nonneg g hg hA hB) (atom2458Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2459Coded_nonneg g hg hA hB) (atom2460Coded_nonneg g hg hA hB)) (add_nonneg (atom2461Coded_nonneg g hg hA hB) (add_nonneg (atom2462Coded_nonneg g hg hA hB) (atom2463Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2464Coded_nonneg g hg hA hB) (atom2465Coded_nonneg g hg hA hB)) (add_nonneg (atom2466Coded_nonneg g hg hA hB) (add_nonneg (atom2467Coded_nonneg g hg hA hB) (atom2468Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2469Coded_nonneg g hg hA hB) (atom2470Coded_nonneg g hg hA hB)) (add_nonneg (atom2471Coded_nonneg g hg hA hB) (add_nonneg (atom2472Coded_nonneg g hg hA hB) (atom2473Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2474Coded_nonneg g hg hA hB) (atom2475Coded_nonneg g hg hA hB)) (add_nonneg (atom2476Coded_nonneg g hg hA hB) (add_nonneg (atom2477Coded_nonneg g hg hA hB) (atom2478Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2479Coded_nonneg g hg hA hB) (atom2480Coded_nonneg g hg hA hB)) (add_nonneg (atom2481Coded_nonneg g hg hA hB) (add_nonneg (atom2482Coded_nonneg g hg hA hB) (atom2483Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2484Coded_nonneg g hg hA hB) (atom2485Coded_nonneg g hg hA hB)) (add_nonneg (atom2486Coded_nonneg g hg hA hB) (add_nonneg (atom2487Coded_nonneg g hg hA hB) (atom2488Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2489Coded_nonneg g hg hA hB) (atom2490Coded_nonneg g hg hA hB)) (add_nonneg (atom2491Coded_nonneg g hg hA hB) (add_nonneg (atom2492Coded_nonneg g hg hA hB) (atom2493Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2494Coded_nonneg g hg hA hB) (atom2495Coded_nonneg g hg hA hB)) (add_nonneg (atom2496Coded_nonneg g hg hA hB) (add_nonneg (atom2497Coded_nonneg g hg hA hB) (atom2498Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2499Coded_nonneg g hg hA hB) (atom2500Coded_nonneg g hg hA hB)) (add_nonneg (atom2501Coded_nonneg g hg hA hB) (add_nonneg (atom2502Coded_nonneg g hg hA hB) (atom2503Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2504Coded_nonneg g hg hA hB) (atom2505Coded_nonneg g hg hA hB)) (add_nonneg (atom2506Coded_nonneg g hg hA hB) (add_nonneg (atom2507Coded_nonneg g hg hA hB) (atom2508Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom2509Coded_nonneg g hg hA hB) (atom2510Coded_nonneg g hg hA hB)) (add_nonneg (atom2511Coded_nonneg g hg hA hB) (add_nonneg (atom2512Coded_nonneg g hg hA hB) (atom2513Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2514Coded_nonneg g hg hA hB) (atom2515Coded_nonneg g hg hA hB)) (add_nonneg (atom2516Coded_nonneg g hg hA hB) (add_nonneg (atom2517Coded_nonneg g hg hA hB) (atom2518Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom2519Coded_nonneg g hg hA hB) (atom2520Coded_nonneg g hg hA hB)) (add_nonneg (atom2521Coded_nonneg g hg hA hB) (add_nonneg (atom2522Coded_nonneg g hg hA hB) (atom2523Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom2524Coded_nonneg g hg hA hB) (atom2525Coded_nonneg g hg hA hB)) (add_nonneg (atom2526Coded_nonneg g hg hA hB) (add_nonneg (atom2527Coded_nonneg g hg hA hB) (atom2528Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
