-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1489 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1489 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1489 = ((g 5) * (g 7) * (g 17)) := by
  norm_num [atom1489, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1489_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32355227510496 : Int) atom1489) := by
  rw [SparsePolynomial.eval_scale, eval_atom1489]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1489Coded : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 1))]
theorem atom1489Coded_decode : atom1489 = SparsePolynomial.decodeCubic 24 atom1489Coded := by decide +kernel
theorem atom1489Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) := by
  have h := atom1489_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1489Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1490 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1490 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1490 = ((g 5) * (g 7) * (g 18)) := by
  norm_num [atom1490, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1490_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43745229153648 : Int) atom1490) := by
  rw [SparsePolynomial.eval_scale, eval_atom1490]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1490Coded : CoefficientMerge.Poly := [(nat_lit 3066, Int.ofNat (nat_lit 1))]
theorem atom1490Coded_decode : atom1490 = SparsePolynomial.decodeCubic 24 atom1490Coded := by decide +kernel
theorem atom1490Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded) := by
  have h := atom1490_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1490Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1491 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1491 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1491 = ((g 5) * (g 7) * (g 19)) := by
  norm_num [atom1491, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1491_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56706432921600 : Int) atom1491) := by
  rw [SparsePolynomial.eval_scale, eval_atom1491]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1491Coded : CoefficientMerge.Poly := [(nat_lit 3067, Int.ofNat (nat_lit 1))]
theorem atom1491Coded_decode : atom1491 = SparsePolynomial.decodeCubic 24 atom1491Coded := by decide +kernel
theorem atom1491Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) := by
  have h := atom1491_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1491Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1492 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1492 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1492 = ((g 5) * (g 7) * (g 20)) := by
  norm_num [atom1492, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1492_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76377038711952 : Int) atom1492) := by
  rw [SparsePolynomial.eval_scale, eval_atom1492]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1492Coded : CoefficientMerge.Poly := [(nat_lit 3068, Int.ofNat (nat_lit 1))]
theorem atom1492Coded_decode : atom1492 = SparsePolynomial.decodeCubic 24 atom1492Coded := by decide +kernel
theorem atom1492Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) := by
  have h := atom1492_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1492Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1493 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1493 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1493 = ((g 5) * (g 7) * (g 21)) := by
  norm_num [atom1493, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1493_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (133755104320728 : Int) atom1493) := by
  rw [SparsePolynomial.eval_scale, eval_atom1493]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1493Coded : CoefficientMerge.Poly := [(nat_lit 3069, Int.ofNat (nat_lit 1))]
theorem atom1493Coded_decode : atom1493 = SparsePolynomial.decodeCubic 24 atom1493Coded := by decide +kernel
theorem atom1493Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded) := by
  have h := atom1493_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1493Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1494 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1494 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1494 = ((g 5) * (g 7) * (g 22)) := by
  norm_num [atom1494, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1494_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191133169929504 : Int) atom1494) := by
  rw [SparsePolynomial.eval_scale, eval_atom1494]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1494Coded : CoefficientMerge.Poly := [(nat_lit 3070, Int.ofNat (nat_lit 1))]
theorem atom1494Coded_decode : atom1494 = SparsePolynomial.decodeCubic 24 atom1494Coded := by decide +kernel
theorem atom1494Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) := by
  have h := atom1494_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1494Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1495 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1495 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1495 = ((g 5) * (g 7) * (g 23)) := by
  norm_num [atom1495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1495_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (252374959277892 : Int) atom1495) := by
  rw [SparsePolynomial.eval_scale, eval_atom1495]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1495Coded : CoefficientMerge.Poly := [(nat_lit 3071, Int.ofNat (nat_lit 1))]
theorem atom1495Coded_decode : atom1495 = SparsePolynomial.decodeCubic 24 atom1495Coded := by decide +kernel
theorem atom1495Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded) := by
  have h := atom1495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1496 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1496 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1496 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom1496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1496_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30617742364704 : Int) atom1496) := by
  rw [SparsePolynomial.eval_scale, eval_atom1496]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1496Coded : CoefficientMerge.Poly := [(nat_lit 3080, Int.ofNat (nat_lit 1))]
theorem atom1496Coded_decode : atom1496 = SparsePolynomial.decodeCubic 24 atom1496Coded := by decide +kernel
theorem atom1496Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) := by
  have h := atom1496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1497 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1497 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1497 = ((g 5) * (g 8) * (g 9)) := by
  norm_num [atom1497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1497_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48899114252208 : Int) atom1497) := by
  rw [SparsePolynomial.eval_scale, eval_atom1497]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1497Coded : CoefficientMerge.Poly := [(nat_lit 3081, Int.ofNat (nat_lit 1))]
theorem atom1497Coded_decode : atom1497 = SparsePolynomial.decodeCubic 24 atom1497Coded := by decide +kernel
theorem atom1497Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) := by
  have h := atom1497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1498 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1498 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1498 = ((g 5) * (g 8) * (g 10)) := by
  norm_num [atom1498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1498_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21675381235200 : Int) atom1498) := by
  rw [SparsePolynomial.eval_scale, eval_atom1498]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1498Coded : CoefficientMerge.Poly := [(nat_lit 3082, Int.ofNat (nat_lit 1))]
theorem atom1498Coded_decode : atom1498 = SparsePolynomial.decodeCubic 24 atom1498Coded := by decide +kernel
theorem atom1498Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded) := by
  have h := atom1498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1499 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1499 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1499 = ((g 5) * (g 8) * (g 11)) := by
  norm_num [atom1499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1499_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31085474131008 : Int) atom1499) := by
  rw [SparsePolynomial.eval_scale, eval_atom1499]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1499Coded : CoefficientMerge.Poly := [(nat_lit 3083, Int.ofNat (nat_lit 1))]
theorem atom1499Coded_decode : atom1499 = SparsePolynomial.decodeCubic 24 atom1499Coded := by decide +kernel
theorem atom1499Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) := by
  have h := atom1499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1500 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1500 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1500 = ((g 5) * (g 8) * (g 12)) := by
  norm_num [atom1500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1500_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58922406959328 : Int) atom1500) := by
  rw [SparsePolynomial.eval_scale, eval_atom1500]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1500Coded : CoefficientMerge.Poly := [(nat_lit 3084, Int.ofNat (nat_lit 1))]
theorem atom1500Coded_decode : atom1500 = SparsePolynomial.decodeCubic 24 atom1500Coded := by decide +kernel
theorem atom1500Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded) := by
  have h := atom1500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1501 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1501 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1501 = ((g 5) * (g 8) * (g 13)) := by
  norm_num [atom1501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1501_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53259267609504 : Int) atom1501) := by
  rw [SparsePolynomial.eval_scale, eval_atom1501]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1501Coded : CoefficientMerge.Poly := [(nat_lit 3085, Int.ofNat (nat_lit 1))]
theorem atom1501Coded_decode : atom1501 = SparsePolynomial.decodeCubic 24 atom1501Coded := by decide +kernel
theorem atom1501Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) := by
  have h := atom1501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1502 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1502 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1502 = ((g 5) * (g 8) * (g 14)) := by
  norm_num [atom1502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1502_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43921865443104 : Int) atom1502) := by
  rw [SparsePolynomial.eval_scale, eval_atom1502]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1502Coded : CoefficientMerge.Poly := [(nat_lit 3086, Int.ofNat (nat_lit 1))]
theorem atom1502Coded_decode : atom1502 = SparsePolynomial.decodeCubic 24 atom1502Coded := by decide +kernel
theorem atom1502Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) := by
  have h := atom1502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1503 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1503 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1503 = ((g 5) * (g 8) * (g 15)) := by
  norm_num [atom1503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1503_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50109208943904 : Int) atom1503) := by
  rw [SparsePolynomial.eval_scale, eval_atom1503]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1503Coded : CoefficientMerge.Poly := [(nat_lit 3087, Int.ofNat (nat_lit 1))]
theorem atom1503Coded_decode : atom1503 = SparsePolynomial.decodeCubic 24 atom1503Coded := by decide +kernel
theorem atom1503Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded) := by
  have h := atom1503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1504 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1504 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1504 = ((g 5) * (g 8) * (g 16)) := by
  norm_num [atom1504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1504_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56296552444704 : Int) atom1504) := by
  rw [SparsePolynomial.eval_scale, eval_atom1504]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1504Coded : CoefficientMerge.Poly := [(nat_lit 3088, Int.ofNat (nat_lit 1))]
theorem atom1504Coded_decode : atom1504 = SparsePolynomial.decodeCubic 24 atom1504Coded := by decide +kernel
theorem atom1504Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) := by
  have h := atom1504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1505 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1505 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1505 = ((g 5) * (g 8) * (g 17)) := by
  norm_num [atom1505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1505_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62483895945504 : Int) atom1505) := by
  rw [SparsePolynomial.eval_scale, eval_atom1505]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1505Coded : CoefficientMerge.Poly := [(nat_lit 3089, Int.ofNat (nat_lit 1))]
theorem atom1505Coded_decode : atom1505 = SparsePolynomial.decodeCubic 24 atom1505Coded := by decide +kernel
theorem atom1505Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded) := by
  have h := atom1505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1506 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1506 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1506 = ((g 5) * (g 8) * (g 18)) := by
  norm_num [atom1506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1506_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76832947703952 : Int) atom1506) := by
  rw [SparsePolynomial.eval_scale, eval_atom1506]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1506Coded : CoefficientMerge.Poly := [(nat_lit 3090, Int.ofNat (nat_lit 1))]
theorem atom1506Coded_decode : atom1506 = SparsePolynomial.decodeCubic 24 atom1506Coded := by decide +kernel
theorem atom1506Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) := by
  have h := atom1506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1507 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1507 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1507 = ((g 5) * (g 8) * (g 19)) := by
  norm_num [atom1507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1507_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96207152025600 : Int) atom1507) := by
  rw [SparsePolynomial.eval_scale, eval_atom1507]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1507Coded : CoefficientMerge.Poly := [(nat_lit 3091, Int.ofNat (nat_lit 1))]
theorem atom1507Coded_decode : atom1507 = SparsePolynomial.decodeCubic 24 atom1507Coded := by decide +kernel
theorem atom1507Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) := by
  have h := atom1507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1508 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1508 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1508 = ((g 5) * (g 8) * (g 20)) := by
  norm_num [atom1508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1508_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122290758369648 : Int) atom1508) := by
  rw [SparsePolynomial.eval_scale, eval_atom1508]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1508Coded : CoefficientMerge.Poly := [(nat_lit 3092, Int.ofNat (nat_lit 1))]
theorem atom1508Coded_decode : atom1508 = SparsePolynomial.decodeCubic 24 atom1508Coded := by decide +kernel
theorem atom1508Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded) := by
  have h := atom1508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1509 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1509 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1509 = ((g 5) * (g 8) * (g 21)) := by
  norm_num [atom1509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1509_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193758103116072 : Int) atom1509) := by
  rw [SparsePolynomial.eval_scale, eval_atom1509]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1509Coded : CoefficientMerge.Poly := [(nat_lit 3093, Int.ofNat (nat_lit 1))]
theorem atom1509Coded_decode : atom1509 = SparsePolynomial.decodeCubic 24 atom1509Coded := by decide +kernel
theorem atom1509Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) := by
  have h := atom1509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1510 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1510 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1510 = ((g 5) * (g 8) * (g 22)) := by
  norm_num [atom1510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1510_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (265225447862496 : Int) atom1510) := by
  rw [SparsePolynomial.eval_scale, eval_atom1510]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1510Coded : CoefficientMerge.Poly := [(nat_lit 3094, Int.ofNat (nat_lit 1))]
theorem atom1510Coded_decode : atom1510 = SparsePolynomial.decodeCubic 24 atom1510Coded := by decide +kernel
theorem atom1510Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded) := by
  have h := atom1510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1511 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1511 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1511 = ((g 5) * (g 8) * (g 23)) := by
  norm_num [atom1511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1511_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (340940705202108 : Int) atom1511) := by
  rw [SparsePolynomial.eval_scale, eval_atom1511]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1511Coded : CoefficientMerge.Poly := [(nat_lit 3095, Int.ofNat (nat_lit 1))]
theorem atom1511Coded_decode : atom1511 = SparsePolynomial.decodeCubic 24 atom1511Coded := by decide +kernel
theorem atom1511Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) := by
  have h := atom1511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1512 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1512 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1512 = ((g 5) * (g 9) * (g 9)) := by
  norm_num [atom1512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1512_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50132370389904 : Int) atom1512) := by
  rw [SparsePolynomial.eval_scale, eval_atom1512]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1512Coded : CoefficientMerge.Poly := [(nat_lit 3105, Int.ofNat (nat_lit 1))]
theorem atom1512Coded_decode : atom1512 = SparsePolynomial.decodeCubic 24 atom1512Coded := by decide +kernel
theorem atom1512Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) := by
  have h := atom1512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1513 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1513 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1513 = ((g 5) * (g 9) * (g 10)) := by
  norm_num [atom1513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1513_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73000342255104 : Int) atom1513) := by
  rw [SparsePolynomial.eval_scale, eval_atom1513]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1513Coded : CoefficientMerge.Poly := [(nat_lit 3106, Int.ofNat (nat_lit 1))]
theorem atom1513Coded_decode : atom1513 = SparsePolynomial.decodeCubic 24 atom1513Coded := by decide +kernel
theorem atom1513Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded) := by
  have h := atom1513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1514 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1514 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1514 = ((g 5) * (g 9) * (g 11)) := by
  norm_num [atom1514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1514_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60389198950608 : Int) atom1514) := by
  rw [SparsePolynomial.eval_scale, eval_atom1514]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1514Coded : CoefficientMerge.Poly := [(nat_lit 3107, Int.ofNat (nat_lit 1))]
theorem atom1514Coded_decode : atom1514 = SparsePolynomial.decodeCubic 24 atom1514Coded := by decide +kernel
theorem atom1514Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) := by
  have h := atom1514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1515 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1515 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1515 = ((g 5) * (g 9) * (g 12)) := by
  norm_num [atom1515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1515_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91330434703728 : Int) atom1515) := by
  rw [SparsePolynomial.eval_scale, eval_atom1515]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1515Coded : CoefficientMerge.Poly := [(nat_lit 3108, Int.ofNat (nat_lit 1))]
theorem atom1515Coded_decode : atom1515 = SparsePolynomial.decodeCubic 24 atom1515Coded := by decide +kernel
theorem atom1515Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded) := by
  have h := atom1515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1516 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1516 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1516 = ((g 5) * (g 9) * (g 13)) := by
  norm_num [atom1516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1516_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82605517126704 : Int) atom1516) := by
  rw [SparsePolynomial.eval_scale, eval_atom1516]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1516Coded : CoefficientMerge.Poly := [(nat_lit 3109, Int.ofNat (nat_lit 1))]
theorem atom1516Coded_decode : atom1516 = SparsePolynomial.decodeCubic 24 atom1516Coded := by decide +kernel
theorem atom1516Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) := by
  have h := atom1516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1517 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1517 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1517 = ((g 5) * (g 9) * (g 14)) := by
  norm_num [atom1517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1517_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73289377309104 : Int) atom1517) := by
  rw [SparsePolynomial.eval_scale, eval_atom1517]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1517Coded : CoefficientMerge.Poly := [(nat_lit 3110, Int.ofNat (nat_lit 1))]
theorem atom1517Coded_decode : atom1517 = SparsePolynomial.decodeCubic 24 atom1517Coded := by decide +kernel
theorem atom1517Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) := by
  have h := atom1517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1518 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1518 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1518 = ((g 5) * (g 9) * (g 15)) := by
  norm_num [atom1518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1518_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79497983158704 : Int) atom1518) := by
  rw [SparsePolynomial.eval_scale, eval_atom1518]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1518Coded : CoefficientMerge.Poly := [(nat_lit 3111, Int.ofNat (nat_lit 1))]
theorem atom1518Coded_decode : atom1518 = SparsePolynomial.decodeCubic 24 atom1518Coded := by decide +kernel
theorem atom1518Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded) := by
  have h := atom1518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1519 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1519 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1519 = ((g 5) * (g 9) * (g 16)) := by
  norm_num [atom1519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1519_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85706589008304 : Int) atom1519) := by
  rw [SparsePolynomial.eval_scale, eval_atom1519]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1519Coded : CoefficientMerge.Poly := [(nat_lit 3112, Int.ofNat (nat_lit 1))]
theorem atom1519Coded_decode : atom1519 = SparsePolynomial.decodeCubic 24 atom1519Coded := by decide +kernel
theorem atom1519Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) := by
  have h := atom1519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1520 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1520 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1520 = ((g 5) * (g 9) * (g 17)) := by
  norm_num [atom1520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1520_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91915194857904 : Int) atom1520) := by
  rw [SparsePolynomial.eval_scale, eval_atom1520]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1520Coded : CoefficientMerge.Poly := [(nat_lit 3113, Int.ofNat (nat_lit 1))]
theorem atom1520Coded_decode : atom1520 = SparsePolynomial.decodeCubic 24 atom1520Coded := by decide +kernel
theorem atom1520Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded) := by
  have h := atom1520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1521 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1521 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1521 = ((g 5) * (g 9) * (g 18)) := by
  norm_num [atom1521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1521_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110304175786200 : Int) atom1521) := by
  rw [SparsePolynomial.eval_scale, eval_atom1521]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1521Coded : CoefficientMerge.Poly := [(nat_lit 3114, Int.ofNat (nat_lit 1))]
theorem atom1521Coded_decode : atom1521 = SparsePolynomial.decodeCubic 24 atom1521Coded := by decide +kernel
theorem atom1521Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) := by
  have h := atom1521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1522 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1522 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1522 = ((g 5) * (g 9) * (g 19)) := by
  norm_num [atom1522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1522_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135921777108480 : Int) atom1522) := by
  rw [SparsePolynomial.eval_scale, eval_atom1522]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1522Coded : CoefficientMerge.Poly := [(nat_lit 3115, Int.ofNat (nat_lit 1))]
theorem atom1522Coded_decode : atom1522 = SparsePolynomial.decodeCubic 24 atom1522Coded := by decide +kernel
theorem atom1522Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) := by
  have h := atom1522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1523 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1523 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1523 = ((g 5) * (g 9) * (g 20)) := by
  norm_num [atom1523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1523_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168248780453160 : Int) atom1523) := by
  rw [SparsePolynomial.eval_scale, eval_atom1523]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1523Coded : CoefficientMerge.Poly := [(nat_lit 3116, Int.ofNat (nat_lit 1))]
theorem atom1523Coded_decode : atom1523 = SparsePolynomial.decodeCubic 24 atom1523Coded := by decide +kernel
theorem atom1523Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded) := by
  have h := atom1523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1524 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1524 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1524 = ((g 5) * (g 9) * (g 21)) := by
  norm_num [atom1524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1524_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (249458858366652 : Int) atom1524) := by
  rw [SparsePolynomial.eval_scale, eval_atom1524]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1524Coded : CoefficientMerge.Poly := [(nat_lit 3117, Int.ofNat (nat_lit 1))]
theorem atom1524Coded_decode : atom1524 = SparsePolynomial.decodeCubic 24 atom1524Coded := by decide +kernel
theorem atom1524Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) := by
  have h := atom1524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1525 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1525 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1525 = ((g 5) * (g 9) * (g 22)) := by
  norm_num [atom1525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1525_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (330668936280144 : Int) atom1525) := by
  rw [SparsePolynomial.eval_scale, eval_atom1525]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1525Coded : CoefficientMerge.Poly := [(nat_lit 3118, Int.ofNat (nat_lit 1))]
theorem atom1525Coded_decode : atom1525 = SparsePolynomial.decodeCubic 24 atom1525Coded := by decide +kernel
theorem atom1525Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded) := by
  have h := atom1525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1526 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1526 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1526 = ((g 5) * (g 9) * (g 23)) := by
  norm_num [atom1526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1526_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415673127039258 : Int) atom1526) := by
  rw [SparsePolynomial.eval_scale, eval_atom1526]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1526Coded : CoefficientMerge.Poly := [(nat_lit 3119, Int.ofNat (nat_lit 1))]
theorem atom1526Coded_decode : atom1526 = SparsePolynomial.decodeCubic 24 atom1526Coded := by decide +kernel
theorem atom1526Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) := by
  have h := atom1526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1527 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1527 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1527 = ((g 5) * (g 10) * (g 10)) := by
  norm_num [atom1527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1527_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54718970367600 : Int) atom1527) := by
  rw [SparsePolynomial.eval_scale, eval_atom1527]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1527Coded : CoefficientMerge.Poly := [(nat_lit 3130, Int.ofNat (nat_lit 1))]
theorem atom1527Coded_decode : atom1527 = SparsePolynomial.decodeCubic 24 atom1527Coded := by decide +kernel
theorem atom1527Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) := by
  have h := atom1527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1528 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1528 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1528 = ((g 5) * (g 10) * (g 11)) := by
  norm_num [atom1528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1528_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103035403280304 : Int) atom1528) := by
  rw [SparsePolynomial.eval_scale, eval_atom1528]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1528Coded : CoefficientMerge.Poly := [(nat_lit 3131, Int.ofNat (nat_lit 1))]
theorem atom1528Coded_decode : atom1528 = SparsePolynomial.decodeCubic 24 atom1528Coded := by decide +kernel
theorem atom1528Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded) := by
  have h := atom1528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1529 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1529 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1529 = ((g 5) * (g 10) * (g 12)) := by
  norm_num [atom1529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1529_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129894268063824 : Int) atom1529) := by
  rw [SparsePolynomial.eval_scale, eval_atom1529]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1529Coded : CoefficientMerge.Poly := [(nat_lit 3132, Int.ofNat (nat_lit 1))]
theorem atom1529Coded_decode : atom1529 = SparsePolynomial.decodeCubic 24 atom1529Coded := by decide +kernel
theorem atom1529Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) := by
  have h := atom1529_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1529Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1530 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1530 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1530 = ((g 5) * (g 10) * (g 13)) := by
  norm_num [atom1530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1530_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123253060669200 : Int) atom1530) := by
  rw [SparsePolynomial.eval_scale, eval_atom1530]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1530Coded : CoefficientMerge.Poly := [(nat_lit 3133, Int.ofNat (nat_lit 1))]
theorem atom1530Coded_decode : atom1530 = SparsePolynomial.decodeCubic 24 atom1530Coded := by decide +kernel
theorem atom1530Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded) := by
  have h := atom1530_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1530Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1531 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1531 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1531 = ((g 5) * (g 10) * (g 14)) := by
  norm_num [atom1531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1531_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (112937590458000 : Int) atom1531) := by
  rw [SparsePolynomial.eval_scale, eval_atom1531]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1531Coded : CoefficientMerge.Poly := [(nat_lit 3134, Int.ofNat (nat_lit 1))]
theorem atom1531Coded_decode : atom1531 = SparsePolynomial.decodeCubic 24 atom1531Coded := by decide +kernel
theorem atom1531Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) := by
  have h := atom1531_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1531Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1532 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1532 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1532 = ((g 5) * (g 10) * (g 15)) := by
  norm_num [atom1532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1532_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118146865914000 : Int) atom1532) := by
  rw [SparsePolynomial.eval_scale, eval_atom1532]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1532Coded : CoefficientMerge.Poly := [(nat_lit 3135, Int.ofNat (nat_lit 1))]
theorem atom1532Coded_decode : atom1532 = SparsePolynomial.decodeCubic 24 atom1532Coded := by decide +kernel
theorem atom1532Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) := by
  have h := atom1532_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1532Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1533 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1533 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1533 = ((g 5) * (g 10) * (g 16)) := by
  norm_num [atom1533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1533_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123356141370000 : Int) atom1533) := by
  rw [SparsePolynomial.eval_scale, eval_atom1533]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1533Coded : CoefficientMerge.Poly := [(nat_lit 3136, Int.ofNat (nat_lit 1))]
theorem atom1533Coded_decode : atom1533 = SparsePolynomial.decodeCubic 24 atom1533Coded := by decide +kernel
theorem atom1533Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded) := by
  have h := atom1533_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1533Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1534 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1534 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1534 = ((g 5) * (g 10) * (g 17)) := by
  norm_num [atom1534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1534_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (128565416826000 : Int) atom1534) := by
  rw [SparsePolynomial.eval_scale, eval_atom1534]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1534Coded : CoefficientMerge.Poly := [(nat_lit 3137, Int.ofNat (nat_lit 1))]
theorem atom1534Coded_decode : atom1534 = SparsePolynomial.decodeCubic 24 atom1534Coded := by decide +kernel
theorem atom1534Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) := by
  have h := atom1534_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1534Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1535 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1535 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1535 = ((g 5) * (g 10) * (g 18)) := by
  norm_num [atom1535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1535_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154777723324488 : Int) atom1535) := by
  rw [SparsePolynomial.eval_scale, eval_atom1535]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1535Coded : CoefficientMerge.Poly := [(nat_lit 3138, Int.ofNat (nat_lit 1))]
theorem atom1535Coded_decode : atom1535 = SparsePolynomial.decodeCubic 24 atom1535Coded := by decide +kernel
theorem atom1535Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded) := by
  have h := atom1535_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1535Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1536 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1536 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1536 = ((g 5) * (g 10) * (g 19)) := by
  norm_num [atom1536, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1536_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (186951414228480 : Int) atom1536) := by
  rw [SparsePolynomial.eval_scale, eval_atom1536]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1536Coded : CoefficientMerge.Poly := [(nat_lit 3139, Int.ofNat (nat_lit 1))]
theorem atom1536Coded_decode : atom1536 = SparsePolynomial.decodeCubic 24 atom1536Coded := by decide +kernel
theorem atom1536Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) := by
  have h := atom1536_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1536Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1537 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1537 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1537 = ((g 5) * (g 10) * (g 20)) := by
  norm_num [atom1537, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1537_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225834507154872 : Int) atom1537) := by
  rw [SparsePolynomial.eval_scale, eval_atom1537]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1537Coded : CoefficientMerge.Poly := [(nat_lit 3140, Int.ofNat (nat_lit 1))]
theorem atom1537Coded_decode : atom1537 = SparsePolynomial.decodeCubic 24 atom1537Coded := by decide +kernel
theorem atom1537Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) := by
  have h := atom1537_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1537Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1538 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1538 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1538 = ((g 5) * (g 10) * (g 21)) := by
  norm_num [atom1538, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1538_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (306021256696980 : Int) atom1538) := by
  rw [SparsePolynomial.eval_scale, eval_atom1538]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1538Coded : CoefficientMerge.Poly := [(nat_lit 3141, Int.ofNat (nat_lit 1))]
theorem atom1538Coded_decode : atom1538 = SparsePolynomial.decodeCubic 24 atom1538Coded := by decide +kernel
theorem atom1538Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded) := by
  have h := atom1538_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1538Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1539 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1539 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1539 = ((g 5) * (g 10) * (g 22)) := by
  norm_num [atom1539, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1539_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (386208006239088 : Int) atom1539) := by
  rw [SparsePolynomial.eval_scale, eval_atom1539]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1539Coded : CoefficientMerge.Poly := [(nat_lit 3142, Int.ofNat (nat_lit 1))]
theorem atom1539Coded_decode : atom1539 = SparsePolynomial.decodeCubic 24 atom1539Coded := by decide +kernel
theorem atom1539Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) := by
  have h := atom1539_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1539Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1540 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1540 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1540 = ((g 5) * (g 10) * (g 23)) := by
  norm_num [atom1540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1540_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (467666395638750 : Int) atom1540) := by
  rw [SparsePolynomial.eval_scale, eval_atom1540]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1540Coded : CoefficientMerge.Poly := [(nat_lit 3143, Int.ofNat (nat_lit 1))]
theorem atom1540Coded_decode : atom1540 = SparsePolynomial.decodeCubic 24 atom1540Coded := by decide +kernel
theorem atom1540Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded) := by
  have h := atom1540_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1540Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1541 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1541 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1541 = ((g 5) * (g 11) * (g 11)) := by
  norm_num [atom1541, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1541_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86333512567104 : Int) atom1541) := by
  rw [SparsePolynomial.eval_scale, eval_atom1541]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1541Coded : CoefficientMerge.Poly := [(nat_lit 3155, Int.ofNat (nat_lit 1))]
theorem atom1541Coded_decode : atom1541 = SparsePolynomial.decodeCubic 24 atom1541Coded := by decide +kernel
theorem atom1541Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) := by
  have h := atom1541_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1541Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1542 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1542 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1542 = ((g 5) * (g 11) * (g 12)) := by
  norm_num [atom1542, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1542_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177727995707328 : Int) atom1542) := by
  rw [SparsePolynomial.eval_scale, eval_atom1542]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1542Coded : CoefficientMerge.Poly := [(nat_lit 3156, Int.ofNat (nat_lit 1))]
theorem atom1542Coded_decode : atom1542 = SparsePolynomial.decodeCubic 24 atom1542Coded := by decide +kernel
theorem atom1542Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) := by
  have h := atom1542_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1542Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1543 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1543 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1543 = ((g 5) * (g 11) * (g 13)) := by
  norm_num [atom1543, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1543_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165983824600704 : Int) atom1543) := by
  rw [SparsePolynomial.eval_scale, eval_atom1543]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1543Coded : CoefficientMerge.Poly := [(nat_lit 3157, Int.ofNat (nat_lit 1))]
theorem atom1543Coded_decode : atom1543 = SparsePolynomial.decodeCubic 24 atom1543Coded := by decide +kernel
theorem atom1543Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded) := by
  have h := atom1543_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1543Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1544 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1544 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1544 = ((g 5) * (g 11) * (g 14)) := by
  norm_num [atom1544, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1544_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150565390677504 : Int) atom1544) := by
  rw [SparsePolynomial.eval_scale, eval_atom1544]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1544Coded : CoefficientMerge.Poly := [(nat_lit 3158, Int.ofNat (nat_lit 1))]
theorem atom1544Coded_decode : atom1544 = SparsePolynomial.decodeCubic 24 atom1544Coded := by decide +kernel
theorem atom1544Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) := by
  have h := atom1544_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1544Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1545 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1545 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1545 = ((g 5) * (g 11) * (g 15)) := by
  norm_num [atom1545, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1545_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150671702421504 : Int) atom1545) := by
  rw [SparsePolynomial.eval_scale, eval_atom1545]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1545Coded : CoefficientMerge.Poly := [(nat_lit 3159, Int.ofNat (nat_lit 1))]
theorem atom1545Coded_decode : atom1545 = SparsePolynomial.decodeCubic 24 atom1545Coded := by decide +kernel
theorem atom1545Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded) := by
  have h := atom1545_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1545Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1546 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1546 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1546 = ((g 5) * (g 11) * (g 16)) := by
  norm_num [atom1546, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1546_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153861054741504 : Int) atom1546) := by
  rw [SparsePolynomial.eval_scale, eval_atom1546]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1546Coded : CoefficientMerge.Poly := [(nat_lit 3160, Int.ofNat (nat_lit 1))]
theorem atom1546Coded_decode : atom1546 = SparsePolynomial.decodeCubic 24 atom1546Coded := by decide +kernel
theorem atom1546Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) := by
  have h := atom1546_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1546Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1547 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1547 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1547 = ((g 5) * (g 11) * (g 17)) := by
  norm_num [atom1547, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1547_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (157050407061504 : Int) atom1547) := by
  rw [SparsePolynomial.eval_scale, eval_atom1547]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1547Coded : CoefficientMerge.Poly := [(nat_lit 3161, Int.ofNat (nat_lit 1))]
theorem atom1547Coded_decode : atom1547 = SparsePolynomial.decodeCubic 24 atom1547Coded := by decide +kernel
theorem atom1547Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) := by
  have h := atom1547_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1547Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1548 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1548 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1548 = ((g 5) * (g 11) * (g 18)) := by
  norm_num [atom1548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1548_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198462683884608 : Int) atom1548) := by
  rw [SparsePolynomial.eval_scale, eval_atom1548]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1548Coded : CoefficientMerge.Poly := [(nat_lit 3162, Int.ofNat (nat_lit 1))]
theorem atom1548Coded_decode : atom1548 = SparsePolynomial.decodeCubic 24 atom1548Coded := by decide +kernel
theorem atom1548Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded) := by
  have h := atom1548_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1548Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1549 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1549 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1549 = ((g 5) * (g 11) * (g 19)) := by
  norm_num [atom1549, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1549_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223083434787840 : Int) atom1549) := by
  rw [SparsePolynomial.eval_scale, eval_atom1549]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1549Coded : CoefficientMerge.Poly := [(nat_lit 3163, Int.ofNat (nat_lit 1))]
theorem atom1549Coded_decode : atom1549 = SparsePolynomial.decodeCubic 24 atom1549Coded := by decide +kernel
theorem atom1549Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) := by
  have h := atom1549_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1549Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1550 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1550 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1550 = ((g 5) * (g 11) * (g 20)) := by
  norm_num [atom1550, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1550_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276330381484608 : Int) atom1550) := by
  rw [SparsePolynomial.eval_scale, eval_atom1550]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1550Coded : CoefficientMerge.Poly := [(nat_lit 3164, Int.ofNat (nat_lit 1))]
theorem atom1550Coded_decode : atom1550 = SparsePolynomial.decodeCubic 24 atom1550Coded := by decide +kernel
theorem atom1550Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded) := by
  have h := atom1550_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1550Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1551 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1551 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1551 = ((g 5) * (g 11) * (g 21)) := by
  norm_num [atom1551, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1551_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (348770785600512 : Int) atom1551) := by
  rw [SparsePolynomial.eval_scale, eval_atom1551]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1551Coded : CoefficientMerge.Poly := [(nat_lit 3165, Int.ofNat (nat_lit 1))]
theorem atom1551Coded_decode : atom1551 = SparsePolynomial.decodeCubic 24 atom1551Coded := by decide +kernel
theorem atom1551Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) := by
  have h := atom1551_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1551Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1552 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1552 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1552 = ((g 5) * (g 11) * (g 22)) := by
  norm_num [atom1552, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1552_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (431499235368960 : Int) atom1552) := by
  rw [SparsePolynomial.eval_scale, eval_atom1552]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1552Coded : CoefficientMerge.Poly := [(nat_lit 3166, Int.ofNat (nat_lit 1))]
theorem atom1552Coded_decode : atom1552 = SparsePolynomial.decodeCubic 24 atom1552Coded := by decide +kernel
theorem atom1552Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) := by
  have h := atom1552_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1552Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1553 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1553 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1553 = ((g 5) * (g 11) * (g 23)) := by
  norm_num [atom1553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1553_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (514227685137408 : Int) atom1553) := by
  rw [SparsePolynomial.eval_scale, eval_atom1553]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1553Coded : CoefficientMerge.Poly := [(nat_lit 3167, Int.ofNat (nat_lit 1))]
theorem atom1553Coded_decode : atom1553 = SparsePolynomial.decodeCubic 24 atom1553Coded := by decide +kernel
theorem atom1553Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded) := by
  have h := atom1553_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1553Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1554 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1554 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1554 = ((g 5) * (g 12) * (g 12)) := by
  norm_num [atom1554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1554_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129411562794624 : Int) atom1554) := by
  rw [SparsePolynomial.eval_scale, eval_atom1554]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1554Coded : CoefficientMerge.Poly := [(nat_lit 3180, Int.ofNat (nat_lit 1))]
theorem atom1554Coded_decode : atom1554 = SparsePolynomial.decodeCubic 24 atom1554Coded := by decide +kernel
theorem atom1554Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) := by
  have h := atom1554_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1554Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1555 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1555 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1555 = ((g 5) * (g 12) * (g 13)) := by
  norm_num [atom1555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1555_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (235307586628224 : Int) atom1555) := by
  rw [SparsePolynomial.eval_scale, eval_atom1555]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1555Coded : CoefficientMerge.Poly := [(nat_lit 3181, Int.ofNat (nat_lit 1))]
theorem atom1555Coded_decode : atom1555 = SparsePolynomial.decodeCubic 24 atom1555Coded := by decide +kernel
theorem atom1555Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded) := by
  have h := atom1555_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1555Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1556 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1556 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1556 = ((g 5) * (g 12) * (g 14)) := by
  norm_num [atom1556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1556_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (219931677402624 : Int) atom1556) := by
  rw [SparsePolynomial.eval_scale, eval_atom1556]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1556Coded : CoefficientMerge.Poly := [(nat_lit 3182, Int.ofNat (nat_lit 1))]
theorem atom1556Coded_decode : atom1556 = SparsePolynomial.decodeCubic 24 atom1556Coded := by decide +kernel
theorem atom1556Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) := by
  have h := atom1556_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1556Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1557 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1557 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1557 = ((g 5) * (g 12) * (g 15)) := by
  norm_num [atom1557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1557_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220080513844224 : Int) atom1557) := by
  rw [SparsePolynomial.eval_scale, eval_atom1557]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1557Coded : CoefficientMerge.Poly := [(nat_lit 3183, Int.ofNat (nat_lit 1))]
theorem atom1557Coded_decode : atom1557 = SparsePolynomial.decodeCubic 24 atom1557Coded := by decide +kernel
theorem atom1557Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) := by
  have h := atom1557_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1557Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1558 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1558 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1558 = ((g 5) * (g 12) * (g 16)) := by
  norm_num [atom1558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1558_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220229350285824 : Int) atom1558) := by
  rw [SparsePolynomial.eval_scale, eval_atom1558]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1558Coded : CoefficientMerge.Poly := [(nat_lit 3184, Int.ofNat (nat_lit 1))]
theorem atom1558Coded_decode : atom1558 = SparsePolynomial.decodeCubic 24 atom1558Coded := by decide +kernel
theorem atom1558Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded) := by
  have h := atom1558_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1558Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1559 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1559 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1559 = ((g 5) * (g 12) * (g 17)) := by
  norm_num [atom1559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1559_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220378186727424 : Int) atom1559) := by
  rw [SparsePolynomial.eval_scale, eval_atom1559]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1559Coded : CoefficientMerge.Poly := [(nat_lit 3185, Int.ofNat (nat_lit 1))]
theorem atom1559Coded_decode : atom1559 = SparsePolynomial.decodeCubic 24 atom1559Coded := by decide +kernel
theorem atom1559Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) := by
  have h := atom1559_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1559Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1560 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1560 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1560 = ((g 5) * (g 12) * (g 18)) := by
  norm_num [atom1560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1560_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (284414134232448 : Int) atom1560) := by
  rw [SparsePolynomial.eval_scale, eval_atom1560]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1560Coded : CoefficientMerge.Poly := [(nat_lit 3186, Int.ofNat (nat_lit 1))]
theorem atom1560Coded_decode : atom1560 = SparsePolynomial.decodeCubic 24 atom1560Coded := by decide +kernel
theorem atom1560Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded) := by
  have h := atom1560_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1560Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1561 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1561 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1561 = ((g 5) * (g 12) * (g 19)) := by
  norm_num [atom1561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1561_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (271093818378240 : Int) atom1561) := by
  rw [SparsePolynomial.eval_scale, eval_atom1561]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1561Coded : CoefficientMerge.Poly := [(nat_lit 3187, Int.ofNat (nat_lit 1))]
theorem atom1561Coded_decode : atom1561 = SparsePolynomial.decodeCubic 24 atom1561Coded := by decide +kernel
theorem atom1561Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) := by
  have h := atom1561_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1561Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1562 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1562 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1562 = ((g 5) * (g 12) * (g 20)) := by
  norm_num [atom1562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1562_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (374528944741248 : Int) atom1562) := by
  rw [SparsePolynomial.eval_scale, eval_atom1562]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1562Coded : CoefficientMerge.Poly := [(nat_lit 3188, Int.ofNat (nat_lit 1))]
theorem atom1562Coded_decode : atom1562 = SparsePolynomial.decodeCubic 24 atom1562Coded := by decide +kernel
theorem atom1562Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) := by
  have h := atom1562_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1562Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1563 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1563 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1563 = ((g 5) * (g 12) * (g 21)) := by
  norm_num [atom1563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1563_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (372227408796672 : Int) atom1563) := by
  rw [SparsePolynomial.eval_scale, eval_atom1563]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1563Coded : CoefficientMerge.Poly := [(nat_lit 3189, Int.ofNat (nat_lit 1))]
theorem atom1563Coded_decode : atom1563 = SparsePolynomial.decodeCubic 24 atom1563Coded := by decide +kernel
theorem atom1563Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded) := by
  have h := atom1563_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1563Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1564 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1564 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1564 = ((g 5) * (g 12) * (g 22)) := by
  norm_num [atom1564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1564_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (439600190261760 : Int) atom1564) := by
  rw [SparsePolynomial.eval_scale, eval_atom1564]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1564Coded : CoefficientMerge.Poly := [(nat_lit 3190, Int.ofNat (nat_lit 1))]
theorem atom1564Coded_decode : atom1564 = SparsePolynomial.decodeCubic 24 atom1564Coded := by decide +kernel
theorem atom1564Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) := by
  have h := atom1564_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1564Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1565 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1565 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1565 = ((g 5) * (g 12) * (g 23)) := by
  norm_num [atom1565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1565_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (506972971726848 : Int) atom1565) := by
  rw [SparsePolynomial.eval_scale, eval_atom1565]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1565Coded : CoefficientMerge.Poly := [(nat_lit 3191, Int.ofNat (nat_lit 1))]
theorem atom1565Coded_decode : atom1565 = SparsePolynomial.decodeCubic 24 atom1565Coded := by decide +kernel
theorem atom1565Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded) := by
  have h := atom1565_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1565Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1566 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1566 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1566 = ((g 5) * (g 13) * (g 13)) := by
  norm_num [atom1566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1566_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (143913103488000 : Int) atom1566) := by
  rw [SparsePolynomial.eval_scale, eval_atom1566]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1566Coded : CoefficientMerge.Poly := [(nat_lit 3205, Int.ofNat (nat_lit 1))]
theorem atom1566Coded_decode : atom1566 = SparsePolynomial.decodeCubic 24 atom1566Coded := by decide +kernel
theorem atom1566Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) := by
  have h := atom1566_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1566Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1567 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1567 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1567 = ((g 5) * (g 13) * (g 14)) := by
  norm_num [atom1567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1567_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (256062342412800 : Int) atom1567) := by
  rw [SparsePolynomial.eval_scale, eval_atom1567]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1567Coded : CoefficientMerge.Poly := [(nat_lit 3206, Int.ofNat (nat_lit 1))]
theorem atom1567Coded_decode : atom1567 = SparsePolynomial.decodeCubic 24 atom1567Coded := by decide +kernel
theorem atom1567Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) := by
  have h := atom1567_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1567Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1568 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1568 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1568 = ((g 5) * (g 13) * (g 15)) := by
  norm_num [atom1568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1568_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (249067029657600 : Int) atom1568) := by
  rw [SparsePolynomial.eval_scale, eval_atom1568]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1568Coded : CoefficientMerge.Poly := [(nat_lit 3207, Int.ofNat (nat_lit 1))]
theorem atom1568Coded_decode : atom1568 = SparsePolynomial.decodeCubic 24 atom1568Coded := by decide +kernel
theorem atom1568Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded) := by
  have h := atom1568_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1568Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block021 : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 32355227510496)), (nat_lit 3066, Int.ofNat (nat_lit 43745229153648)), (nat_lit 3067, Int.ofNat (nat_lit 56706432921600)), (nat_lit 3068, Int.ofNat (nat_lit 76377038711952)), (nat_lit 3069, Int.ofNat (nat_lit 133755104320728)), (nat_lit 3070, Int.ofNat (nat_lit 191133169929504)), (nat_lit 3071, Int.ofNat (nat_lit 252374959277892)), (nat_lit 3080, Int.ofNat (nat_lit 30617742364704)), (nat_lit 3081, Int.ofNat (nat_lit 48899114252208)), (nat_lit 3082, Int.ofNat (nat_lit 21675381235200)), (nat_lit 3083, Int.ofNat (nat_lit 31085474131008)), (nat_lit 3084, Int.ofNat (nat_lit 58922406959328)), (nat_lit 3085, Int.ofNat (nat_lit 53259267609504)), (nat_lit 3086, Int.ofNat (nat_lit 43921865443104)), (nat_lit 3087, Int.ofNat (nat_lit 50109208943904)), (nat_lit 3088, Int.ofNat (nat_lit 56296552444704)), (nat_lit 3089, Int.ofNat (nat_lit 62483895945504)), (nat_lit 3090, Int.ofNat (nat_lit 76832947703952)), (nat_lit 3091, Int.ofNat (nat_lit 96207152025600)), (nat_lit 3092, Int.ofNat (nat_lit 122290758369648)), (nat_lit 3093, Int.ofNat (nat_lit 193758103116072)), (nat_lit 3094, Int.ofNat (nat_lit 265225447862496)), (nat_lit 3095, Int.ofNat (nat_lit 340940705202108)), (nat_lit 3105, Int.ofNat (nat_lit 50132370389904)), (nat_lit 3106, Int.ofNat (nat_lit 73000342255104)), (nat_lit 3107, Int.ofNat (nat_lit 60389198950608)), (nat_lit 3108, Int.ofNat (nat_lit 91330434703728)), (nat_lit 3109, Int.ofNat (nat_lit 82605517126704)), (nat_lit 3110, Int.ofNat (nat_lit 73289377309104)), (nat_lit 3111, Int.ofNat (nat_lit 79497983158704)), (nat_lit 3112, Int.ofNat (nat_lit 85706589008304)), (nat_lit 3113, Int.ofNat (nat_lit 91915194857904)), (nat_lit 3114, Int.ofNat (nat_lit 110304175786200)), (nat_lit 3115, Int.ofNat (nat_lit 135921777108480)), (nat_lit 3116, Int.ofNat (nat_lit 168248780453160)), (nat_lit 3117, Int.ofNat (nat_lit 249458858366652)), (nat_lit 3118, Int.ofNat (nat_lit 330668936280144)), (nat_lit 3119, Int.ofNat (nat_lit 415673127039258)), (nat_lit 3130, Int.ofNat (nat_lit 54718970367600)), (nat_lit 3131, Int.ofNat (nat_lit 103035403280304)), (nat_lit 3132, Int.ofNat (nat_lit 129894268063824)), (nat_lit 3133, Int.ofNat (nat_lit 123253060669200)), (nat_lit 3134, Int.ofNat (nat_lit 112937590458000)), (nat_lit 3135, Int.ofNat (nat_lit 118146865914000)), (nat_lit 3136, Int.ofNat (nat_lit 123356141370000)), (nat_lit 3137, Int.ofNat (nat_lit 128565416826000)), (nat_lit 3138, Int.ofNat (nat_lit 154777723324488)), (nat_lit 3139, Int.ofNat (nat_lit 186951414228480)), (nat_lit 3140, Int.ofNat (nat_lit 225834507154872)), (nat_lit 3141, Int.ofNat (nat_lit 306021256696980)), (nat_lit 3142, Int.ofNat (nat_lit 386208006239088)), (nat_lit 3143, Int.ofNat (nat_lit 467666395638750)), (nat_lit 3155, Int.ofNat (nat_lit 86333512567104)), (nat_lit 3156, Int.ofNat (nat_lit 177727995707328)), (nat_lit 3157, Int.ofNat (nat_lit 165983824600704)), (nat_lit 3158, Int.ofNat (nat_lit 150565390677504)), (nat_lit 3159, Int.ofNat (nat_lit 150671702421504)), (nat_lit 3160, Int.ofNat (nat_lit 153861054741504)), (nat_lit 3161, Int.ofNat (nat_lit 157050407061504)), (nat_lit 3162, Int.ofNat (nat_lit 198462683884608)), (nat_lit 3163, Int.ofNat (nat_lit 223083434787840)), (nat_lit 3164, Int.ofNat (nat_lit 276330381484608)), (nat_lit 3165, Int.ofNat (nat_lit 348770785600512)), (nat_lit 3166, Int.ofNat (nat_lit 431499235368960)), (nat_lit 3167, Int.ofNat (nat_lit 514227685137408)), (nat_lit 3180, Int.ofNat (nat_lit 129411562794624)), (nat_lit 3181, Int.ofNat (nat_lit 235307586628224)), (nat_lit 3182, Int.ofNat (nat_lit 219931677402624)), (nat_lit 3183, Int.ofNat (nat_lit 220080513844224)), (nat_lit 3184, Int.ofNat (nat_lit 220229350285824)), (nat_lit 3185, Int.ofNat (nat_lit 220378186727424)), (nat_lit 3186, Int.ofNat (nat_lit 284414134232448)), (nat_lit 3187, Int.ofNat (nat_lit 271093818378240)), (nat_lit 3188, Int.ofNat (nat_lit 374528944741248)), (nat_lit 3189, Int.ofNat (nat_lit 372227408796672)), (nat_lit 3190, Int.ofNat (nat_lit 439600190261760)), (nat_lit 3191, Int.ofNat (nat_lit 506972971726848)), (nat_lit 3205, Int.ofNat (nat_lit 143913103488000)), (nat_lit 3206, Int.ofNat (nat_lit 256062342412800)), (nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
def block021_data_flat000 : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 32355227510496))]
theorem block021_data_flat000_step : block021_data_flat000 = (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) := by decide +kernel
theorem block021_data_flat000_original : block021_data_flat000 = (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) := by
  rw [block021_data_flat000_step]
def block021_data_flat001 : CoefficientMerge.Poly := [(nat_lit 3066, Int.ofNat (nat_lit 43745229153648))]
theorem block021_data_flat001_step : block021_data_flat001 = (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded) := by decide +kernel
theorem block021_data_flat001_original : block021_data_flat001 = (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded) := by
  rw [block021_data_flat001_step]
def block021_data_flat002 : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 32355227510496)), (nat_lit 3066, Int.ofNat (nat_lit 43745229153648))]
theorem block021_data_flat002_step : block021_data_flat002 = (CoefficientMerge.fastMerge block021_data_flat000 block021_data_flat001) := by decide +kernel
theorem block021_data_flat002_original : block021_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded)) := by
  rw [block021_data_flat002_step, block021_data_flat000_original, block021_data_flat001_original]
def block021_data_flat003 : CoefficientMerge.Poly := [(nat_lit 3067, Int.ofNat (nat_lit 56706432921600))]
theorem block021_data_flat003_step : block021_data_flat003 = (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) := by decide +kernel
theorem block021_data_flat003_original : block021_data_flat003 = (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) := by
  rw [block021_data_flat003_step]
def block021_data_flat004 : CoefficientMerge.Poly := [(nat_lit 3068, Int.ofNat (nat_lit 76377038711952))]
theorem block021_data_flat004_step : block021_data_flat004 = (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) := by decide +kernel
theorem block021_data_flat004_original : block021_data_flat004 = (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) := by
  rw [block021_data_flat004_step]
def block021_data_flat005 : CoefficientMerge.Poly := [(nat_lit 3069, Int.ofNat (nat_lit 133755104320728))]
theorem block021_data_flat005_step : block021_data_flat005 = (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded) := by decide +kernel
theorem block021_data_flat005_original : block021_data_flat005 = (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded) := by
  rw [block021_data_flat005_step]
def block021_data_flat006 : CoefficientMerge.Poly := [(nat_lit 3068, Int.ofNat (nat_lit 76377038711952)), (nat_lit 3069, Int.ofNat (nat_lit 133755104320728))]
theorem block021_data_flat006_step : block021_data_flat006 = (CoefficientMerge.fastMerge block021_data_flat004 block021_data_flat005) := by decide +kernel
theorem block021_data_flat006_original : block021_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded)) := by
  rw [block021_data_flat006_step, block021_data_flat004_original, block021_data_flat005_original]
def block021_data_flat007 : CoefficientMerge.Poly := [(nat_lit 3067, Int.ofNat (nat_lit 56706432921600)), (nat_lit 3068, Int.ofNat (nat_lit 76377038711952)), (nat_lit 3069, Int.ofNat (nat_lit 133755104320728))]
theorem block021_data_flat007_step : block021_data_flat007 = (CoefficientMerge.fastMerge block021_data_flat003 block021_data_flat006) := by decide +kernel
theorem block021_data_flat007_original : block021_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded))) := by
  rw [block021_data_flat007_step, block021_data_flat003_original, block021_data_flat006_original]
def block021_data_flat008 : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 32355227510496)), (nat_lit 3066, Int.ofNat (nat_lit 43745229153648)), (nat_lit 3067, Int.ofNat (nat_lit 56706432921600)), (nat_lit 3068, Int.ofNat (nat_lit 76377038711952)), (nat_lit 3069, Int.ofNat (nat_lit 133755104320728))]
theorem block021_data_flat008_step : block021_data_flat008 = (CoefficientMerge.fastMerge block021_data_flat002 block021_data_flat007) := by decide +kernel
theorem block021_data_flat008_original : block021_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded)))) := by
  rw [block021_data_flat008_step, block021_data_flat002_original, block021_data_flat007_original]
def block021_data_flat009 : CoefficientMerge.Poly := [(nat_lit 3070, Int.ofNat (nat_lit 191133169929504))]
theorem block021_data_flat009_step : block021_data_flat009 = (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) := by decide +kernel
theorem block021_data_flat009_original : block021_data_flat009 = (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) := by
  rw [block021_data_flat009_step]
def block021_data_flat010 : CoefficientMerge.Poly := [(nat_lit 3071, Int.ofNat (nat_lit 252374959277892))]
theorem block021_data_flat010_step : block021_data_flat010 = (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded) := by decide +kernel
theorem block021_data_flat010_original : block021_data_flat010 = (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded) := by
  rw [block021_data_flat010_step]
def block021_data_flat011 : CoefficientMerge.Poly := [(nat_lit 3070, Int.ofNat (nat_lit 191133169929504)), (nat_lit 3071, Int.ofNat (nat_lit 252374959277892))]
theorem block021_data_flat011_step : block021_data_flat011 = (CoefficientMerge.fastMerge block021_data_flat009 block021_data_flat010) := by decide +kernel
theorem block021_data_flat011_original : block021_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded)) := by
  rw [block021_data_flat011_step, block021_data_flat009_original, block021_data_flat010_original]
def block021_data_flat012 : CoefficientMerge.Poly := [(nat_lit 3080, Int.ofNat (nat_lit 30617742364704))]
theorem block021_data_flat012_step : block021_data_flat012 = (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) := by decide +kernel
theorem block021_data_flat012_original : block021_data_flat012 = (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) := by
  rw [block021_data_flat012_step]
def block021_data_flat013 : CoefficientMerge.Poly := [(nat_lit 3081, Int.ofNat (nat_lit 48899114252208))]
theorem block021_data_flat013_step : block021_data_flat013 = (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) := by decide +kernel
theorem block021_data_flat013_original : block021_data_flat013 = (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) := by
  rw [block021_data_flat013_step]
def block021_data_flat014 : CoefficientMerge.Poly := [(nat_lit 3082, Int.ofNat (nat_lit 21675381235200))]
theorem block021_data_flat014_step : block021_data_flat014 = (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded) := by decide +kernel
theorem block021_data_flat014_original : block021_data_flat014 = (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded) := by
  rw [block021_data_flat014_step]
def block021_data_flat015 : CoefficientMerge.Poly := [(nat_lit 3081, Int.ofNat (nat_lit 48899114252208)), (nat_lit 3082, Int.ofNat (nat_lit 21675381235200))]
theorem block021_data_flat015_step : block021_data_flat015 = (CoefficientMerge.fastMerge block021_data_flat013 block021_data_flat014) := by decide +kernel
theorem block021_data_flat015_original : block021_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded)) := by
  rw [block021_data_flat015_step, block021_data_flat013_original, block021_data_flat014_original]
def block021_data_flat016 : CoefficientMerge.Poly := [(nat_lit 3080, Int.ofNat (nat_lit 30617742364704)), (nat_lit 3081, Int.ofNat (nat_lit 48899114252208)), (nat_lit 3082, Int.ofNat (nat_lit 21675381235200))]
theorem block021_data_flat016_step : block021_data_flat016 = (CoefficientMerge.fastMerge block021_data_flat012 block021_data_flat015) := by decide +kernel
theorem block021_data_flat016_original : block021_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded))) := by
  rw [block021_data_flat016_step, block021_data_flat012_original, block021_data_flat015_original]
def block021_data_flat017 : CoefficientMerge.Poly := [(nat_lit 3070, Int.ofNat (nat_lit 191133169929504)), (nat_lit 3071, Int.ofNat (nat_lit 252374959277892)), (nat_lit 3080, Int.ofNat (nat_lit 30617742364704)), (nat_lit 3081, Int.ofNat (nat_lit 48899114252208)), (nat_lit 3082, Int.ofNat (nat_lit 21675381235200))]
theorem block021_data_flat017_step : block021_data_flat017 = (CoefficientMerge.fastMerge block021_data_flat011 block021_data_flat016) := by decide +kernel
theorem block021_data_flat017_original : block021_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded)))) := by
  rw [block021_data_flat017_step, block021_data_flat011_original, block021_data_flat016_original]
def block021_data_flat018 : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 32355227510496)), (nat_lit 3066, Int.ofNat (nat_lit 43745229153648)), (nat_lit 3067, Int.ofNat (nat_lit 56706432921600)), (nat_lit 3068, Int.ofNat (nat_lit 76377038711952)), (nat_lit 3069, Int.ofNat (nat_lit 133755104320728)), (nat_lit 3070, Int.ofNat (nat_lit 191133169929504)), (nat_lit 3071, Int.ofNat (nat_lit 252374959277892)), (nat_lit 3080, Int.ofNat (nat_lit 30617742364704)), (nat_lit 3081, Int.ofNat (nat_lit 48899114252208)), (nat_lit 3082, Int.ofNat (nat_lit 21675381235200))]
theorem block021_data_flat018_step : block021_data_flat018 = (CoefficientMerge.fastMerge block021_data_flat008 block021_data_flat017) := by decide +kernel
theorem block021_data_flat018_original : block021_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded))))) := by
  rw [block021_data_flat018_step, block021_data_flat008_original, block021_data_flat017_original]
def block021_data_flat019 : CoefficientMerge.Poly := [(nat_lit 3083, Int.ofNat (nat_lit 31085474131008))]
theorem block021_data_flat019_step : block021_data_flat019 = (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) := by decide +kernel
theorem block021_data_flat019_original : block021_data_flat019 = (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) := by
  rw [block021_data_flat019_step]
def block021_data_flat020 : CoefficientMerge.Poly := [(nat_lit 3084, Int.ofNat (nat_lit 58922406959328))]
theorem block021_data_flat020_step : block021_data_flat020 = (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded) := by decide +kernel
theorem block021_data_flat020_original : block021_data_flat020 = (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded) := by
  rw [block021_data_flat020_step]
def block021_data_flat021 : CoefficientMerge.Poly := [(nat_lit 3083, Int.ofNat (nat_lit 31085474131008)), (nat_lit 3084, Int.ofNat (nat_lit 58922406959328))]
theorem block021_data_flat021_step : block021_data_flat021 = (CoefficientMerge.fastMerge block021_data_flat019 block021_data_flat020) := by decide +kernel
theorem block021_data_flat021_original : block021_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded)) := by
  rw [block021_data_flat021_step, block021_data_flat019_original, block021_data_flat020_original]
def block021_data_flat022 : CoefficientMerge.Poly := [(nat_lit 3085, Int.ofNat (nat_lit 53259267609504))]
theorem block021_data_flat022_step : block021_data_flat022 = (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) := by decide +kernel
theorem block021_data_flat022_original : block021_data_flat022 = (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) := by
  rw [block021_data_flat022_step]
def block021_data_flat023 : CoefficientMerge.Poly := [(nat_lit 3086, Int.ofNat (nat_lit 43921865443104))]
theorem block021_data_flat023_step : block021_data_flat023 = (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) := by decide +kernel
theorem block021_data_flat023_original : block021_data_flat023 = (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) := by
  rw [block021_data_flat023_step]
def block021_data_flat024 : CoefficientMerge.Poly := [(nat_lit 3087, Int.ofNat (nat_lit 50109208943904))]
theorem block021_data_flat024_step : block021_data_flat024 = (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded) := by decide +kernel
theorem block021_data_flat024_original : block021_data_flat024 = (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded) := by
  rw [block021_data_flat024_step]
def block021_data_flat025 : CoefficientMerge.Poly := [(nat_lit 3086, Int.ofNat (nat_lit 43921865443104)), (nat_lit 3087, Int.ofNat (nat_lit 50109208943904))]
theorem block021_data_flat025_step : block021_data_flat025 = (CoefficientMerge.fastMerge block021_data_flat023 block021_data_flat024) := by decide +kernel
theorem block021_data_flat025_original : block021_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded)) := by
  rw [block021_data_flat025_step, block021_data_flat023_original, block021_data_flat024_original]
def block021_data_flat026 : CoefficientMerge.Poly := [(nat_lit 3085, Int.ofNat (nat_lit 53259267609504)), (nat_lit 3086, Int.ofNat (nat_lit 43921865443104)), (nat_lit 3087, Int.ofNat (nat_lit 50109208943904))]
theorem block021_data_flat026_step : block021_data_flat026 = (CoefficientMerge.fastMerge block021_data_flat022 block021_data_flat025) := by decide +kernel
theorem block021_data_flat026_original : block021_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded))) := by
  rw [block021_data_flat026_step, block021_data_flat022_original, block021_data_flat025_original]
def block021_data_flat027 : CoefficientMerge.Poly := [(nat_lit 3083, Int.ofNat (nat_lit 31085474131008)), (nat_lit 3084, Int.ofNat (nat_lit 58922406959328)), (nat_lit 3085, Int.ofNat (nat_lit 53259267609504)), (nat_lit 3086, Int.ofNat (nat_lit 43921865443104)), (nat_lit 3087, Int.ofNat (nat_lit 50109208943904))]
theorem block021_data_flat027_step : block021_data_flat027 = (CoefficientMerge.fastMerge block021_data_flat021 block021_data_flat026) := by decide +kernel
theorem block021_data_flat027_original : block021_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded)))) := by
  rw [block021_data_flat027_step, block021_data_flat021_original, block021_data_flat026_original]
def block021_data_flat028 : CoefficientMerge.Poly := [(nat_lit 3088, Int.ofNat (nat_lit 56296552444704))]
theorem block021_data_flat028_step : block021_data_flat028 = (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) := by decide +kernel
theorem block021_data_flat028_original : block021_data_flat028 = (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) := by
  rw [block021_data_flat028_step]
def block021_data_flat029 : CoefficientMerge.Poly := [(nat_lit 3089, Int.ofNat (nat_lit 62483895945504))]
theorem block021_data_flat029_step : block021_data_flat029 = (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded) := by decide +kernel
theorem block021_data_flat029_original : block021_data_flat029 = (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded) := by
  rw [block021_data_flat029_step]
def block021_data_flat030 : CoefficientMerge.Poly := [(nat_lit 3088, Int.ofNat (nat_lit 56296552444704)), (nat_lit 3089, Int.ofNat (nat_lit 62483895945504))]
theorem block021_data_flat030_step : block021_data_flat030 = (CoefficientMerge.fastMerge block021_data_flat028 block021_data_flat029) := by decide +kernel
theorem block021_data_flat030_original : block021_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded)) := by
  rw [block021_data_flat030_step, block021_data_flat028_original, block021_data_flat029_original]
def block021_data_flat031 : CoefficientMerge.Poly := [(nat_lit 3090, Int.ofNat (nat_lit 76832947703952))]
theorem block021_data_flat031_step : block021_data_flat031 = (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) := by decide +kernel
theorem block021_data_flat031_original : block021_data_flat031 = (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) := by
  rw [block021_data_flat031_step]
def block021_data_flat032 : CoefficientMerge.Poly := [(nat_lit 3091, Int.ofNat (nat_lit 96207152025600))]
theorem block021_data_flat032_step : block021_data_flat032 = (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) := by decide +kernel
theorem block021_data_flat032_original : block021_data_flat032 = (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) := by
  rw [block021_data_flat032_step]
def block021_data_flat033 : CoefficientMerge.Poly := [(nat_lit 3092, Int.ofNat (nat_lit 122290758369648))]
theorem block021_data_flat033_step : block021_data_flat033 = (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded) := by decide +kernel
theorem block021_data_flat033_original : block021_data_flat033 = (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded) := by
  rw [block021_data_flat033_step]
def block021_data_flat034 : CoefficientMerge.Poly := [(nat_lit 3091, Int.ofNat (nat_lit 96207152025600)), (nat_lit 3092, Int.ofNat (nat_lit 122290758369648))]
theorem block021_data_flat034_step : block021_data_flat034 = (CoefficientMerge.fastMerge block021_data_flat032 block021_data_flat033) := by decide +kernel
theorem block021_data_flat034_original : block021_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded)) := by
  rw [block021_data_flat034_step, block021_data_flat032_original, block021_data_flat033_original]
def block021_data_flat035 : CoefficientMerge.Poly := [(nat_lit 3090, Int.ofNat (nat_lit 76832947703952)), (nat_lit 3091, Int.ofNat (nat_lit 96207152025600)), (nat_lit 3092, Int.ofNat (nat_lit 122290758369648))]
theorem block021_data_flat035_step : block021_data_flat035 = (CoefficientMerge.fastMerge block021_data_flat031 block021_data_flat034) := by decide +kernel
theorem block021_data_flat035_original : block021_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded))) := by
  rw [block021_data_flat035_step, block021_data_flat031_original, block021_data_flat034_original]
def block021_data_flat036 : CoefficientMerge.Poly := [(nat_lit 3088, Int.ofNat (nat_lit 56296552444704)), (nat_lit 3089, Int.ofNat (nat_lit 62483895945504)), (nat_lit 3090, Int.ofNat (nat_lit 76832947703952)), (nat_lit 3091, Int.ofNat (nat_lit 96207152025600)), (nat_lit 3092, Int.ofNat (nat_lit 122290758369648))]
theorem block021_data_flat036_step : block021_data_flat036 = (CoefficientMerge.fastMerge block021_data_flat030 block021_data_flat035) := by decide +kernel
theorem block021_data_flat036_original : block021_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded)))) := by
  rw [block021_data_flat036_step, block021_data_flat030_original, block021_data_flat035_original]
def block021_data_flat037 : CoefficientMerge.Poly := [(nat_lit 3083, Int.ofNat (nat_lit 31085474131008)), (nat_lit 3084, Int.ofNat (nat_lit 58922406959328)), (nat_lit 3085, Int.ofNat (nat_lit 53259267609504)), (nat_lit 3086, Int.ofNat (nat_lit 43921865443104)), (nat_lit 3087, Int.ofNat (nat_lit 50109208943904)), (nat_lit 3088, Int.ofNat (nat_lit 56296552444704)), (nat_lit 3089, Int.ofNat (nat_lit 62483895945504)), (nat_lit 3090, Int.ofNat (nat_lit 76832947703952)), (nat_lit 3091, Int.ofNat (nat_lit 96207152025600)), (nat_lit 3092, Int.ofNat (nat_lit 122290758369648))]
theorem block021_data_flat037_step : block021_data_flat037 = (CoefficientMerge.fastMerge block021_data_flat027 block021_data_flat036) := by decide +kernel
theorem block021_data_flat037_original : block021_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded))))) := by
  rw [block021_data_flat037_step, block021_data_flat027_original, block021_data_flat036_original]
def block021_data_flat038 : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 32355227510496)), (nat_lit 3066, Int.ofNat (nat_lit 43745229153648)), (nat_lit 3067, Int.ofNat (nat_lit 56706432921600)), (nat_lit 3068, Int.ofNat (nat_lit 76377038711952)), (nat_lit 3069, Int.ofNat (nat_lit 133755104320728)), (nat_lit 3070, Int.ofNat (nat_lit 191133169929504)), (nat_lit 3071, Int.ofNat (nat_lit 252374959277892)), (nat_lit 3080, Int.ofNat (nat_lit 30617742364704)), (nat_lit 3081, Int.ofNat (nat_lit 48899114252208)), (nat_lit 3082, Int.ofNat (nat_lit 21675381235200)), (nat_lit 3083, Int.ofNat (nat_lit 31085474131008)), (nat_lit 3084, Int.ofNat (nat_lit 58922406959328)), (nat_lit 3085, Int.ofNat (nat_lit 53259267609504)), (nat_lit 3086, Int.ofNat (nat_lit 43921865443104)), (nat_lit 3087, Int.ofNat (nat_lit 50109208943904)), (nat_lit 3088, Int.ofNat (nat_lit 56296552444704)), (nat_lit 3089, Int.ofNat (nat_lit 62483895945504)), (nat_lit 3090, Int.ofNat (nat_lit 76832947703952)), (nat_lit 3091, Int.ofNat (nat_lit 96207152025600)), (nat_lit 3092, Int.ofNat (nat_lit 122290758369648))]
theorem block021_data_flat038_step : block021_data_flat038 = (CoefficientMerge.fastMerge block021_data_flat018 block021_data_flat037) := by decide +kernel
theorem block021_data_flat038_original : block021_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded)))))) := by
  rw [block021_data_flat038_step, block021_data_flat018_original, block021_data_flat037_original]
def block021_data_flat039 : CoefficientMerge.Poly := [(nat_lit 3093, Int.ofNat (nat_lit 193758103116072))]
theorem block021_data_flat039_step : block021_data_flat039 = (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) := by decide +kernel
theorem block021_data_flat039_original : block021_data_flat039 = (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) := by
  rw [block021_data_flat039_step]
def block021_data_flat040 : CoefficientMerge.Poly := [(nat_lit 3094, Int.ofNat (nat_lit 265225447862496))]
theorem block021_data_flat040_step : block021_data_flat040 = (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded) := by decide +kernel
theorem block021_data_flat040_original : block021_data_flat040 = (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded) := by
  rw [block021_data_flat040_step]
def block021_data_flat041 : CoefficientMerge.Poly := [(nat_lit 3093, Int.ofNat (nat_lit 193758103116072)), (nat_lit 3094, Int.ofNat (nat_lit 265225447862496))]
theorem block021_data_flat041_step : block021_data_flat041 = (CoefficientMerge.fastMerge block021_data_flat039 block021_data_flat040) := by decide +kernel
theorem block021_data_flat041_original : block021_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded)) := by
  rw [block021_data_flat041_step, block021_data_flat039_original, block021_data_flat040_original]
def block021_data_flat042 : CoefficientMerge.Poly := [(nat_lit 3095, Int.ofNat (nat_lit 340940705202108))]
theorem block021_data_flat042_step : block021_data_flat042 = (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) := by decide +kernel
theorem block021_data_flat042_original : block021_data_flat042 = (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) := by
  rw [block021_data_flat042_step]
def block021_data_flat043 : CoefficientMerge.Poly := [(nat_lit 3105, Int.ofNat (nat_lit 50132370389904))]
theorem block021_data_flat043_step : block021_data_flat043 = (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) := by decide +kernel
theorem block021_data_flat043_original : block021_data_flat043 = (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) := by
  rw [block021_data_flat043_step]
def block021_data_flat044 : CoefficientMerge.Poly := [(nat_lit 3106, Int.ofNat (nat_lit 73000342255104))]
theorem block021_data_flat044_step : block021_data_flat044 = (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded) := by decide +kernel
theorem block021_data_flat044_original : block021_data_flat044 = (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded) := by
  rw [block021_data_flat044_step]
def block021_data_flat045 : CoefficientMerge.Poly := [(nat_lit 3105, Int.ofNat (nat_lit 50132370389904)), (nat_lit 3106, Int.ofNat (nat_lit 73000342255104))]
theorem block021_data_flat045_step : block021_data_flat045 = (CoefficientMerge.fastMerge block021_data_flat043 block021_data_flat044) := by decide +kernel
theorem block021_data_flat045_original : block021_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded)) := by
  rw [block021_data_flat045_step, block021_data_flat043_original, block021_data_flat044_original]
def block021_data_flat046 : CoefficientMerge.Poly := [(nat_lit 3095, Int.ofNat (nat_lit 340940705202108)), (nat_lit 3105, Int.ofNat (nat_lit 50132370389904)), (nat_lit 3106, Int.ofNat (nat_lit 73000342255104))]
theorem block021_data_flat046_step : block021_data_flat046 = (CoefficientMerge.fastMerge block021_data_flat042 block021_data_flat045) := by decide +kernel
theorem block021_data_flat046_original : block021_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded))) := by
  rw [block021_data_flat046_step, block021_data_flat042_original, block021_data_flat045_original]
def block021_data_flat047 : CoefficientMerge.Poly := [(nat_lit 3093, Int.ofNat (nat_lit 193758103116072)), (nat_lit 3094, Int.ofNat (nat_lit 265225447862496)), (nat_lit 3095, Int.ofNat (nat_lit 340940705202108)), (nat_lit 3105, Int.ofNat (nat_lit 50132370389904)), (nat_lit 3106, Int.ofNat (nat_lit 73000342255104))]
theorem block021_data_flat047_step : block021_data_flat047 = (CoefficientMerge.fastMerge block021_data_flat041 block021_data_flat046) := by decide +kernel
theorem block021_data_flat047_original : block021_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded)))) := by
  rw [block021_data_flat047_step, block021_data_flat041_original, block021_data_flat046_original]
def block021_data_flat048 : CoefficientMerge.Poly := [(nat_lit 3107, Int.ofNat (nat_lit 60389198950608))]
theorem block021_data_flat048_step : block021_data_flat048 = (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) := by decide +kernel
theorem block021_data_flat048_original : block021_data_flat048 = (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) := by
  rw [block021_data_flat048_step]
def block021_data_flat049 : CoefficientMerge.Poly := [(nat_lit 3108, Int.ofNat (nat_lit 91330434703728))]
theorem block021_data_flat049_step : block021_data_flat049 = (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded) := by decide +kernel
theorem block021_data_flat049_original : block021_data_flat049 = (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded) := by
  rw [block021_data_flat049_step]
def block021_data_flat050 : CoefficientMerge.Poly := [(nat_lit 3107, Int.ofNat (nat_lit 60389198950608)), (nat_lit 3108, Int.ofNat (nat_lit 91330434703728))]
theorem block021_data_flat050_step : block021_data_flat050 = (CoefficientMerge.fastMerge block021_data_flat048 block021_data_flat049) := by decide +kernel
theorem block021_data_flat050_original : block021_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded)) := by
  rw [block021_data_flat050_step, block021_data_flat048_original, block021_data_flat049_original]
def block021_data_flat051 : CoefficientMerge.Poly := [(nat_lit 3109, Int.ofNat (nat_lit 82605517126704))]
theorem block021_data_flat051_step : block021_data_flat051 = (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) := by decide +kernel
theorem block021_data_flat051_original : block021_data_flat051 = (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) := by
  rw [block021_data_flat051_step]
def block021_data_flat052 : CoefficientMerge.Poly := [(nat_lit 3110, Int.ofNat (nat_lit 73289377309104))]
theorem block021_data_flat052_step : block021_data_flat052 = (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) := by decide +kernel
theorem block021_data_flat052_original : block021_data_flat052 = (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) := by
  rw [block021_data_flat052_step]
def block021_data_flat053 : CoefficientMerge.Poly := [(nat_lit 3111, Int.ofNat (nat_lit 79497983158704))]
theorem block021_data_flat053_step : block021_data_flat053 = (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded) := by decide +kernel
theorem block021_data_flat053_original : block021_data_flat053 = (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded) := by
  rw [block021_data_flat053_step]
def block021_data_flat054 : CoefficientMerge.Poly := [(nat_lit 3110, Int.ofNat (nat_lit 73289377309104)), (nat_lit 3111, Int.ofNat (nat_lit 79497983158704))]
theorem block021_data_flat054_step : block021_data_flat054 = (CoefficientMerge.fastMerge block021_data_flat052 block021_data_flat053) := by decide +kernel
theorem block021_data_flat054_original : block021_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded)) := by
  rw [block021_data_flat054_step, block021_data_flat052_original, block021_data_flat053_original]
def block021_data_flat055 : CoefficientMerge.Poly := [(nat_lit 3109, Int.ofNat (nat_lit 82605517126704)), (nat_lit 3110, Int.ofNat (nat_lit 73289377309104)), (nat_lit 3111, Int.ofNat (nat_lit 79497983158704))]
theorem block021_data_flat055_step : block021_data_flat055 = (CoefficientMerge.fastMerge block021_data_flat051 block021_data_flat054) := by decide +kernel
theorem block021_data_flat055_original : block021_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded))) := by
  rw [block021_data_flat055_step, block021_data_flat051_original, block021_data_flat054_original]
def block021_data_flat056 : CoefficientMerge.Poly := [(nat_lit 3107, Int.ofNat (nat_lit 60389198950608)), (nat_lit 3108, Int.ofNat (nat_lit 91330434703728)), (nat_lit 3109, Int.ofNat (nat_lit 82605517126704)), (nat_lit 3110, Int.ofNat (nat_lit 73289377309104)), (nat_lit 3111, Int.ofNat (nat_lit 79497983158704))]
theorem block021_data_flat056_step : block021_data_flat056 = (CoefficientMerge.fastMerge block021_data_flat050 block021_data_flat055) := by decide +kernel
theorem block021_data_flat056_original : block021_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded)))) := by
  rw [block021_data_flat056_step, block021_data_flat050_original, block021_data_flat055_original]
def block021_data_flat057 : CoefficientMerge.Poly := [(nat_lit 3093, Int.ofNat (nat_lit 193758103116072)), (nat_lit 3094, Int.ofNat (nat_lit 265225447862496)), (nat_lit 3095, Int.ofNat (nat_lit 340940705202108)), (nat_lit 3105, Int.ofNat (nat_lit 50132370389904)), (nat_lit 3106, Int.ofNat (nat_lit 73000342255104)), (nat_lit 3107, Int.ofNat (nat_lit 60389198950608)), (nat_lit 3108, Int.ofNat (nat_lit 91330434703728)), (nat_lit 3109, Int.ofNat (nat_lit 82605517126704)), (nat_lit 3110, Int.ofNat (nat_lit 73289377309104)), (nat_lit 3111, Int.ofNat (nat_lit 79497983158704))]
theorem block021_data_flat057_step : block021_data_flat057 = (CoefficientMerge.fastMerge block021_data_flat047 block021_data_flat056) := by decide +kernel
theorem block021_data_flat057_original : block021_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded))))) := by
  rw [block021_data_flat057_step, block021_data_flat047_original, block021_data_flat056_original]
def block021_data_flat058 : CoefficientMerge.Poly := [(nat_lit 3112, Int.ofNat (nat_lit 85706589008304))]
theorem block021_data_flat058_step : block021_data_flat058 = (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) := by decide +kernel
theorem block021_data_flat058_original : block021_data_flat058 = (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) := by
  rw [block021_data_flat058_step]
def block021_data_flat059 : CoefficientMerge.Poly := [(nat_lit 3113, Int.ofNat (nat_lit 91915194857904))]
theorem block021_data_flat059_step : block021_data_flat059 = (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded) := by decide +kernel
theorem block021_data_flat059_original : block021_data_flat059 = (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded) := by
  rw [block021_data_flat059_step]
def block021_data_flat060 : CoefficientMerge.Poly := [(nat_lit 3112, Int.ofNat (nat_lit 85706589008304)), (nat_lit 3113, Int.ofNat (nat_lit 91915194857904))]
theorem block021_data_flat060_step : block021_data_flat060 = (CoefficientMerge.fastMerge block021_data_flat058 block021_data_flat059) := by decide +kernel
theorem block021_data_flat060_original : block021_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded)) := by
  rw [block021_data_flat060_step, block021_data_flat058_original, block021_data_flat059_original]
def block021_data_flat061 : CoefficientMerge.Poly := [(nat_lit 3114, Int.ofNat (nat_lit 110304175786200))]
theorem block021_data_flat061_step : block021_data_flat061 = (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) := by decide +kernel
theorem block021_data_flat061_original : block021_data_flat061 = (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) := by
  rw [block021_data_flat061_step]
def block021_data_flat062 : CoefficientMerge.Poly := [(nat_lit 3115, Int.ofNat (nat_lit 135921777108480))]
theorem block021_data_flat062_step : block021_data_flat062 = (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) := by decide +kernel
theorem block021_data_flat062_original : block021_data_flat062 = (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) := by
  rw [block021_data_flat062_step]
def block021_data_flat063 : CoefficientMerge.Poly := [(nat_lit 3116, Int.ofNat (nat_lit 168248780453160))]
theorem block021_data_flat063_step : block021_data_flat063 = (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded) := by decide +kernel
theorem block021_data_flat063_original : block021_data_flat063 = (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded) := by
  rw [block021_data_flat063_step]
def block021_data_flat064 : CoefficientMerge.Poly := [(nat_lit 3115, Int.ofNat (nat_lit 135921777108480)), (nat_lit 3116, Int.ofNat (nat_lit 168248780453160))]
theorem block021_data_flat064_step : block021_data_flat064 = (CoefficientMerge.fastMerge block021_data_flat062 block021_data_flat063) := by decide +kernel
theorem block021_data_flat064_original : block021_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded)) := by
  rw [block021_data_flat064_step, block021_data_flat062_original, block021_data_flat063_original]
def block021_data_flat065 : CoefficientMerge.Poly := [(nat_lit 3114, Int.ofNat (nat_lit 110304175786200)), (nat_lit 3115, Int.ofNat (nat_lit 135921777108480)), (nat_lit 3116, Int.ofNat (nat_lit 168248780453160))]
theorem block021_data_flat065_step : block021_data_flat065 = (CoefficientMerge.fastMerge block021_data_flat061 block021_data_flat064) := by decide +kernel
theorem block021_data_flat065_original : block021_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded))) := by
  rw [block021_data_flat065_step, block021_data_flat061_original, block021_data_flat064_original]
def block021_data_flat066 : CoefficientMerge.Poly := [(nat_lit 3112, Int.ofNat (nat_lit 85706589008304)), (nat_lit 3113, Int.ofNat (nat_lit 91915194857904)), (nat_lit 3114, Int.ofNat (nat_lit 110304175786200)), (nat_lit 3115, Int.ofNat (nat_lit 135921777108480)), (nat_lit 3116, Int.ofNat (nat_lit 168248780453160))]
theorem block021_data_flat066_step : block021_data_flat066 = (CoefficientMerge.fastMerge block021_data_flat060 block021_data_flat065) := by decide +kernel
theorem block021_data_flat066_original : block021_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded)))) := by
  rw [block021_data_flat066_step, block021_data_flat060_original, block021_data_flat065_original]
def block021_data_flat067 : CoefficientMerge.Poly := [(nat_lit 3117, Int.ofNat (nat_lit 249458858366652))]
theorem block021_data_flat067_step : block021_data_flat067 = (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) := by decide +kernel
theorem block021_data_flat067_original : block021_data_flat067 = (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) := by
  rw [block021_data_flat067_step]
def block021_data_flat068 : CoefficientMerge.Poly := [(nat_lit 3118, Int.ofNat (nat_lit 330668936280144))]
theorem block021_data_flat068_step : block021_data_flat068 = (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded) := by decide +kernel
theorem block021_data_flat068_original : block021_data_flat068 = (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded) := by
  rw [block021_data_flat068_step]
def block021_data_flat069 : CoefficientMerge.Poly := [(nat_lit 3117, Int.ofNat (nat_lit 249458858366652)), (nat_lit 3118, Int.ofNat (nat_lit 330668936280144))]
theorem block021_data_flat069_step : block021_data_flat069 = (CoefficientMerge.fastMerge block021_data_flat067 block021_data_flat068) := by decide +kernel
theorem block021_data_flat069_original : block021_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded)) := by
  rw [block021_data_flat069_step, block021_data_flat067_original, block021_data_flat068_original]
def block021_data_flat070 : CoefficientMerge.Poly := [(nat_lit 3119, Int.ofNat (nat_lit 415673127039258))]
theorem block021_data_flat070_step : block021_data_flat070 = (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) := by decide +kernel
theorem block021_data_flat070_original : block021_data_flat070 = (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) := by
  rw [block021_data_flat070_step]
def block021_data_flat071 : CoefficientMerge.Poly := [(nat_lit 3130, Int.ofNat (nat_lit 54718970367600))]
theorem block021_data_flat071_step : block021_data_flat071 = (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) := by decide +kernel
theorem block021_data_flat071_original : block021_data_flat071 = (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) := by
  rw [block021_data_flat071_step]
def block021_data_flat072 : CoefficientMerge.Poly := [(nat_lit 3131, Int.ofNat (nat_lit 103035403280304))]
theorem block021_data_flat072_step : block021_data_flat072 = (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded) := by decide +kernel
theorem block021_data_flat072_original : block021_data_flat072 = (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded) := by
  rw [block021_data_flat072_step]
def block021_data_flat073 : CoefficientMerge.Poly := [(nat_lit 3130, Int.ofNat (nat_lit 54718970367600)), (nat_lit 3131, Int.ofNat (nat_lit 103035403280304))]
theorem block021_data_flat073_step : block021_data_flat073 = (CoefficientMerge.fastMerge block021_data_flat071 block021_data_flat072) := by decide +kernel
theorem block021_data_flat073_original : block021_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded)) := by
  rw [block021_data_flat073_step, block021_data_flat071_original, block021_data_flat072_original]
def block021_data_flat074 : CoefficientMerge.Poly := [(nat_lit 3119, Int.ofNat (nat_lit 415673127039258)), (nat_lit 3130, Int.ofNat (nat_lit 54718970367600)), (nat_lit 3131, Int.ofNat (nat_lit 103035403280304))]
theorem block021_data_flat074_step : block021_data_flat074 = (CoefficientMerge.fastMerge block021_data_flat070 block021_data_flat073) := by decide +kernel
theorem block021_data_flat074_original : block021_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded))) := by
  rw [block021_data_flat074_step, block021_data_flat070_original, block021_data_flat073_original]
def block021_data_flat075 : CoefficientMerge.Poly := [(nat_lit 3117, Int.ofNat (nat_lit 249458858366652)), (nat_lit 3118, Int.ofNat (nat_lit 330668936280144)), (nat_lit 3119, Int.ofNat (nat_lit 415673127039258)), (nat_lit 3130, Int.ofNat (nat_lit 54718970367600)), (nat_lit 3131, Int.ofNat (nat_lit 103035403280304))]
theorem block021_data_flat075_step : block021_data_flat075 = (CoefficientMerge.fastMerge block021_data_flat069 block021_data_flat074) := by decide +kernel
theorem block021_data_flat075_original : block021_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded)))) := by
  rw [block021_data_flat075_step, block021_data_flat069_original, block021_data_flat074_original]
def block021_data_flat076 : CoefficientMerge.Poly := [(nat_lit 3112, Int.ofNat (nat_lit 85706589008304)), (nat_lit 3113, Int.ofNat (nat_lit 91915194857904)), (nat_lit 3114, Int.ofNat (nat_lit 110304175786200)), (nat_lit 3115, Int.ofNat (nat_lit 135921777108480)), (nat_lit 3116, Int.ofNat (nat_lit 168248780453160)), (nat_lit 3117, Int.ofNat (nat_lit 249458858366652)), (nat_lit 3118, Int.ofNat (nat_lit 330668936280144)), (nat_lit 3119, Int.ofNat (nat_lit 415673127039258)), (nat_lit 3130, Int.ofNat (nat_lit 54718970367600)), (nat_lit 3131, Int.ofNat (nat_lit 103035403280304))]
theorem block021_data_flat076_step : block021_data_flat076 = (CoefficientMerge.fastMerge block021_data_flat066 block021_data_flat075) := by decide +kernel
theorem block021_data_flat076_original : block021_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded))))) := by
  rw [block021_data_flat076_step, block021_data_flat066_original, block021_data_flat075_original]
def block021_data_flat077 : CoefficientMerge.Poly := [(nat_lit 3093, Int.ofNat (nat_lit 193758103116072)), (nat_lit 3094, Int.ofNat (nat_lit 265225447862496)), (nat_lit 3095, Int.ofNat (nat_lit 340940705202108)), (nat_lit 3105, Int.ofNat (nat_lit 50132370389904)), (nat_lit 3106, Int.ofNat (nat_lit 73000342255104)), (nat_lit 3107, Int.ofNat (nat_lit 60389198950608)), (nat_lit 3108, Int.ofNat (nat_lit 91330434703728)), (nat_lit 3109, Int.ofNat (nat_lit 82605517126704)), (nat_lit 3110, Int.ofNat (nat_lit 73289377309104)), (nat_lit 3111, Int.ofNat (nat_lit 79497983158704)), (nat_lit 3112, Int.ofNat (nat_lit 85706589008304)), (nat_lit 3113, Int.ofNat (nat_lit 91915194857904)), (nat_lit 3114, Int.ofNat (nat_lit 110304175786200)), (nat_lit 3115, Int.ofNat (nat_lit 135921777108480)), (nat_lit 3116, Int.ofNat (nat_lit 168248780453160)), (nat_lit 3117, Int.ofNat (nat_lit 249458858366652)), (nat_lit 3118, Int.ofNat (nat_lit 330668936280144)), (nat_lit 3119, Int.ofNat (nat_lit 415673127039258)), (nat_lit 3130, Int.ofNat (nat_lit 54718970367600)), (nat_lit 3131, Int.ofNat (nat_lit 103035403280304))]
theorem block021_data_flat077_step : block021_data_flat077 = (CoefficientMerge.fastMerge block021_data_flat057 block021_data_flat076) := by decide +kernel
theorem block021_data_flat077_original : block021_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded)))))) := by
  rw [block021_data_flat077_step, block021_data_flat057_original, block021_data_flat076_original]
def block021_data_flat078 : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 32355227510496)), (nat_lit 3066, Int.ofNat (nat_lit 43745229153648)), (nat_lit 3067, Int.ofNat (nat_lit 56706432921600)), (nat_lit 3068, Int.ofNat (nat_lit 76377038711952)), (nat_lit 3069, Int.ofNat (nat_lit 133755104320728)), (nat_lit 3070, Int.ofNat (nat_lit 191133169929504)), (nat_lit 3071, Int.ofNat (nat_lit 252374959277892)), (nat_lit 3080, Int.ofNat (nat_lit 30617742364704)), (nat_lit 3081, Int.ofNat (nat_lit 48899114252208)), (nat_lit 3082, Int.ofNat (nat_lit 21675381235200)), (nat_lit 3083, Int.ofNat (nat_lit 31085474131008)), (nat_lit 3084, Int.ofNat (nat_lit 58922406959328)), (nat_lit 3085, Int.ofNat (nat_lit 53259267609504)), (nat_lit 3086, Int.ofNat (nat_lit 43921865443104)), (nat_lit 3087, Int.ofNat (nat_lit 50109208943904)), (nat_lit 3088, Int.ofNat (nat_lit 56296552444704)), (nat_lit 3089, Int.ofNat (nat_lit 62483895945504)), (nat_lit 3090, Int.ofNat (nat_lit 76832947703952)), (nat_lit 3091, Int.ofNat (nat_lit 96207152025600)), (nat_lit 3092, Int.ofNat (nat_lit 122290758369648)), (nat_lit 3093, Int.ofNat (nat_lit 193758103116072)), (nat_lit 3094, Int.ofNat (nat_lit 265225447862496)), (nat_lit 3095, Int.ofNat (nat_lit 340940705202108)), (nat_lit 3105, Int.ofNat (nat_lit 50132370389904)), (nat_lit 3106, Int.ofNat (nat_lit 73000342255104)), (nat_lit 3107, Int.ofNat (nat_lit 60389198950608)), (nat_lit 3108, Int.ofNat (nat_lit 91330434703728)), (nat_lit 3109, Int.ofNat (nat_lit 82605517126704)), (nat_lit 3110, Int.ofNat (nat_lit 73289377309104)), (nat_lit 3111, Int.ofNat (nat_lit 79497983158704)), (nat_lit 3112, Int.ofNat (nat_lit 85706589008304)), (nat_lit 3113, Int.ofNat (nat_lit 91915194857904)), (nat_lit 3114, Int.ofNat (nat_lit 110304175786200)), (nat_lit 3115, Int.ofNat (nat_lit 135921777108480)), (nat_lit 3116, Int.ofNat (nat_lit 168248780453160)), (nat_lit 3117, Int.ofNat (nat_lit 249458858366652)), (nat_lit 3118, Int.ofNat (nat_lit 330668936280144)), (nat_lit 3119, Int.ofNat (nat_lit 415673127039258)), (nat_lit 3130, Int.ofNat (nat_lit 54718970367600)), (nat_lit 3131, Int.ofNat (nat_lit 103035403280304))]
theorem block021_data_flat078_step : block021_data_flat078 = (CoefficientMerge.fastMerge block021_data_flat038 block021_data_flat077) := by decide +kernel
theorem block021_data_flat078_original : block021_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded))))))) := by
  rw [block021_data_flat078_step, block021_data_flat038_original, block021_data_flat077_original]
def block021_data_flat079 : CoefficientMerge.Poly := [(nat_lit 3132, Int.ofNat (nat_lit 129894268063824))]
theorem block021_data_flat079_step : block021_data_flat079 = (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) := by decide +kernel
theorem block021_data_flat079_original : block021_data_flat079 = (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) := by
  rw [block021_data_flat079_step]
def block021_data_flat080 : CoefficientMerge.Poly := [(nat_lit 3133, Int.ofNat (nat_lit 123253060669200))]
theorem block021_data_flat080_step : block021_data_flat080 = (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded) := by decide +kernel
theorem block021_data_flat080_original : block021_data_flat080 = (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded) := by
  rw [block021_data_flat080_step]
def block021_data_flat081 : CoefficientMerge.Poly := [(nat_lit 3132, Int.ofNat (nat_lit 129894268063824)), (nat_lit 3133, Int.ofNat (nat_lit 123253060669200))]
theorem block021_data_flat081_step : block021_data_flat081 = (CoefficientMerge.fastMerge block021_data_flat079 block021_data_flat080) := by decide +kernel
theorem block021_data_flat081_original : block021_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded)) := by
  rw [block021_data_flat081_step, block021_data_flat079_original, block021_data_flat080_original]
def block021_data_flat082 : CoefficientMerge.Poly := [(nat_lit 3134, Int.ofNat (nat_lit 112937590458000))]
theorem block021_data_flat082_step : block021_data_flat082 = (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) := by decide +kernel
theorem block021_data_flat082_original : block021_data_flat082 = (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) := by
  rw [block021_data_flat082_step]
def block021_data_flat083 : CoefficientMerge.Poly := [(nat_lit 3135, Int.ofNat (nat_lit 118146865914000))]
theorem block021_data_flat083_step : block021_data_flat083 = (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) := by decide +kernel
theorem block021_data_flat083_original : block021_data_flat083 = (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) := by
  rw [block021_data_flat083_step]
def block021_data_flat084 : CoefficientMerge.Poly := [(nat_lit 3136, Int.ofNat (nat_lit 123356141370000))]
theorem block021_data_flat084_step : block021_data_flat084 = (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded) := by decide +kernel
theorem block021_data_flat084_original : block021_data_flat084 = (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded) := by
  rw [block021_data_flat084_step]
def block021_data_flat085 : CoefficientMerge.Poly := [(nat_lit 3135, Int.ofNat (nat_lit 118146865914000)), (nat_lit 3136, Int.ofNat (nat_lit 123356141370000))]
theorem block021_data_flat085_step : block021_data_flat085 = (CoefficientMerge.fastMerge block021_data_flat083 block021_data_flat084) := by decide +kernel
theorem block021_data_flat085_original : block021_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded)) := by
  rw [block021_data_flat085_step, block021_data_flat083_original, block021_data_flat084_original]
def block021_data_flat086 : CoefficientMerge.Poly := [(nat_lit 3134, Int.ofNat (nat_lit 112937590458000)), (nat_lit 3135, Int.ofNat (nat_lit 118146865914000)), (nat_lit 3136, Int.ofNat (nat_lit 123356141370000))]
theorem block021_data_flat086_step : block021_data_flat086 = (CoefficientMerge.fastMerge block021_data_flat082 block021_data_flat085) := by decide +kernel
theorem block021_data_flat086_original : block021_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded))) := by
  rw [block021_data_flat086_step, block021_data_flat082_original, block021_data_flat085_original]
def block021_data_flat087 : CoefficientMerge.Poly := [(nat_lit 3132, Int.ofNat (nat_lit 129894268063824)), (nat_lit 3133, Int.ofNat (nat_lit 123253060669200)), (nat_lit 3134, Int.ofNat (nat_lit 112937590458000)), (nat_lit 3135, Int.ofNat (nat_lit 118146865914000)), (nat_lit 3136, Int.ofNat (nat_lit 123356141370000))]
theorem block021_data_flat087_step : block021_data_flat087 = (CoefficientMerge.fastMerge block021_data_flat081 block021_data_flat086) := by decide +kernel
theorem block021_data_flat087_original : block021_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded)))) := by
  rw [block021_data_flat087_step, block021_data_flat081_original, block021_data_flat086_original]
def block021_data_flat088 : CoefficientMerge.Poly := [(nat_lit 3137, Int.ofNat (nat_lit 128565416826000))]
theorem block021_data_flat088_step : block021_data_flat088 = (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) := by decide +kernel
theorem block021_data_flat088_original : block021_data_flat088 = (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) := by
  rw [block021_data_flat088_step]
def block021_data_flat089 : CoefficientMerge.Poly := [(nat_lit 3138, Int.ofNat (nat_lit 154777723324488))]
theorem block021_data_flat089_step : block021_data_flat089 = (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded) := by decide +kernel
theorem block021_data_flat089_original : block021_data_flat089 = (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded) := by
  rw [block021_data_flat089_step]
def block021_data_flat090 : CoefficientMerge.Poly := [(nat_lit 3137, Int.ofNat (nat_lit 128565416826000)), (nat_lit 3138, Int.ofNat (nat_lit 154777723324488))]
theorem block021_data_flat090_step : block021_data_flat090 = (CoefficientMerge.fastMerge block021_data_flat088 block021_data_flat089) := by decide +kernel
theorem block021_data_flat090_original : block021_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded)) := by
  rw [block021_data_flat090_step, block021_data_flat088_original, block021_data_flat089_original]
def block021_data_flat091 : CoefficientMerge.Poly := [(nat_lit 3139, Int.ofNat (nat_lit 186951414228480))]
theorem block021_data_flat091_step : block021_data_flat091 = (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) := by decide +kernel
theorem block021_data_flat091_original : block021_data_flat091 = (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) := by
  rw [block021_data_flat091_step]
def block021_data_flat092 : CoefficientMerge.Poly := [(nat_lit 3140, Int.ofNat (nat_lit 225834507154872))]
theorem block021_data_flat092_step : block021_data_flat092 = (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) := by decide +kernel
theorem block021_data_flat092_original : block021_data_flat092 = (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) := by
  rw [block021_data_flat092_step]
def block021_data_flat093 : CoefficientMerge.Poly := [(nat_lit 3141, Int.ofNat (nat_lit 306021256696980))]
theorem block021_data_flat093_step : block021_data_flat093 = (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded) := by decide +kernel
theorem block021_data_flat093_original : block021_data_flat093 = (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded) := by
  rw [block021_data_flat093_step]
def block021_data_flat094 : CoefficientMerge.Poly := [(nat_lit 3140, Int.ofNat (nat_lit 225834507154872)), (nat_lit 3141, Int.ofNat (nat_lit 306021256696980))]
theorem block021_data_flat094_step : block021_data_flat094 = (CoefficientMerge.fastMerge block021_data_flat092 block021_data_flat093) := by decide +kernel
theorem block021_data_flat094_original : block021_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded)) := by
  rw [block021_data_flat094_step, block021_data_flat092_original, block021_data_flat093_original]
def block021_data_flat095 : CoefficientMerge.Poly := [(nat_lit 3139, Int.ofNat (nat_lit 186951414228480)), (nat_lit 3140, Int.ofNat (nat_lit 225834507154872)), (nat_lit 3141, Int.ofNat (nat_lit 306021256696980))]
theorem block021_data_flat095_step : block021_data_flat095 = (CoefficientMerge.fastMerge block021_data_flat091 block021_data_flat094) := by decide +kernel
theorem block021_data_flat095_original : block021_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded))) := by
  rw [block021_data_flat095_step, block021_data_flat091_original, block021_data_flat094_original]
def block021_data_flat096 : CoefficientMerge.Poly := [(nat_lit 3137, Int.ofNat (nat_lit 128565416826000)), (nat_lit 3138, Int.ofNat (nat_lit 154777723324488)), (nat_lit 3139, Int.ofNat (nat_lit 186951414228480)), (nat_lit 3140, Int.ofNat (nat_lit 225834507154872)), (nat_lit 3141, Int.ofNat (nat_lit 306021256696980))]
theorem block021_data_flat096_step : block021_data_flat096 = (CoefficientMerge.fastMerge block021_data_flat090 block021_data_flat095) := by decide +kernel
theorem block021_data_flat096_original : block021_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded)))) := by
  rw [block021_data_flat096_step, block021_data_flat090_original, block021_data_flat095_original]
def block021_data_flat097 : CoefficientMerge.Poly := [(nat_lit 3132, Int.ofNat (nat_lit 129894268063824)), (nat_lit 3133, Int.ofNat (nat_lit 123253060669200)), (nat_lit 3134, Int.ofNat (nat_lit 112937590458000)), (nat_lit 3135, Int.ofNat (nat_lit 118146865914000)), (nat_lit 3136, Int.ofNat (nat_lit 123356141370000)), (nat_lit 3137, Int.ofNat (nat_lit 128565416826000)), (nat_lit 3138, Int.ofNat (nat_lit 154777723324488)), (nat_lit 3139, Int.ofNat (nat_lit 186951414228480)), (nat_lit 3140, Int.ofNat (nat_lit 225834507154872)), (nat_lit 3141, Int.ofNat (nat_lit 306021256696980))]
theorem block021_data_flat097_step : block021_data_flat097 = (CoefficientMerge.fastMerge block021_data_flat087 block021_data_flat096) := by decide +kernel
theorem block021_data_flat097_original : block021_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded))))) := by
  rw [block021_data_flat097_step, block021_data_flat087_original, block021_data_flat096_original]
def block021_data_flat098 : CoefficientMerge.Poly := [(nat_lit 3142, Int.ofNat (nat_lit 386208006239088))]
theorem block021_data_flat098_step : block021_data_flat098 = (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) := by decide +kernel
theorem block021_data_flat098_original : block021_data_flat098 = (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) := by
  rw [block021_data_flat098_step]
def block021_data_flat099 : CoefficientMerge.Poly := [(nat_lit 3143, Int.ofNat (nat_lit 467666395638750))]
theorem block021_data_flat099_step : block021_data_flat099 = (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded) := by decide +kernel
theorem block021_data_flat099_original : block021_data_flat099 = (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded) := by
  rw [block021_data_flat099_step]
def block021_data_flat100 : CoefficientMerge.Poly := [(nat_lit 3142, Int.ofNat (nat_lit 386208006239088)), (nat_lit 3143, Int.ofNat (nat_lit 467666395638750))]
theorem block021_data_flat100_step : block021_data_flat100 = (CoefficientMerge.fastMerge block021_data_flat098 block021_data_flat099) := by decide +kernel
theorem block021_data_flat100_original : block021_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded)) := by
  rw [block021_data_flat100_step, block021_data_flat098_original, block021_data_flat099_original]
def block021_data_flat101 : CoefficientMerge.Poly := [(nat_lit 3155, Int.ofNat (nat_lit 86333512567104))]
theorem block021_data_flat101_step : block021_data_flat101 = (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) := by decide +kernel
theorem block021_data_flat101_original : block021_data_flat101 = (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) := by
  rw [block021_data_flat101_step]
def block021_data_flat102 : CoefficientMerge.Poly := [(nat_lit 3156, Int.ofNat (nat_lit 177727995707328))]
theorem block021_data_flat102_step : block021_data_flat102 = (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) := by decide +kernel
theorem block021_data_flat102_original : block021_data_flat102 = (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) := by
  rw [block021_data_flat102_step]
def block021_data_flat103 : CoefficientMerge.Poly := [(nat_lit 3157, Int.ofNat (nat_lit 165983824600704))]
theorem block021_data_flat103_step : block021_data_flat103 = (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded) := by decide +kernel
theorem block021_data_flat103_original : block021_data_flat103 = (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded) := by
  rw [block021_data_flat103_step]
def block021_data_flat104 : CoefficientMerge.Poly := [(nat_lit 3156, Int.ofNat (nat_lit 177727995707328)), (nat_lit 3157, Int.ofNat (nat_lit 165983824600704))]
theorem block021_data_flat104_step : block021_data_flat104 = (CoefficientMerge.fastMerge block021_data_flat102 block021_data_flat103) := by decide +kernel
theorem block021_data_flat104_original : block021_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded)) := by
  rw [block021_data_flat104_step, block021_data_flat102_original, block021_data_flat103_original]
def block021_data_flat105 : CoefficientMerge.Poly := [(nat_lit 3155, Int.ofNat (nat_lit 86333512567104)), (nat_lit 3156, Int.ofNat (nat_lit 177727995707328)), (nat_lit 3157, Int.ofNat (nat_lit 165983824600704))]
theorem block021_data_flat105_step : block021_data_flat105 = (CoefficientMerge.fastMerge block021_data_flat101 block021_data_flat104) := by decide +kernel
theorem block021_data_flat105_original : block021_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded))) := by
  rw [block021_data_flat105_step, block021_data_flat101_original, block021_data_flat104_original]
def block021_data_flat106 : CoefficientMerge.Poly := [(nat_lit 3142, Int.ofNat (nat_lit 386208006239088)), (nat_lit 3143, Int.ofNat (nat_lit 467666395638750)), (nat_lit 3155, Int.ofNat (nat_lit 86333512567104)), (nat_lit 3156, Int.ofNat (nat_lit 177727995707328)), (nat_lit 3157, Int.ofNat (nat_lit 165983824600704))]
theorem block021_data_flat106_step : block021_data_flat106 = (CoefficientMerge.fastMerge block021_data_flat100 block021_data_flat105) := by decide +kernel
theorem block021_data_flat106_original : block021_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded)))) := by
  rw [block021_data_flat106_step, block021_data_flat100_original, block021_data_flat105_original]
def block021_data_flat107 : CoefficientMerge.Poly := [(nat_lit 3158, Int.ofNat (nat_lit 150565390677504))]
theorem block021_data_flat107_step : block021_data_flat107 = (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) := by decide +kernel
theorem block021_data_flat107_original : block021_data_flat107 = (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) := by
  rw [block021_data_flat107_step]
def block021_data_flat108 : CoefficientMerge.Poly := [(nat_lit 3159, Int.ofNat (nat_lit 150671702421504))]
theorem block021_data_flat108_step : block021_data_flat108 = (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded) := by decide +kernel
theorem block021_data_flat108_original : block021_data_flat108 = (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded) := by
  rw [block021_data_flat108_step]
def block021_data_flat109 : CoefficientMerge.Poly := [(nat_lit 3158, Int.ofNat (nat_lit 150565390677504)), (nat_lit 3159, Int.ofNat (nat_lit 150671702421504))]
theorem block021_data_flat109_step : block021_data_flat109 = (CoefficientMerge.fastMerge block021_data_flat107 block021_data_flat108) := by decide +kernel
theorem block021_data_flat109_original : block021_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded)) := by
  rw [block021_data_flat109_step, block021_data_flat107_original, block021_data_flat108_original]
def block021_data_flat110 : CoefficientMerge.Poly := [(nat_lit 3160, Int.ofNat (nat_lit 153861054741504))]
theorem block021_data_flat110_step : block021_data_flat110 = (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) := by decide +kernel
theorem block021_data_flat110_original : block021_data_flat110 = (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) := by
  rw [block021_data_flat110_step]
def block021_data_flat111 : CoefficientMerge.Poly := [(nat_lit 3161, Int.ofNat (nat_lit 157050407061504))]
theorem block021_data_flat111_step : block021_data_flat111 = (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) := by decide +kernel
theorem block021_data_flat111_original : block021_data_flat111 = (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) := by
  rw [block021_data_flat111_step]
def block021_data_flat112 : CoefficientMerge.Poly := [(nat_lit 3162, Int.ofNat (nat_lit 198462683884608))]
theorem block021_data_flat112_step : block021_data_flat112 = (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded) := by decide +kernel
theorem block021_data_flat112_original : block021_data_flat112 = (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded) := by
  rw [block021_data_flat112_step]
def block021_data_flat113 : CoefficientMerge.Poly := [(nat_lit 3161, Int.ofNat (nat_lit 157050407061504)), (nat_lit 3162, Int.ofNat (nat_lit 198462683884608))]
theorem block021_data_flat113_step : block021_data_flat113 = (CoefficientMerge.fastMerge block021_data_flat111 block021_data_flat112) := by decide +kernel
theorem block021_data_flat113_original : block021_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded)) := by
  rw [block021_data_flat113_step, block021_data_flat111_original, block021_data_flat112_original]
def block021_data_flat114 : CoefficientMerge.Poly := [(nat_lit 3160, Int.ofNat (nat_lit 153861054741504)), (nat_lit 3161, Int.ofNat (nat_lit 157050407061504)), (nat_lit 3162, Int.ofNat (nat_lit 198462683884608))]
theorem block021_data_flat114_step : block021_data_flat114 = (CoefficientMerge.fastMerge block021_data_flat110 block021_data_flat113) := by decide +kernel
theorem block021_data_flat114_original : block021_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded))) := by
  rw [block021_data_flat114_step, block021_data_flat110_original, block021_data_flat113_original]
def block021_data_flat115 : CoefficientMerge.Poly := [(nat_lit 3158, Int.ofNat (nat_lit 150565390677504)), (nat_lit 3159, Int.ofNat (nat_lit 150671702421504)), (nat_lit 3160, Int.ofNat (nat_lit 153861054741504)), (nat_lit 3161, Int.ofNat (nat_lit 157050407061504)), (nat_lit 3162, Int.ofNat (nat_lit 198462683884608))]
theorem block021_data_flat115_step : block021_data_flat115 = (CoefficientMerge.fastMerge block021_data_flat109 block021_data_flat114) := by decide +kernel
theorem block021_data_flat115_original : block021_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded)))) := by
  rw [block021_data_flat115_step, block021_data_flat109_original, block021_data_flat114_original]
def block021_data_flat116 : CoefficientMerge.Poly := [(nat_lit 3142, Int.ofNat (nat_lit 386208006239088)), (nat_lit 3143, Int.ofNat (nat_lit 467666395638750)), (nat_lit 3155, Int.ofNat (nat_lit 86333512567104)), (nat_lit 3156, Int.ofNat (nat_lit 177727995707328)), (nat_lit 3157, Int.ofNat (nat_lit 165983824600704)), (nat_lit 3158, Int.ofNat (nat_lit 150565390677504)), (nat_lit 3159, Int.ofNat (nat_lit 150671702421504)), (nat_lit 3160, Int.ofNat (nat_lit 153861054741504)), (nat_lit 3161, Int.ofNat (nat_lit 157050407061504)), (nat_lit 3162, Int.ofNat (nat_lit 198462683884608))]
theorem block021_data_flat116_step : block021_data_flat116 = (CoefficientMerge.fastMerge block021_data_flat106 block021_data_flat115) := by decide +kernel
theorem block021_data_flat116_original : block021_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded))))) := by
  rw [block021_data_flat116_step, block021_data_flat106_original, block021_data_flat115_original]
def block021_data_flat117 : CoefficientMerge.Poly := [(nat_lit 3132, Int.ofNat (nat_lit 129894268063824)), (nat_lit 3133, Int.ofNat (nat_lit 123253060669200)), (nat_lit 3134, Int.ofNat (nat_lit 112937590458000)), (nat_lit 3135, Int.ofNat (nat_lit 118146865914000)), (nat_lit 3136, Int.ofNat (nat_lit 123356141370000)), (nat_lit 3137, Int.ofNat (nat_lit 128565416826000)), (nat_lit 3138, Int.ofNat (nat_lit 154777723324488)), (nat_lit 3139, Int.ofNat (nat_lit 186951414228480)), (nat_lit 3140, Int.ofNat (nat_lit 225834507154872)), (nat_lit 3141, Int.ofNat (nat_lit 306021256696980)), (nat_lit 3142, Int.ofNat (nat_lit 386208006239088)), (nat_lit 3143, Int.ofNat (nat_lit 467666395638750)), (nat_lit 3155, Int.ofNat (nat_lit 86333512567104)), (nat_lit 3156, Int.ofNat (nat_lit 177727995707328)), (nat_lit 3157, Int.ofNat (nat_lit 165983824600704)), (nat_lit 3158, Int.ofNat (nat_lit 150565390677504)), (nat_lit 3159, Int.ofNat (nat_lit 150671702421504)), (nat_lit 3160, Int.ofNat (nat_lit 153861054741504)), (nat_lit 3161, Int.ofNat (nat_lit 157050407061504)), (nat_lit 3162, Int.ofNat (nat_lit 198462683884608))]
theorem block021_data_flat117_step : block021_data_flat117 = (CoefficientMerge.fastMerge block021_data_flat097 block021_data_flat116) := by decide +kernel
theorem block021_data_flat117_original : block021_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded)))))) := by
  rw [block021_data_flat117_step, block021_data_flat097_original, block021_data_flat116_original]
def block021_data_flat118 : CoefficientMerge.Poly := [(nat_lit 3163, Int.ofNat (nat_lit 223083434787840))]
theorem block021_data_flat118_step : block021_data_flat118 = (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) := by decide +kernel
theorem block021_data_flat118_original : block021_data_flat118 = (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) := by
  rw [block021_data_flat118_step]
def block021_data_flat119 : CoefficientMerge.Poly := [(nat_lit 3164, Int.ofNat (nat_lit 276330381484608))]
theorem block021_data_flat119_step : block021_data_flat119 = (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded) := by decide +kernel
theorem block021_data_flat119_original : block021_data_flat119 = (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded) := by
  rw [block021_data_flat119_step]
def block021_data_flat120 : CoefficientMerge.Poly := [(nat_lit 3163, Int.ofNat (nat_lit 223083434787840)), (nat_lit 3164, Int.ofNat (nat_lit 276330381484608))]
theorem block021_data_flat120_step : block021_data_flat120 = (CoefficientMerge.fastMerge block021_data_flat118 block021_data_flat119) := by decide +kernel
theorem block021_data_flat120_original : block021_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded)) := by
  rw [block021_data_flat120_step, block021_data_flat118_original, block021_data_flat119_original]
def block021_data_flat121 : CoefficientMerge.Poly := [(nat_lit 3165, Int.ofNat (nat_lit 348770785600512))]
theorem block021_data_flat121_step : block021_data_flat121 = (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) := by decide +kernel
theorem block021_data_flat121_original : block021_data_flat121 = (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) := by
  rw [block021_data_flat121_step]
def block021_data_flat122 : CoefficientMerge.Poly := [(nat_lit 3166, Int.ofNat (nat_lit 431499235368960))]
theorem block021_data_flat122_step : block021_data_flat122 = (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) := by decide +kernel
theorem block021_data_flat122_original : block021_data_flat122 = (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) := by
  rw [block021_data_flat122_step]
def block021_data_flat123 : CoefficientMerge.Poly := [(nat_lit 3167, Int.ofNat (nat_lit 514227685137408))]
theorem block021_data_flat123_step : block021_data_flat123 = (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded) := by decide +kernel
theorem block021_data_flat123_original : block021_data_flat123 = (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded) := by
  rw [block021_data_flat123_step]
def block021_data_flat124 : CoefficientMerge.Poly := [(nat_lit 3166, Int.ofNat (nat_lit 431499235368960)), (nat_lit 3167, Int.ofNat (nat_lit 514227685137408))]
theorem block021_data_flat124_step : block021_data_flat124 = (CoefficientMerge.fastMerge block021_data_flat122 block021_data_flat123) := by decide +kernel
theorem block021_data_flat124_original : block021_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded)) := by
  rw [block021_data_flat124_step, block021_data_flat122_original, block021_data_flat123_original]
def block021_data_flat125 : CoefficientMerge.Poly := [(nat_lit 3165, Int.ofNat (nat_lit 348770785600512)), (nat_lit 3166, Int.ofNat (nat_lit 431499235368960)), (nat_lit 3167, Int.ofNat (nat_lit 514227685137408))]
theorem block021_data_flat125_step : block021_data_flat125 = (CoefficientMerge.fastMerge block021_data_flat121 block021_data_flat124) := by decide +kernel
theorem block021_data_flat125_original : block021_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded))) := by
  rw [block021_data_flat125_step, block021_data_flat121_original, block021_data_flat124_original]
def block021_data_flat126 : CoefficientMerge.Poly := [(nat_lit 3163, Int.ofNat (nat_lit 223083434787840)), (nat_lit 3164, Int.ofNat (nat_lit 276330381484608)), (nat_lit 3165, Int.ofNat (nat_lit 348770785600512)), (nat_lit 3166, Int.ofNat (nat_lit 431499235368960)), (nat_lit 3167, Int.ofNat (nat_lit 514227685137408))]
theorem block021_data_flat126_step : block021_data_flat126 = (CoefficientMerge.fastMerge block021_data_flat120 block021_data_flat125) := by decide +kernel
theorem block021_data_flat126_original : block021_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded)))) := by
  rw [block021_data_flat126_step, block021_data_flat120_original, block021_data_flat125_original]
def block021_data_flat127 : CoefficientMerge.Poly := [(nat_lit 3180, Int.ofNat (nat_lit 129411562794624))]
theorem block021_data_flat127_step : block021_data_flat127 = (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) := by decide +kernel
theorem block021_data_flat127_original : block021_data_flat127 = (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) := by
  rw [block021_data_flat127_step]
def block021_data_flat128 : CoefficientMerge.Poly := [(nat_lit 3181, Int.ofNat (nat_lit 235307586628224))]
theorem block021_data_flat128_step : block021_data_flat128 = (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded) := by decide +kernel
theorem block021_data_flat128_original : block021_data_flat128 = (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded) := by
  rw [block021_data_flat128_step]
def block021_data_flat129 : CoefficientMerge.Poly := [(nat_lit 3180, Int.ofNat (nat_lit 129411562794624)), (nat_lit 3181, Int.ofNat (nat_lit 235307586628224))]
theorem block021_data_flat129_step : block021_data_flat129 = (CoefficientMerge.fastMerge block021_data_flat127 block021_data_flat128) := by decide +kernel
theorem block021_data_flat129_original : block021_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded)) := by
  rw [block021_data_flat129_step, block021_data_flat127_original, block021_data_flat128_original]
def block021_data_flat130 : CoefficientMerge.Poly := [(nat_lit 3182, Int.ofNat (nat_lit 219931677402624))]
theorem block021_data_flat130_step : block021_data_flat130 = (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) := by decide +kernel
theorem block021_data_flat130_original : block021_data_flat130 = (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) := by
  rw [block021_data_flat130_step]
def block021_data_flat131 : CoefficientMerge.Poly := [(nat_lit 3183, Int.ofNat (nat_lit 220080513844224))]
theorem block021_data_flat131_step : block021_data_flat131 = (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) := by decide +kernel
theorem block021_data_flat131_original : block021_data_flat131 = (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) := by
  rw [block021_data_flat131_step]
def block021_data_flat132 : CoefficientMerge.Poly := [(nat_lit 3184, Int.ofNat (nat_lit 220229350285824))]
theorem block021_data_flat132_step : block021_data_flat132 = (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded) := by decide +kernel
theorem block021_data_flat132_original : block021_data_flat132 = (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded) := by
  rw [block021_data_flat132_step]
def block021_data_flat133 : CoefficientMerge.Poly := [(nat_lit 3183, Int.ofNat (nat_lit 220080513844224)), (nat_lit 3184, Int.ofNat (nat_lit 220229350285824))]
theorem block021_data_flat133_step : block021_data_flat133 = (CoefficientMerge.fastMerge block021_data_flat131 block021_data_flat132) := by decide +kernel
theorem block021_data_flat133_original : block021_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded)) := by
  rw [block021_data_flat133_step, block021_data_flat131_original, block021_data_flat132_original]
def block021_data_flat134 : CoefficientMerge.Poly := [(nat_lit 3182, Int.ofNat (nat_lit 219931677402624)), (nat_lit 3183, Int.ofNat (nat_lit 220080513844224)), (nat_lit 3184, Int.ofNat (nat_lit 220229350285824))]
theorem block021_data_flat134_step : block021_data_flat134 = (CoefficientMerge.fastMerge block021_data_flat130 block021_data_flat133) := by decide +kernel
theorem block021_data_flat134_original : block021_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded))) := by
  rw [block021_data_flat134_step, block021_data_flat130_original, block021_data_flat133_original]
def block021_data_flat135 : CoefficientMerge.Poly := [(nat_lit 3180, Int.ofNat (nat_lit 129411562794624)), (nat_lit 3181, Int.ofNat (nat_lit 235307586628224)), (nat_lit 3182, Int.ofNat (nat_lit 219931677402624)), (nat_lit 3183, Int.ofNat (nat_lit 220080513844224)), (nat_lit 3184, Int.ofNat (nat_lit 220229350285824))]
theorem block021_data_flat135_step : block021_data_flat135 = (CoefficientMerge.fastMerge block021_data_flat129 block021_data_flat134) := by decide +kernel
theorem block021_data_flat135_original : block021_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded)))) := by
  rw [block021_data_flat135_step, block021_data_flat129_original, block021_data_flat134_original]
def block021_data_flat136 : CoefficientMerge.Poly := [(nat_lit 3163, Int.ofNat (nat_lit 223083434787840)), (nat_lit 3164, Int.ofNat (nat_lit 276330381484608)), (nat_lit 3165, Int.ofNat (nat_lit 348770785600512)), (nat_lit 3166, Int.ofNat (nat_lit 431499235368960)), (nat_lit 3167, Int.ofNat (nat_lit 514227685137408)), (nat_lit 3180, Int.ofNat (nat_lit 129411562794624)), (nat_lit 3181, Int.ofNat (nat_lit 235307586628224)), (nat_lit 3182, Int.ofNat (nat_lit 219931677402624)), (nat_lit 3183, Int.ofNat (nat_lit 220080513844224)), (nat_lit 3184, Int.ofNat (nat_lit 220229350285824))]
theorem block021_data_flat136_step : block021_data_flat136 = (CoefficientMerge.fastMerge block021_data_flat126 block021_data_flat135) := by decide +kernel
theorem block021_data_flat136_original : block021_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded))))) := by
  rw [block021_data_flat136_step, block021_data_flat126_original, block021_data_flat135_original]
def block021_data_flat137 : CoefficientMerge.Poly := [(nat_lit 3185, Int.ofNat (nat_lit 220378186727424))]
theorem block021_data_flat137_step : block021_data_flat137 = (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) := by decide +kernel
theorem block021_data_flat137_original : block021_data_flat137 = (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) := by
  rw [block021_data_flat137_step]
def block021_data_flat138 : CoefficientMerge.Poly := [(nat_lit 3186, Int.ofNat (nat_lit 284414134232448))]
theorem block021_data_flat138_step : block021_data_flat138 = (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded) := by decide +kernel
theorem block021_data_flat138_original : block021_data_flat138 = (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded) := by
  rw [block021_data_flat138_step]
def block021_data_flat139 : CoefficientMerge.Poly := [(nat_lit 3185, Int.ofNat (nat_lit 220378186727424)), (nat_lit 3186, Int.ofNat (nat_lit 284414134232448))]
theorem block021_data_flat139_step : block021_data_flat139 = (CoefficientMerge.fastMerge block021_data_flat137 block021_data_flat138) := by decide +kernel
theorem block021_data_flat139_original : block021_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded)) := by
  rw [block021_data_flat139_step, block021_data_flat137_original, block021_data_flat138_original]
def block021_data_flat140 : CoefficientMerge.Poly := [(nat_lit 3187, Int.ofNat (nat_lit 271093818378240))]
theorem block021_data_flat140_step : block021_data_flat140 = (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) := by decide +kernel
theorem block021_data_flat140_original : block021_data_flat140 = (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) := by
  rw [block021_data_flat140_step]
def block021_data_flat141 : CoefficientMerge.Poly := [(nat_lit 3188, Int.ofNat (nat_lit 374528944741248))]
theorem block021_data_flat141_step : block021_data_flat141 = (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) := by decide +kernel
theorem block021_data_flat141_original : block021_data_flat141 = (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) := by
  rw [block021_data_flat141_step]
def block021_data_flat142 : CoefficientMerge.Poly := [(nat_lit 3189, Int.ofNat (nat_lit 372227408796672))]
theorem block021_data_flat142_step : block021_data_flat142 = (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded) := by decide +kernel
theorem block021_data_flat142_original : block021_data_flat142 = (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded) := by
  rw [block021_data_flat142_step]
def block021_data_flat143 : CoefficientMerge.Poly := [(nat_lit 3188, Int.ofNat (nat_lit 374528944741248)), (nat_lit 3189, Int.ofNat (nat_lit 372227408796672))]
theorem block021_data_flat143_step : block021_data_flat143 = (CoefficientMerge.fastMerge block021_data_flat141 block021_data_flat142) := by decide +kernel
theorem block021_data_flat143_original : block021_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded)) := by
  rw [block021_data_flat143_step, block021_data_flat141_original, block021_data_flat142_original]
def block021_data_flat144 : CoefficientMerge.Poly := [(nat_lit 3187, Int.ofNat (nat_lit 271093818378240)), (nat_lit 3188, Int.ofNat (nat_lit 374528944741248)), (nat_lit 3189, Int.ofNat (nat_lit 372227408796672))]
theorem block021_data_flat144_step : block021_data_flat144 = (CoefficientMerge.fastMerge block021_data_flat140 block021_data_flat143) := by decide +kernel
theorem block021_data_flat144_original : block021_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded))) := by
  rw [block021_data_flat144_step, block021_data_flat140_original, block021_data_flat143_original]
def block021_data_flat145 : CoefficientMerge.Poly := [(nat_lit 3185, Int.ofNat (nat_lit 220378186727424)), (nat_lit 3186, Int.ofNat (nat_lit 284414134232448)), (nat_lit 3187, Int.ofNat (nat_lit 271093818378240)), (nat_lit 3188, Int.ofNat (nat_lit 374528944741248)), (nat_lit 3189, Int.ofNat (nat_lit 372227408796672))]
theorem block021_data_flat145_step : block021_data_flat145 = (CoefficientMerge.fastMerge block021_data_flat139 block021_data_flat144) := by decide +kernel
theorem block021_data_flat145_original : block021_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded)))) := by
  rw [block021_data_flat145_step, block021_data_flat139_original, block021_data_flat144_original]
def block021_data_flat146 : CoefficientMerge.Poly := [(nat_lit 3190, Int.ofNat (nat_lit 439600190261760))]
theorem block021_data_flat146_step : block021_data_flat146 = (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) := by decide +kernel
theorem block021_data_flat146_original : block021_data_flat146 = (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) := by
  rw [block021_data_flat146_step]
def block021_data_flat147 : CoefficientMerge.Poly := [(nat_lit 3191, Int.ofNat (nat_lit 506972971726848))]
theorem block021_data_flat147_step : block021_data_flat147 = (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded) := by decide +kernel
theorem block021_data_flat147_original : block021_data_flat147 = (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded) := by
  rw [block021_data_flat147_step]
def block021_data_flat148 : CoefficientMerge.Poly := [(nat_lit 3190, Int.ofNat (nat_lit 439600190261760)), (nat_lit 3191, Int.ofNat (nat_lit 506972971726848))]
theorem block021_data_flat148_step : block021_data_flat148 = (CoefficientMerge.fastMerge block021_data_flat146 block021_data_flat147) := by decide +kernel
theorem block021_data_flat148_original : block021_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded)) := by
  rw [block021_data_flat148_step, block021_data_flat146_original, block021_data_flat147_original]
def block021_data_flat149 : CoefficientMerge.Poly := [(nat_lit 3205, Int.ofNat (nat_lit 143913103488000))]
theorem block021_data_flat149_step : block021_data_flat149 = (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) := by decide +kernel
theorem block021_data_flat149_original : block021_data_flat149 = (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) := by
  rw [block021_data_flat149_step]
def block021_data_flat150 : CoefficientMerge.Poly := [(nat_lit 3206, Int.ofNat (nat_lit 256062342412800))]
theorem block021_data_flat150_step : block021_data_flat150 = (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) := by decide +kernel
theorem block021_data_flat150_original : block021_data_flat150 = (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) := by
  rw [block021_data_flat150_step]
def block021_data_flat151 : CoefficientMerge.Poly := [(nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
theorem block021_data_flat151_step : block021_data_flat151 = (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded) := by decide +kernel
theorem block021_data_flat151_original : block021_data_flat151 = (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded) := by
  rw [block021_data_flat151_step]
def block021_data_flat152 : CoefficientMerge.Poly := [(nat_lit 3206, Int.ofNat (nat_lit 256062342412800)), (nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
theorem block021_data_flat152_step : block021_data_flat152 = (CoefficientMerge.fastMerge block021_data_flat150 block021_data_flat151) := by decide +kernel
theorem block021_data_flat152_original : block021_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded)) := by
  rw [block021_data_flat152_step, block021_data_flat150_original, block021_data_flat151_original]
def block021_data_flat153 : CoefficientMerge.Poly := [(nat_lit 3205, Int.ofNat (nat_lit 143913103488000)), (nat_lit 3206, Int.ofNat (nat_lit 256062342412800)), (nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
theorem block021_data_flat153_step : block021_data_flat153 = (CoefficientMerge.fastMerge block021_data_flat149 block021_data_flat152) := by decide +kernel
theorem block021_data_flat153_original : block021_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded))) := by
  rw [block021_data_flat153_step, block021_data_flat149_original, block021_data_flat152_original]
def block021_data_flat154 : CoefficientMerge.Poly := [(nat_lit 3190, Int.ofNat (nat_lit 439600190261760)), (nat_lit 3191, Int.ofNat (nat_lit 506972971726848)), (nat_lit 3205, Int.ofNat (nat_lit 143913103488000)), (nat_lit 3206, Int.ofNat (nat_lit 256062342412800)), (nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
theorem block021_data_flat154_step : block021_data_flat154 = (CoefficientMerge.fastMerge block021_data_flat148 block021_data_flat153) := by decide +kernel
theorem block021_data_flat154_original : block021_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded)))) := by
  rw [block021_data_flat154_step, block021_data_flat148_original, block021_data_flat153_original]
def block021_data_flat155 : CoefficientMerge.Poly := [(nat_lit 3185, Int.ofNat (nat_lit 220378186727424)), (nat_lit 3186, Int.ofNat (nat_lit 284414134232448)), (nat_lit 3187, Int.ofNat (nat_lit 271093818378240)), (nat_lit 3188, Int.ofNat (nat_lit 374528944741248)), (nat_lit 3189, Int.ofNat (nat_lit 372227408796672)), (nat_lit 3190, Int.ofNat (nat_lit 439600190261760)), (nat_lit 3191, Int.ofNat (nat_lit 506972971726848)), (nat_lit 3205, Int.ofNat (nat_lit 143913103488000)), (nat_lit 3206, Int.ofNat (nat_lit 256062342412800)), (nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
theorem block021_data_flat155_step : block021_data_flat155 = (CoefficientMerge.fastMerge block021_data_flat145 block021_data_flat154) := by decide +kernel
theorem block021_data_flat155_original : block021_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded))))) := by
  rw [block021_data_flat155_step, block021_data_flat145_original, block021_data_flat154_original]
def block021_data_flat156 : CoefficientMerge.Poly := [(nat_lit 3163, Int.ofNat (nat_lit 223083434787840)), (nat_lit 3164, Int.ofNat (nat_lit 276330381484608)), (nat_lit 3165, Int.ofNat (nat_lit 348770785600512)), (nat_lit 3166, Int.ofNat (nat_lit 431499235368960)), (nat_lit 3167, Int.ofNat (nat_lit 514227685137408)), (nat_lit 3180, Int.ofNat (nat_lit 129411562794624)), (nat_lit 3181, Int.ofNat (nat_lit 235307586628224)), (nat_lit 3182, Int.ofNat (nat_lit 219931677402624)), (nat_lit 3183, Int.ofNat (nat_lit 220080513844224)), (nat_lit 3184, Int.ofNat (nat_lit 220229350285824)), (nat_lit 3185, Int.ofNat (nat_lit 220378186727424)), (nat_lit 3186, Int.ofNat (nat_lit 284414134232448)), (nat_lit 3187, Int.ofNat (nat_lit 271093818378240)), (nat_lit 3188, Int.ofNat (nat_lit 374528944741248)), (nat_lit 3189, Int.ofNat (nat_lit 372227408796672)), (nat_lit 3190, Int.ofNat (nat_lit 439600190261760)), (nat_lit 3191, Int.ofNat (nat_lit 506972971726848)), (nat_lit 3205, Int.ofNat (nat_lit 143913103488000)), (nat_lit 3206, Int.ofNat (nat_lit 256062342412800)), (nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
theorem block021_data_flat156_step : block021_data_flat156 = (CoefficientMerge.fastMerge block021_data_flat136 block021_data_flat155) := by decide +kernel
theorem block021_data_flat156_original : block021_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded)))))) := by
  rw [block021_data_flat156_step, block021_data_flat136_original, block021_data_flat155_original]
def block021_data_flat157 : CoefficientMerge.Poly := [(nat_lit 3132, Int.ofNat (nat_lit 129894268063824)), (nat_lit 3133, Int.ofNat (nat_lit 123253060669200)), (nat_lit 3134, Int.ofNat (nat_lit 112937590458000)), (nat_lit 3135, Int.ofNat (nat_lit 118146865914000)), (nat_lit 3136, Int.ofNat (nat_lit 123356141370000)), (nat_lit 3137, Int.ofNat (nat_lit 128565416826000)), (nat_lit 3138, Int.ofNat (nat_lit 154777723324488)), (nat_lit 3139, Int.ofNat (nat_lit 186951414228480)), (nat_lit 3140, Int.ofNat (nat_lit 225834507154872)), (nat_lit 3141, Int.ofNat (nat_lit 306021256696980)), (nat_lit 3142, Int.ofNat (nat_lit 386208006239088)), (nat_lit 3143, Int.ofNat (nat_lit 467666395638750)), (nat_lit 3155, Int.ofNat (nat_lit 86333512567104)), (nat_lit 3156, Int.ofNat (nat_lit 177727995707328)), (nat_lit 3157, Int.ofNat (nat_lit 165983824600704)), (nat_lit 3158, Int.ofNat (nat_lit 150565390677504)), (nat_lit 3159, Int.ofNat (nat_lit 150671702421504)), (nat_lit 3160, Int.ofNat (nat_lit 153861054741504)), (nat_lit 3161, Int.ofNat (nat_lit 157050407061504)), (nat_lit 3162, Int.ofNat (nat_lit 198462683884608)), (nat_lit 3163, Int.ofNat (nat_lit 223083434787840)), (nat_lit 3164, Int.ofNat (nat_lit 276330381484608)), (nat_lit 3165, Int.ofNat (nat_lit 348770785600512)), (nat_lit 3166, Int.ofNat (nat_lit 431499235368960)), (nat_lit 3167, Int.ofNat (nat_lit 514227685137408)), (nat_lit 3180, Int.ofNat (nat_lit 129411562794624)), (nat_lit 3181, Int.ofNat (nat_lit 235307586628224)), (nat_lit 3182, Int.ofNat (nat_lit 219931677402624)), (nat_lit 3183, Int.ofNat (nat_lit 220080513844224)), (nat_lit 3184, Int.ofNat (nat_lit 220229350285824)), (nat_lit 3185, Int.ofNat (nat_lit 220378186727424)), (nat_lit 3186, Int.ofNat (nat_lit 284414134232448)), (nat_lit 3187, Int.ofNat (nat_lit 271093818378240)), (nat_lit 3188, Int.ofNat (nat_lit 374528944741248)), (nat_lit 3189, Int.ofNat (nat_lit 372227408796672)), (nat_lit 3190, Int.ofNat (nat_lit 439600190261760)), (nat_lit 3191, Int.ofNat (nat_lit 506972971726848)), (nat_lit 3205, Int.ofNat (nat_lit 143913103488000)), (nat_lit 3206, Int.ofNat (nat_lit 256062342412800)), (nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
theorem block021_data_flat157_step : block021_data_flat157 = (CoefficientMerge.fastMerge block021_data_flat117 block021_data_flat156) := by decide +kernel
theorem block021_data_flat157_original : block021_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded))))))) := by
  rw [block021_data_flat157_step, block021_data_flat117_original, block021_data_flat156_original]
def block021_data_flat158 : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 32355227510496)), (nat_lit 3066, Int.ofNat (nat_lit 43745229153648)), (nat_lit 3067, Int.ofNat (nat_lit 56706432921600)), (nat_lit 3068, Int.ofNat (nat_lit 76377038711952)), (nat_lit 3069, Int.ofNat (nat_lit 133755104320728)), (nat_lit 3070, Int.ofNat (nat_lit 191133169929504)), (nat_lit 3071, Int.ofNat (nat_lit 252374959277892)), (nat_lit 3080, Int.ofNat (nat_lit 30617742364704)), (nat_lit 3081, Int.ofNat (nat_lit 48899114252208)), (nat_lit 3082, Int.ofNat (nat_lit 21675381235200)), (nat_lit 3083, Int.ofNat (nat_lit 31085474131008)), (nat_lit 3084, Int.ofNat (nat_lit 58922406959328)), (nat_lit 3085, Int.ofNat (nat_lit 53259267609504)), (nat_lit 3086, Int.ofNat (nat_lit 43921865443104)), (nat_lit 3087, Int.ofNat (nat_lit 50109208943904)), (nat_lit 3088, Int.ofNat (nat_lit 56296552444704)), (nat_lit 3089, Int.ofNat (nat_lit 62483895945504)), (nat_lit 3090, Int.ofNat (nat_lit 76832947703952)), (nat_lit 3091, Int.ofNat (nat_lit 96207152025600)), (nat_lit 3092, Int.ofNat (nat_lit 122290758369648)), (nat_lit 3093, Int.ofNat (nat_lit 193758103116072)), (nat_lit 3094, Int.ofNat (nat_lit 265225447862496)), (nat_lit 3095, Int.ofNat (nat_lit 340940705202108)), (nat_lit 3105, Int.ofNat (nat_lit 50132370389904)), (nat_lit 3106, Int.ofNat (nat_lit 73000342255104)), (nat_lit 3107, Int.ofNat (nat_lit 60389198950608)), (nat_lit 3108, Int.ofNat (nat_lit 91330434703728)), (nat_lit 3109, Int.ofNat (nat_lit 82605517126704)), (nat_lit 3110, Int.ofNat (nat_lit 73289377309104)), (nat_lit 3111, Int.ofNat (nat_lit 79497983158704)), (nat_lit 3112, Int.ofNat (nat_lit 85706589008304)), (nat_lit 3113, Int.ofNat (nat_lit 91915194857904)), (nat_lit 3114, Int.ofNat (nat_lit 110304175786200)), (nat_lit 3115, Int.ofNat (nat_lit 135921777108480)), (nat_lit 3116, Int.ofNat (nat_lit 168248780453160)), (nat_lit 3117, Int.ofNat (nat_lit 249458858366652)), (nat_lit 3118, Int.ofNat (nat_lit 330668936280144)), (nat_lit 3119, Int.ofNat (nat_lit 415673127039258)), (nat_lit 3130, Int.ofNat (nat_lit 54718970367600)), (nat_lit 3131, Int.ofNat (nat_lit 103035403280304)), (nat_lit 3132, Int.ofNat (nat_lit 129894268063824)), (nat_lit 3133, Int.ofNat (nat_lit 123253060669200)), (nat_lit 3134, Int.ofNat (nat_lit 112937590458000)), (nat_lit 3135, Int.ofNat (nat_lit 118146865914000)), (nat_lit 3136, Int.ofNat (nat_lit 123356141370000)), (nat_lit 3137, Int.ofNat (nat_lit 128565416826000)), (nat_lit 3138, Int.ofNat (nat_lit 154777723324488)), (nat_lit 3139, Int.ofNat (nat_lit 186951414228480)), (nat_lit 3140, Int.ofNat (nat_lit 225834507154872)), (nat_lit 3141, Int.ofNat (nat_lit 306021256696980)), (nat_lit 3142, Int.ofNat (nat_lit 386208006239088)), (nat_lit 3143, Int.ofNat (nat_lit 467666395638750)), (nat_lit 3155, Int.ofNat (nat_lit 86333512567104)), (nat_lit 3156, Int.ofNat (nat_lit 177727995707328)), (nat_lit 3157, Int.ofNat (nat_lit 165983824600704)), (nat_lit 3158, Int.ofNat (nat_lit 150565390677504)), (nat_lit 3159, Int.ofNat (nat_lit 150671702421504)), (nat_lit 3160, Int.ofNat (nat_lit 153861054741504)), (nat_lit 3161, Int.ofNat (nat_lit 157050407061504)), (nat_lit 3162, Int.ofNat (nat_lit 198462683884608)), (nat_lit 3163, Int.ofNat (nat_lit 223083434787840)), (nat_lit 3164, Int.ofNat (nat_lit 276330381484608)), (nat_lit 3165, Int.ofNat (nat_lit 348770785600512)), (nat_lit 3166, Int.ofNat (nat_lit 431499235368960)), (nat_lit 3167, Int.ofNat (nat_lit 514227685137408)), (nat_lit 3180, Int.ofNat (nat_lit 129411562794624)), (nat_lit 3181, Int.ofNat (nat_lit 235307586628224)), (nat_lit 3182, Int.ofNat (nat_lit 219931677402624)), (nat_lit 3183, Int.ofNat (nat_lit 220080513844224)), (nat_lit 3184, Int.ofNat (nat_lit 220229350285824)), (nat_lit 3185, Int.ofNat (nat_lit 220378186727424)), (nat_lit 3186, Int.ofNat (nat_lit 284414134232448)), (nat_lit 3187, Int.ofNat (nat_lit 271093818378240)), (nat_lit 3188, Int.ofNat (nat_lit 374528944741248)), (nat_lit 3189, Int.ofNat (nat_lit 372227408796672)), (nat_lit 3190, Int.ofNat (nat_lit 439600190261760)), (nat_lit 3191, Int.ofNat (nat_lit 506972971726848)), (nat_lit 3205, Int.ofNat (nat_lit 143913103488000)), (nat_lit 3206, Int.ofNat (nat_lit 256062342412800)), (nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
theorem block021_data_flat158_step : block021_data_flat158 = (CoefficientMerge.fastMerge block021_data_flat078 block021_data_flat157) := by decide +kernel
theorem block021_data_flat158_original : block021_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded)))))))) := by
  rw [block021_data_flat158_step, block021_data_flat078_original, block021_data_flat157_original]
def block021_data_flat159 : CoefficientMerge.Poly := [(nat_lit 3065, Int.ofNat (nat_lit 32355227510496)), (nat_lit 3066, Int.ofNat (nat_lit 43745229153648)), (nat_lit 3067, Int.ofNat (nat_lit 56706432921600)), (nat_lit 3068, Int.ofNat (nat_lit 76377038711952)), (nat_lit 3069, Int.ofNat (nat_lit 133755104320728)), (nat_lit 3070, Int.ofNat (nat_lit 191133169929504)), (nat_lit 3071, Int.ofNat (nat_lit 252374959277892)), (nat_lit 3080, Int.ofNat (nat_lit 30617742364704)), (nat_lit 3081, Int.ofNat (nat_lit 48899114252208)), (nat_lit 3082, Int.ofNat (nat_lit 21675381235200)), (nat_lit 3083, Int.ofNat (nat_lit 31085474131008)), (nat_lit 3084, Int.ofNat (nat_lit 58922406959328)), (nat_lit 3085, Int.ofNat (nat_lit 53259267609504)), (nat_lit 3086, Int.ofNat (nat_lit 43921865443104)), (nat_lit 3087, Int.ofNat (nat_lit 50109208943904)), (nat_lit 3088, Int.ofNat (nat_lit 56296552444704)), (nat_lit 3089, Int.ofNat (nat_lit 62483895945504)), (nat_lit 3090, Int.ofNat (nat_lit 76832947703952)), (nat_lit 3091, Int.ofNat (nat_lit 96207152025600)), (nat_lit 3092, Int.ofNat (nat_lit 122290758369648)), (nat_lit 3093, Int.ofNat (nat_lit 193758103116072)), (nat_lit 3094, Int.ofNat (nat_lit 265225447862496)), (nat_lit 3095, Int.ofNat (nat_lit 340940705202108)), (nat_lit 3105, Int.ofNat (nat_lit 50132370389904)), (nat_lit 3106, Int.ofNat (nat_lit 73000342255104)), (nat_lit 3107, Int.ofNat (nat_lit 60389198950608)), (nat_lit 3108, Int.ofNat (nat_lit 91330434703728)), (nat_lit 3109, Int.ofNat (nat_lit 82605517126704)), (nat_lit 3110, Int.ofNat (nat_lit 73289377309104)), (nat_lit 3111, Int.ofNat (nat_lit 79497983158704)), (nat_lit 3112, Int.ofNat (nat_lit 85706589008304)), (nat_lit 3113, Int.ofNat (nat_lit 91915194857904)), (nat_lit 3114, Int.ofNat (nat_lit 110304175786200)), (nat_lit 3115, Int.ofNat (nat_lit 135921777108480)), (nat_lit 3116, Int.ofNat (nat_lit 168248780453160)), (nat_lit 3117, Int.ofNat (nat_lit 249458858366652)), (nat_lit 3118, Int.ofNat (nat_lit 330668936280144)), (nat_lit 3119, Int.ofNat (nat_lit 415673127039258)), (nat_lit 3130, Int.ofNat (nat_lit 54718970367600)), (nat_lit 3131, Int.ofNat (nat_lit 103035403280304)), (nat_lit 3132, Int.ofNat (nat_lit 129894268063824)), (nat_lit 3133, Int.ofNat (nat_lit 123253060669200)), (nat_lit 3134, Int.ofNat (nat_lit 112937590458000)), (nat_lit 3135, Int.ofNat (nat_lit 118146865914000)), (nat_lit 3136, Int.ofNat (nat_lit 123356141370000)), (nat_lit 3137, Int.ofNat (nat_lit 128565416826000)), (nat_lit 3138, Int.ofNat (nat_lit 154777723324488)), (nat_lit 3139, Int.ofNat (nat_lit 186951414228480)), (nat_lit 3140, Int.ofNat (nat_lit 225834507154872)), (nat_lit 3141, Int.ofNat (nat_lit 306021256696980)), (nat_lit 3142, Int.ofNat (nat_lit 386208006239088)), (nat_lit 3143, Int.ofNat (nat_lit 467666395638750)), (nat_lit 3155, Int.ofNat (nat_lit 86333512567104)), (nat_lit 3156, Int.ofNat (nat_lit 177727995707328)), (nat_lit 3157, Int.ofNat (nat_lit 165983824600704)), (nat_lit 3158, Int.ofNat (nat_lit 150565390677504)), (nat_lit 3159, Int.ofNat (nat_lit 150671702421504)), (nat_lit 3160, Int.ofNat (nat_lit 153861054741504)), (nat_lit 3161, Int.ofNat (nat_lit 157050407061504)), (nat_lit 3162, Int.ofNat (nat_lit 198462683884608)), (nat_lit 3163, Int.ofNat (nat_lit 223083434787840)), (nat_lit 3164, Int.ofNat (nat_lit 276330381484608)), (nat_lit 3165, Int.ofNat (nat_lit 348770785600512)), (nat_lit 3166, Int.ofNat (nat_lit 431499235368960)), (nat_lit 3167, Int.ofNat (nat_lit 514227685137408)), (nat_lit 3180, Int.ofNat (nat_lit 129411562794624)), (nat_lit 3181, Int.ofNat (nat_lit 235307586628224)), (nat_lit 3182, Int.ofNat (nat_lit 219931677402624)), (nat_lit 3183, Int.ofNat (nat_lit 220080513844224)), (nat_lit 3184, Int.ofNat (nat_lit 220229350285824)), (nat_lit 3185, Int.ofNat (nat_lit 220378186727424)), (nat_lit 3186, Int.ofNat (nat_lit 284414134232448)), (nat_lit 3187, Int.ofNat (nat_lit 271093818378240)), (nat_lit 3188, Int.ofNat (nat_lit 374528944741248)), (nat_lit 3189, Int.ofNat (nat_lit 372227408796672)), (nat_lit 3190, Int.ofNat (nat_lit 439600190261760)), (nat_lit 3191, Int.ofNat (nat_lit 506972971726848)), (nat_lit 3205, Int.ofNat (nat_lit 143913103488000)), (nat_lit 3206, Int.ofNat (nat_lit 256062342412800)), (nat_lit 3207, Int.ofNat (nat_lit 249067029657600))]
theorem block021_data_flat159_step : block021_data_flat159 = (CoefficientMerge.trim block021_data_flat158) := by decide +kernel
theorem block021_data_flat159_original : block021_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded))))))))) := by
  rw [block021_data_flat159_step, block021_data_flat158_original]
theorem block021_data : block021 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32355227510496 : Int) atom1489Coded) (CoefficientMerge.scale (43745229153648 : Int) atom1490Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56706432921600 : Int) atom1491Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76377038711952 : Int) atom1492Coded) (CoefficientMerge.scale (133755104320728 : Int) atom1493Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (191133169929504 : Int) atom1494Coded) (CoefficientMerge.scale (252374959277892 : Int) atom1495Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30617742364704 : Int) atom1496Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48899114252208 : Int) atom1497Coded) (CoefficientMerge.scale (21675381235200 : Int) atom1498Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31085474131008 : Int) atom1499Coded) (CoefficientMerge.scale (58922406959328 : Int) atom1500Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53259267609504 : Int) atom1501Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43921865443104 : Int) atom1502Coded) (CoefficientMerge.scale (50109208943904 : Int) atom1503Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (56296552444704 : Int) atom1504Coded) (CoefficientMerge.scale (62483895945504 : Int) atom1505Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (76832947703952 : Int) atom1506Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (96207152025600 : Int) atom1507Coded) (CoefficientMerge.scale (122290758369648 : Int) atom1508Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (193758103116072 : Int) atom1509Coded) (CoefficientMerge.scale (265225447862496 : Int) atom1510Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340940705202108 : Int) atom1511Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50132370389904 : Int) atom1512Coded) (CoefficientMerge.scale (73000342255104 : Int) atom1513Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60389198950608 : Int) atom1514Coded) (CoefficientMerge.scale (91330434703728 : Int) atom1515Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82605517126704 : Int) atom1516Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73289377309104 : Int) atom1517Coded) (CoefficientMerge.scale (79497983158704 : Int) atom1518Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (85706589008304 : Int) atom1519Coded) (CoefficientMerge.scale (91915194857904 : Int) atom1520Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110304175786200 : Int) atom1521Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135921777108480 : Int) atom1522Coded) (CoefficientMerge.scale (168248780453160 : Int) atom1523Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249458858366652 : Int) atom1524Coded) (CoefficientMerge.scale (330668936280144 : Int) atom1525Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415673127039258 : Int) atom1526Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54718970367600 : Int) atom1527Coded) (CoefficientMerge.scale (103035403280304 : Int) atom1528Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129894268063824 : Int) atom1529Coded) (CoefficientMerge.scale (123253060669200 : Int) atom1530Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (112937590458000 : Int) atom1531Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118146865914000 : Int) atom1532Coded) (CoefficientMerge.scale (123356141370000 : Int) atom1533Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (128565416826000 : Int) atom1534Coded) (CoefficientMerge.scale (154777723324488 : Int) atom1535Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186951414228480 : Int) atom1536Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225834507154872 : Int) atom1537Coded) (CoefficientMerge.scale (306021256696980 : Int) atom1538Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (386208006239088 : Int) atom1539Coded) (CoefficientMerge.scale (467666395638750 : Int) atom1540Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (86333512567104 : Int) atom1541Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (177727995707328 : Int) atom1542Coded) (CoefficientMerge.scale (165983824600704 : Int) atom1543Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (150565390677504 : Int) atom1544Coded) (CoefficientMerge.scale (150671702421504 : Int) atom1545Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (153861054741504 : Int) atom1546Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (157050407061504 : Int) atom1547Coded) (CoefficientMerge.scale (198462683884608 : Int) atom1548Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (223083434787840 : Int) atom1549Coded) (CoefficientMerge.scale (276330381484608 : Int) atom1550Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (348770785600512 : Int) atom1551Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431499235368960 : Int) atom1552Coded) (CoefficientMerge.scale (514227685137408 : Int) atom1553Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129411562794624 : Int) atom1554Coded) (CoefficientMerge.scale (235307586628224 : Int) atom1555Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (219931677402624 : Int) atom1556Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (220080513844224 : Int) atom1557Coded) (CoefficientMerge.scale (220229350285824 : Int) atom1558Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (220378186727424 : Int) atom1559Coded) (CoefficientMerge.scale (284414134232448 : Int) atom1560Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (271093818378240 : Int) atom1561Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374528944741248 : Int) atom1562Coded) (CoefficientMerge.scale (372227408796672 : Int) atom1563Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439600190261760 : Int) atom1564Coded) (CoefficientMerge.scale (506972971726848 : Int) atom1565Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143913103488000 : Int) atom1566Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256062342412800 : Int) atom1567Coded) (CoefficientMerge.scale (249067029657600 : Int) atom1568Coded)))))))) := by
  have h : block021 = block021_data_flat159 := by decide +kernel
  exact h.trans block021_data_flat159_original
theorem block021_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block021 := by
  rw [block021_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1489Coded_nonneg g hg hA hB) (atom1490Coded_nonneg g hg hA hB)) (add_nonneg (atom1491Coded_nonneg g hg hA hB) (add_nonneg (atom1492Coded_nonneg g hg hA hB) (atom1493Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1494Coded_nonneg g hg hA hB) (atom1495Coded_nonneg g hg hA hB)) (add_nonneg (atom1496Coded_nonneg g hg hA hB) (add_nonneg (atom1497Coded_nonneg g hg hA hB) (atom1498Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1499Coded_nonneg g hg hA hB) (atom1500Coded_nonneg g hg hA hB)) (add_nonneg (atom1501Coded_nonneg g hg hA hB) (add_nonneg (atom1502Coded_nonneg g hg hA hB) (atom1503Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1504Coded_nonneg g hg hA hB) (atom1505Coded_nonneg g hg hA hB)) (add_nonneg (atom1506Coded_nonneg g hg hA hB) (add_nonneg (atom1507Coded_nonneg g hg hA hB) (atom1508Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1509Coded_nonneg g hg hA hB) (atom1510Coded_nonneg g hg hA hB)) (add_nonneg (atom1511Coded_nonneg g hg hA hB) (add_nonneg (atom1512Coded_nonneg g hg hA hB) (atom1513Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1514Coded_nonneg g hg hA hB) (atom1515Coded_nonneg g hg hA hB)) (add_nonneg (atom1516Coded_nonneg g hg hA hB) (add_nonneg (atom1517Coded_nonneg g hg hA hB) (atom1518Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1519Coded_nonneg g hg hA hB) (atom1520Coded_nonneg g hg hA hB)) (add_nonneg (atom1521Coded_nonneg g hg hA hB) (add_nonneg (atom1522Coded_nonneg g hg hA hB) (atom1523Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1524Coded_nonneg g hg hA hB) (atom1525Coded_nonneg g hg hA hB)) (add_nonneg (atom1526Coded_nonneg g hg hA hB) (add_nonneg (atom1527Coded_nonneg g hg hA hB) (atom1528Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1529Coded_nonneg g hg hA hB) (atom1530Coded_nonneg g hg hA hB)) (add_nonneg (atom1531Coded_nonneg g hg hA hB) (add_nonneg (atom1532Coded_nonneg g hg hA hB) (atom1533Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1534Coded_nonneg g hg hA hB) (atom1535Coded_nonneg g hg hA hB)) (add_nonneg (atom1536Coded_nonneg g hg hA hB) (add_nonneg (atom1537Coded_nonneg g hg hA hB) (atom1538Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1539Coded_nonneg g hg hA hB) (atom1540Coded_nonneg g hg hA hB)) (add_nonneg (atom1541Coded_nonneg g hg hA hB) (add_nonneg (atom1542Coded_nonneg g hg hA hB) (atom1543Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1544Coded_nonneg g hg hA hB) (atom1545Coded_nonneg g hg hA hB)) (add_nonneg (atom1546Coded_nonneg g hg hA hB) (add_nonneg (atom1547Coded_nonneg g hg hA hB) (atom1548Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1549Coded_nonneg g hg hA hB) (atom1550Coded_nonneg g hg hA hB)) (add_nonneg (atom1551Coded_nonneg g hg hA hB) (add_nonneg (atom1552Coded_nonneg g hg hA hB) (atom1553Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1554Coded_nonneg g hg hA hB) (atom1555Coded_nonneg g hg hA hB)) (add_nonneg (atom1556Coded_nonneg g hg hA hB) (add_nonneg (atom1557Coded_nonneg g hg hA hB) (atom1558Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1559Coded_nonneg g hg hA hB) (atom1560Coded_nonneg g hg hA hB)) (add_nonneg (atom1561Coded_nonneg g hg hA hB) (add_nonneg (atom1562Coded_nonneg g hg hA hB) (atom1563Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1564Coded_nonneg g hg hA hB) (atom1565Coded_nonneg g hg hA hB)) (add_nonneg (atom1566Coded_nonneg g hg hA hB) (add_nonneg (atom1567Coded_nonneg g hg hA hB) (atom1568Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
