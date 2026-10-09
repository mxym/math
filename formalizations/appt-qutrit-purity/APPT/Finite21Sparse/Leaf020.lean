-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1456 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1456 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1456 = ((g 9) * (g 9) * (g 17)) := by
  norm_num [atom1456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1456_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182739160800 : Int) atom1456) := by
  rw [SparsePolynomial.eval_scale, eval_atom1456]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1456Coded : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 1))]
theorem atom1456Coded_decode : atom1456 = SparsePolynomial.decodeCubic 21 atom1456Coded := by decide +kernel
theorem atom1456Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) := by
  have h := atom1456_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1456Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1457 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1457 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1457 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom1457, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1457_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (770276908800 : Int) atom1457) := by
  rw [SparsePolynomial.eval_scale, eval_atom1457]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1457Coded : CoefficientMerge.Poly := [(nat_lit 4189, Int.ofNat (nat_lit 1))]
theorem atom1457Coded_decode : atom1457 = SparsePolynomial.decodeCubic 21 atom1457Coded := by decide +kernel
theorem atom1457Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded) := by
  have h := atom1457_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1457Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1458 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1458 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1458 = ((g 9) * (g 10) * (g 13)) := by
  norm_num [atom1458, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1458_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1458) := by
  rw [SparsePolynomial.eval_scale, eval_atom1458]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1458Coded : CoefficientMerge.Poly := [(nat_lit 4192, Int.ofNat (nat_lit 1))]
theorem atom1458Coded_decode : atom1458 = SparsePolynomial.decodeCubic 21 atom1458Coded := by decide +kernel
theorem atom1458Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) := by
  have h := atom1458_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1458Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1459 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1459 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1459 = ((g 9) * (g 10) * (g 14)) := by
  norm_num [atom1459, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1459_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854359833600 : Int) atom1459) := by
  rw [SparsePolynomial.eval_scale, eval_atom1459]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1459Coded : CoefficientMerge.Poly := [(nat_lit 4193, Int.ofNat (nat_lit 1))]
theorem atom1459Coded_decode : atom1459 = SparsePolynomial.decodeCubic 21 atom1459Coded := by decide +kernel
theorem atom1459Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) := by
  have h := atom1459_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1459Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1460 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1460 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1460 = ((g 9) * (g 10) * (g 15)) := by
  norm_num [atom1460, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1460_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5669444229120 : Int) atom1460) := by
  rw [SparsePolynomial.eval_scale, eval_atom1460]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1460Coded : CoefficientMerge.Poly := [(nat_lit 4194, Int.ofNat (nat_lit 1))]
theorem atom1460Coded_decode : atom1460 = SparsePolynomial.decodeCubic 21 atom1460Coded := by decide +kernel
theorem atom1460Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded) := by
  have h := atom1460_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1460Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1461 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1461 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1461 = ((g 9) * (g 10) * (g 17)) := by
  norm_num [atom1461, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1461_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6132165580800 : Int) atom1461) := by
  rw [SparsePolynomial.eval_scale, eval_atom1461]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1461Coded : CoefficientMerge.Poly := [(nat_lit 4196, Int.ofNat (nat_lit 1))]
theorem atom1461Coded_decode : atom1461 = SparsePolynomial.decodeCubic 21 atom1461Coded := by decide +kernel
theorem atom1461Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) := by
  have h := atom1461_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1461Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1462 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1462 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1462 = ((g 9) * (g 10) * (g 18)) := by
  norm_num [atom1462, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1462_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5786258284800 : Int) atom1462) := by
  rw [SparsePolynomial.eval_scale, eval_atom1462]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1462Coded : CoefficientMerge.Poly := [(nat_lit 4197, Int.ofNat (nat_lit 1))]
theorem atom1462Coded_decode : atom1462 = SparsePolynomial.decodeCubic 21 atom1462Coded := by decide +kernel
theorem atom1462Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded) := by
  have h := atom1462_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1462Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1463 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1463 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1463 = ((g 9) * (g 10) * (g 19)) := by
  norm_num [atom1463, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1463_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171238059520 : Int) atom1463) := by
  rw [SparsePolynomial.eval_scale, eval_atom1463]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1463Coded : CoefficientMerge.Poly := [(nat_lit 4198, Int.ofNat (nat_lit 1))]
theorem atom1463Coded_decode : atom1463 = SparsePolynomial.decodeCubic 21 atom1463Coded := by decide +kernel
theorem atom1463Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) := by
  have h := atom1463_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1463Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1464 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1464 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1464 = ((g 9) * (g 10) * (g 20)) := by
  norm_num [atom1464, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1464_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391151612800 : Int) atom1464) := by
  rw [SparsePolynomial.eval_scale, eval_atom1464]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1464Coded : CoefficientMerge.Poly := [(nat_lit 4199, Int.ofNat (nat_lit 1))]
theorem atom1464Coded_decode : atom1464 = SparsePolynomial.decodeCubic 21 atom1464Coded := by decide +kernel
theorem atom1464Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) := by
  have h := atom1464_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1464Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1465 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1465 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1465 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom1465, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1465_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1533788524800 : Int) atom1465) := by
  rw [SparsePolynomial.eval_scale, eval_atom1465]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1465Coded : CoefficientMerge.Poly := [(nat_lit 4211, Int.ofNat (nat_lit 1))]
theorem atom1465Coded_decode : atom1465 = SparsePolynomial.decodeCubic 21 atom1465Coded := by decide +kernel
theorem atom1465Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded) := by
  have h := atom1465_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1465Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1466 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1466 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1466 = ((g 9) * (g 11) * (g 12)) := by
  norm_num [atom1466, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1466_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1876885516800 : Int) atom1466) := by
  rw [SparsePolynomial.eval_scale, eval_atom1466]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1466Coded : CoefficientMerge.Poly := [(nat_lit 4212, Int.ofNat (nat_lit 1))]
theorem atom1466Coded_decode : atom1466 = SparsePolynomial.decodeCubic 21 atom1466Coded := by decide +kernel
theorem atom1466Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) := by
  have h := atom1466_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1466Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1467 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1467 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1467 = ((g 9) * (g 11) * (g 13)) := by
  norm_num [atom1467, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1467_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2563079500800 : Int) atom1467) := by
  rw [SparsePolynomial.eval_scale, eval_atom1467]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1467Coded : CoefficientMerge.Poly := [(nat_lit 4213, Int.ofNat (nat_lit 1))]
theorem atom1467Coded_decode : atom1467 = SparsePolynomial.decodeCubic 21 atom1467Coded := by decide +kernel
theorem atom1467Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded) := by
  have h := atom1467_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1467Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1468 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1468 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1468 = ((g 9) * (g 11) * (g 14)) := by
  norm_num [atom1468, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1468_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3249273484800 : Int) atom1468) := by
  rw [SparsePolynomial.eval_scale, eval_atom1468]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1468Coded : CoefficientMerge.Poly := [(nat_lit 4214, Int.ofNat (nat_lit 1))]
theorem atom1468Coded_decode : atom1468 = SparsePolynomial.decodeCubic 21 atom1468Coded := by decide +kernel
theorem atom1468Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) := by
  have h := atom1468_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1468Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1469 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1469 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1469 = ((g 9) * (g 11) * (g 15)) := by
  norm_num [atom1469, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1469_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6681901564800 : Int) atom1469) := by
  rw [SparsePolynomial.eval_scale, eval_atom1469]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1469Coded : CoefficientMerge.Poly := [(nat_lit 4215, Int.ofNat (nat_lit 1))]
theorem atom1469Coded_decode : atom1469 = SparsePolynomial.decodeCubic 21 atom1469Coded := by decide +kernel
theorem atom1469Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) := by
  have h := atom1469_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1469Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1470 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1470 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1470 = ((g 9) * (g 11) * (g 16)) := by
  norm_num [atom1470, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1470_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1017686224800 : Int) atom1470) := by
  rw [SparsePolynomial.eval_scale, eval_atom1470]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1470Coded : CoefficientMerge.Poly := [(nat_lit 4216, Int.ofNat (nat_lit 1))]
theorem atom1470Coded_decode : atom1470 = SparsePolynomial.decodeCubic 21 atom1470Coded := by decide +kernel
theorem atom1470Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded) := by
  have h := atom1470_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1470Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1471 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1471 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1471 = ((g 9) * (g 11) * (g 17)) := by
  norm_num [atom1471, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1471_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12075930115200 : Int) atom1471) := by
  rw [SparsePolynomial.eval_scale, eval_atom1471]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1471Coded : CoefficientMerge.Poly := [(nat_lit 4217, Int.ofNat (nat_lit 1))]
theorem atom1471Coded_decode : atom1471 = SparsePolynomial.decodeCubic 21 atom1471Coded := by decide +kernel
theorem atom1471Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) := by
  have h := atom1471_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1471Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1472 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1472 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1472 = ((g 9) * (g 11) * (g 18)) := by
  norm_num [atom1472, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1472_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10740378448800 : Int) atom1472) := by
  rw [SparsePolynomial.eval_scale, eval_atom1472]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1472Coded : CoefficientMerge.Poly := [(nat_lit 4218, Int.ofNat (nat_lit 1))]
theorem atom1472Coded_decode : atom1472 = SparsePolynomial.decodeCubic 21 atom1472Coded := by decide +kernel
theorem atom1472Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded) := by
  have h := atom1472_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1472Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1473 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1473 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1473 = ((g 9) * (g 11) * (g 19)) := by
  norm_num [atom1473, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1473_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20105092879200 : Int) atom1473) := by
  rw [SparsePolynomial.eval_scale, eval_atom1473]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1473Coded : CoefficientMerge.Poly := [(nat_lit 4219, Int.ofNat (nat_lit 1))]
theorem atom1473Coded_decode : atom1473 = SparsePolynomial.decodeCubic 21 atom1473Coded := by decide +kernel
theorem atom1473Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) := by
  have h := atom1473_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1473Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1474 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1474 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1474 = ((g 9) * (g 11) * (g 20)) := by
  norm_num [atom1474, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1474_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31025632780800 : Int) atom1474) := by
  rw [SparsePolynomial.eval_scale, eval_atom1474]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1474Coded : CoefficientMerge.Poly := [(nat_lit 4220, Int.ofNat (nat_lit 1))]
theorem atom1474Coded_decode : atom1474 = SparsePolynomial.decodeCubic 21 atom1474Coded := by decide +kernel
theorem atom1474Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) := by
  have h := atom1474_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1474Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1475 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1475 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1475 = ((g 9) * (g 12) * (g 12)) := by
  norm_num [atom1475, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1475_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3074342342400 : Int) atom1475) := by
  rw [SparsePolynomial.eval_scale, eval_atom1475]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1475Coded : CoefficientMerge.Poly := [(nat_lit 4233, Int.ofNat (nat_lit 1))]
theorem atom1475Coded_decode : atom1475 = SparsePolynomial.decodeCubic 21 atom1475Coded := by decide +kernel
theorem atom1475Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded) := by
  have h := atom1475_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1475Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1476 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1476 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1476 = ((g 9) * (g 12) * (g 13)) := by
  norm_num [atom1476, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1476_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6498546969600 : Int) atom1476) := by
  rw [SparsePolynomial.eval_scale, eval_atom1476]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1476Coded : CoefficientMerge.Poly := [(nat_lit 4234, Int.ofNat (nat_lit 1))]
theorem atom1476Coded_decode : atom1476 = SparsePolynomial.decodeCubic 21 atom1476Coded := by decide +kernel
theorem atom1476Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) := by
  have h := atom1476_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1476Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1477 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1477 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1477 = ((g 9) * (g 12) * (g 14)) := by
  norm_num [atom1477, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1477_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7275589171200 : Int) atom1477) := by
  rw [SparsePolynomial.eval_scale, eval_atom1477]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1477Coded : CoefficientMerge.Poly := [(nat_lit 4235, Int.ofNat (nat_lit 1))]
theorem atom1477Coded_decode : atom1477 = SparsePolynomial.decodeCubic 21 atom1477Coded := by decide +kernel
theorem atom1477Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded) := by
  have h := atom1477_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1477Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1478 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1478 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1478 = ((g 9) * (g 12) * (g 15)) := by
  norm_num [atom1478, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1478_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8588646595200 : Int) atom1478) := by
  rw [SparsePolynomial.eval_scale, eval_atom1478]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1478Coded : CoefficientMerge.Poly := [(nat_lit 4236, Int.ofNat (nat_lit 1))]
theorem atom1478Coded_decode : atom1478 = SparsePolynomial.decodeCubic 21 atom1478Coded := by decide +kernel
theorem atom1478Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) := by
  have h := atom1478_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1478Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1479 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1479 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1479 = ((g 9) * (g 12) * (g 16)) := by
  norm_num [atom1479, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1479_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6994941380000 : Int) atom1479) := by
  rw [SparsePolynomial.eval_scale, eval_atom1479]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1479Coded : CoefficientMerge.Poly := [(nat_lit 4237, Int.ofNat (nat_lit 1))]
theorem atom1479Coded_decode : atom1479 = SparsePolynomial.decodeCubic 21 atom1479Coded := by decide +kernel
theorem atom1479Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) := by
  have h := atom1479_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1479Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1480 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1480 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1480 = ((g 9) * (g 12) * (g 17)) := by
  norm_num [atom1480, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1480_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18707359395200 : Int) atom1480) := by
  rw [SparsePolynomial.eval_scale, eval_atom1480]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1480Coded : CoefficientMerge.Poly := [(nat_lit 4238, Int.ofNat (nat_lit 1))]
theorem atom1480Coded_decode : atom1480 = SparsePolynomial.decodeCubic 21 atom1480Coded := by decide +kernel
theorem atom1480Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded) := by
  have h := atom1480_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1480Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1481 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1481 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1481 = ((g 9) * (g 12) * (g 18)) := by
  norm_num [atom1481, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1481_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19393808039200 : Int) atom1481) := by
  rw [SparsePolynomial.eval_scale, eval_atom1481]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1481Coded : CoefficientMerge.Poly := [(nat_lit 4239, Int.ofNat (nat_lit 1))]
theorem atom1481Coded_decode : atom1481 = SparsePolynomial.decodeCubic 21 atom1481Coded := by decide +kernel
theorem atom1481Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) := by
  have h := atom1481_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1481Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1482 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1482 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1482 = ((g 9) * (g 12) * (g 19)) := by
  norm_num [atom1482, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1482_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29075845864800 : Int) atom1482) := by
  rw [SparsePolynomial.eval_scale, eval_atom1482]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1482Coded : CoefficientMerge.Poly := [(nat_lit 4240, Int.ofNat (nat_lit 1))]
theorem atom1482Coded_decode : atom1482 = SparsePolynomial.decodeCubic 21 atom1482Coded := by decide +kernel
theorem atom1482Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded) := by
  have h := atom1482_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1482Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1483 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1483 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1483 = ((g 9) * (g 12) * (g 20)) := by
  norm_num [atom1483, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1483_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40801239259200 : Int) atom1483) := by
  rw [SparsePolynomial.eval_scale, eval_atom1483]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1483Coded : CoefficientMerge.Poly := [(nat_lit 4241, Int.ofNat (nat_lit 1))]
theorem atom1483Coded_decode : atom1483 = SparsePolynomial.decodeCubic 21 atom1483Coded := by decide +kernel
theorem atom1483Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) := by
  have h := atom1483_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1483Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1484 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1484 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1484 = ((g 9) * (g 13) * (g 13)) := by
  norm_num [atom1484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1484_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5863944096000 : Int) atom1484) := by
  rw [SparsePolynomial.eval_scale, eval_atom1484]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1484Coded : CoefficientMerge.Poly := [(nat_lit 4255, Int.ofNat (nat_lit 1))]
theorem atom1484Coded_decode : atom1484 = SparsePolynomial.decodeCubic 21 atom1484Coded := by decide +kernel
theorem atom1484Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) := by
  have h := atom1484_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1484Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1485 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1485 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1485 = ((g 9) * (g 13) * (g 14)) := by
  norm_num [atom1485, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1485_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11257079040000 : Int) atom1485) := by
  rw [SparsePolynomial.eval_scale, eval_atom1485]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1485Coded : CoefficientMerge.Poly := [(nat_lit 4256, Int.ofNat (nat_lit 1))]
theorem atom1485Coded_decode : atom1485 = SparsePolynomial.decodeCubic 21 atom1485Coded := by decide +kernel
theorem atom1485Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded) := by
  have h := atom1485_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1485Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1486 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1486 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1486 = ((g 9) * (g 13) * (g 15)) := by
  norm_num [atom1486, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1486_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13909039300800 : Int) atom1486) := by
  rw [SparsePolynomial.eval_scale, eval_atom1486]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1486Coded : CoefficientMerge.Poly := [(nat_lit 4257, Int.ofNat (nat_lit 1))]
theorem atom1486Coded_decode : atom1486 = SparsePolynomial.decodeCubic 21 atom1486Coded := by decide +kernel
theorem atom1486Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) := by
  have h := atom1486_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1486Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1487 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1487 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1487 = ((g 9) * (g 13) * (g 16)) := by
  norm_num [atom1487, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1487_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13518234338400 : Int) atom1487) := by
  rw [SparsePolynomial.eval_scale, eval_atom1487]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1487Coded : CoefficientMerge.Poly := [(nat_lit 4258, Int.ofNat (nat_lit 1))]
theorem atom1487Coded_decode : atom1487 = SparsePolynomial.decodeCubic 21 atom1487Coded := by decide +kernel
theorem atom1487Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded) := by
  have h := atom1487_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1487Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1488 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1488 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1488 = ((g 9) * (g 13) * (g 17)) := by
  norm_num [atom1488, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1488_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29696485795200 : Int) atom1488) := by
  rw [SparsePolynomial.eval_scale, eval_atom1488]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1488Coded : CoefficientMerge.Poly := [(nat_lit 4259, Int.ofNat (nat_lit 1))]
theorem atom1488Coded_decode : atom1488 = SparsePolynomial.decodeCubic 21 atom1488Coded := by decide +kernel
theorem atom1488Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) := by
  have h := atom1488_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1488Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1489 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1489 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1489 = ((g 9) * (g 13) * (g 18)) := by
  norm_num [atom1489, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1489_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32840704461600 : Int) atom1489) := by
  rw [SparsePolynomial.eval_scale, eval_atom1489]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1489Coded : CoefficientMerge.Poly := [(nat_lit 4260, Int.ofNat (nat_lit 1))]
theorem atom1489Coded_decode : atom1489 = SparsePolynomial.decodeCubic 21 atom1489Coded := by decide +kernel
theorem atom1489Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) := by
  have h := atom1489_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1489Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1490 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1490 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1490 = ((g 9) * (g 13) * (g 19)) := by
  norm_num [atom1490, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1490_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37111606192800 : Int) atom1490) := by
  rw [SparsePolynomial.eval_scale, eval_atom1490]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1490Coded : CoefficientMerge.Poly := [(nat_lit 4261, Int.ofNat (nat_lit 1))]
theorem atom1490Coded_decode : atom1490 = SparsePolynomial.decodeCubic 21 atom1490Coded := by decide +kernel
theorem atom1490Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded) := by
  have h := atom1490_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1490Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1491 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1491 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1491 = ((g 9) * (g 13) * (g 20)) := by
  norm_num [atom1491, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1491_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55562141678400 : Int) atom1491) := by
  rw [SparsePolynomial.eval_scale, eval_atom1491]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1491Coded : CoefficientMerge.Poly := [(nat_lit 4262, Int.ofNat (nat_lit 1))]
theorem atom1491Coded_decode : atom1491 = SparsePolynomial.decodeCubic 21 atom1491Coded := by decide +kernel
theorem atom1491Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) := by
  have h := atom1491_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1491Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1492 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1492 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1492 = ((g 9) * (g 14) * (g 14)) := by
  norm_num [atom1492, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1492_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10101226464000 : Int) atom1492) := by
  rw [SparsePolynomial.eval_scale, eval_atom1492]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1492Coded : CoefficientMerge.Poly := [(nat_lit 4277, Int.ofNat (nat_lit 1))]
theorem atom1492Coded_decode : atom1492 = SparsePolynomial.decodeCubic 21 atom1492Coded := by decide +kernel
theorem atom1492Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded) := by
  have h := atom1492_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1492Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1493 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1493 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1493 = ((g 9) * (g 14) * (g 15)) := by
  norm_num [atom1493, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1493_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19117589904000 : Int) atom1493) := by
  rw [SparsePolynomial.eval_scale, eval_atom1493]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1493Coded : CoefficientMerge.Poly := [(nat_lit 4278, Int.ofNat (nat_lit 1))]
theorem atom1493Coded_decode : atom1493 = SparsePolynomial.decodeCubic 21 atom1493Coded := by decide +kernel
theorem atom1493Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) := by
  have h := atom1493_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1493Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1494 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1494 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1494 = ((g 9) * (g 14) * (g 16)) := by
  norm_num [atom1494, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1494_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19922377860000 : Int) atom1494) := by
  rw [SparsePolynomial.eval_scale, eval_atom1494]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1494Coded : CoefficientMerge.Poly := [(nat_lit 4279, Int.ofNat (nat_lit 1))]
theorem atom1494Coded_decode : atom1494 = SparsePolynomial.decodeCubic 21 atom1494Coded := by decide +kernel
theorem atom1494Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) := by
  have h := atom1494_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1494Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1495 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1495 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1495 = ((g 9) * (g 14) * (g 17)) := by
  norm_num [atom1495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1495_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42879142051200 : Int) atom1495) := by
  rw [SparsePolynomial.eval_scale, eval_atom1495]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1495Coded : CoefficientMerge.Poly := [(nat_lit 4280, Int.ofNat (nat_lit 1))]
theorem atom1495Coded_decode : atom1495 = SparsePolynomial.decodeCubic 21 atom1495Coded := by decide +kernel
theorem atom1495Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded) := by
  have h := atom1495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1496 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1496 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1496 = ((g 9) * (g 14) * (g 18)) := by
  norm_num [atom1496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1496_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48700483725600 : Int) atom1496) := by
  rw [SparsePolynomial.eval_scale, eval_atom1496]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1496Coded : CoefficientMerge.Poly := [(nat_lit 4281, Int.ofNat (nat_lit 1))]
theorem atom1496Coded_decode : atom1496 = SparsePolynomial.decodeCubic 21 atom1496Coded := by decide +kernel
theorem atom1496Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) := by
  have h := atom1496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1497 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1497 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1497 = ((g 9) * (g 14) * (g 19)) := by
  norm_num [atom1497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1497_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49598093109600 : Int) atom1497) := by
  rw [SparsePolynomial.eval_scale, eval_atom1497]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1497Coded : CoefficientMerge.Poly := [(nat_lit 4282, Int.ofNat (nat_lit 1))]
theorem atom1497Coded_decode : atom1497 = SparsePolynomial.decodeCubic 21 atom1497Coded := by decide +kernel
theorem atom1497Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded) := by
  have h := atom1497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1498 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1498 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1498 = ((g 9) * (g 14) * (g 20)) := by
  norm_num [atom1498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1498_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74906046734400 : Int) atom1498) := by
  rw [SparsePolynomial.eval_scale, eval_atom1498]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1498Coded : CoefficientMerge.Poly := [(nat_lit 4283, Int.ofNat (nat_lit 1))]
theorem atom1498Coded_decode : atom1498 = SparsePolynomial.decodeCubic 21 atom1498Coded := by decide +kernel
theorem atom1498Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) := by
  have h := atom1498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1499 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1499 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1499 = ((g 9) * (g 15) * (g 15)) := by
  norm_num [atom1499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1499_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16795322611200 : Int) atom1499) := by
  rw [SparsePolynomial.eval_scale, eval_atom1499]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1499Coded : CoefficientMerge.Poly := [(nat_lit 4299, Int.ofNat (nat_lit 1))]
theorem atom1499Coded_decode : atom1499 = SparsePolynomial.decodeCubic 21 atom1499Coded := by decide +kernel
theorem atom1499Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) := by
  have h := atom1499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1500 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1500 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1500 = ((g 9) * (g 15) * (g 16)) := by
  norm_num [atom1500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1500_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35735021557200 : Int) atom1500) := by
  rw [SparsePolynomial.eval_scale, eval_atom1500]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1500Coded : CoefficientMerge.Poly := [(nat_lit 4300, Int.ofNat (nat_lit 1))]
theorem atom1500Coded_decode : atom1500 = SparsePolynomial.decodeCubic 21 atom1500Coded := by decide +kernel
theorem atom1500Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded) := by
  have h := atom1500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1501 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1501 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1501 = ((g 9) * (g 15) * (g 17)) := by
  norm_num [atom1501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1501_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64884545510400 : Int) atom1501) := by
  rw [SparsePolynomial.eval_scale, eval_atom1501]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1501Coded : CoefficientMerge.Poly := [(nat_lit 4301, Int.ofNat (nat_lit 1))]
theorem atom1501Coded_decode : atom1501 = SparsePolynomial.decodeCubic 21 atom1501Coded := by decide +kernel
theorem atom1501Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) := by
  have h := atom1501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1502 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1502 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1502 = ((g 9) * (g 15) * (g 18)) := by
  norm_num [atom1502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1502_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69986611724400 : Int) atom1502) := by
  rw [SparsePolynomial.eval_scale, eval_atom1502]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1502Coded : CoefficientMerge.Poly := [(nat_lit 4302, Int.ofNat (nat_lit 1))]
theorem atom1502Coded_decode : atom1502 = SparsePolynomial.decodeCubic 21 atom1502Coded := by decide +kernel
theorem atom1502Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded) := by
  have h := atom1502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1503 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1503 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1503 = ((g 9) * (g 15) * (g 19)) := by
  norm_num [atom1503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1503_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53647060446000 : Int) atom1503) := by
  rw [SparsePolynomial.eval_scale, eval_atom1503]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1503Coded : CoefficientMerge.Poly := [(nat_lit 4303, Int.ofNat (nat_lit 1))]
theorem atom1503Coded_decode : atom1503 = SparsePolynomial.decodeCubic 21 atom1503Coded := by decide +kernel
theorem atom1503Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) := by
  have h := atom1503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1504 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1504 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1504 = ((g 9) * (g 15) * (g 20)) := by
  norm_num [atom1504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1504_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84256708258800 : Int) atom1504) := by
  rw [SparsePolynomial.eval_scale, eval_atom1504]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1504Coded : CoefficientMerge.Poly := [(nat_lit 4304, Int.ofNat (nat_lit 1))]
theorem atom1504Coded_decode : atom1504 = SparsePolynomial.decodeCubic 21 atom1504Coded := by decide +kernel
theorem atom1504Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) := by
  have h := atom1504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1505 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1505 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1505 = ((g 9) * (g 16) * (g 16)) := by
  norm_num [atom1505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1505_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14605687272960 : Int) atom1505) := by
  rw [SparsePolynomial.eval_scale, eval_atom1505]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1505Coded : CoefficientMerge.Poly := [(nat_lit 4321, Int.ofNat (nat_lit 1))]
theorem atom1505Coded_decode : atom1505 = SparsePolynomial.decodeCubic 21 atom1505Coded := by decide +kernel
theorem atom1505Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded) := by
  have h := atom1505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1506 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1506 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1506 = ((g 9) * (g 16) * (g 17)) := by
  norm_num [atom1506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1506_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55660876311600 : Int) atom1506) := by
  rw [SparsePolynomial.eval_scale, eval_atom1506]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1506Coded : CoefficientMerge.Poly := [(nat_lit 4322, Int.ofNat (nat_lit 1))]
theorem atom1506Coded_decode : atom1506 = SparsePolynomial.decodeCubic 21 atom1506Coded := by decide +kernel
theorem atom1506Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) := by
  have h := atom1506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1507 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1507 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1507 = ((g 9) * (g 16) * (g 18)) := by
  norm_num [atom1507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1507_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65795220880200 : Int) atom1507) := by
  rw [SparsePolynomial.eval_scale, eval_atom1507]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1507Coded : CoefficientMerge.Poly := [(nat_lit 4323, Int.ofNat (nat_lit 1))]
theorem atom1507Coded_decode : atom1507 = SparsePolynomial.decodeCubic 21 atom1507Coded := by decide +kernel
theorem atom1507Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded) := by
  have h := atom1507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1508 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1508 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1508 = ((g 9) * (g 16) * (g 19)) := by
  norm_num [atom1508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1508_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48673825250400 : Int) atom1508) := by
  rw [SparsePolynomial.eval_scale, eval_atom1508]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1508Coded : CoefficientMerge.Poly := [(nat_lit 4324, Int.ofNat (nat_lit 1))]
theorem atom1508Coded_decode : atom1508 = SparsePolynomial.decodeCubic 21 atom1508Coded := by decide +kernel
theorem atom1508Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) := by
  have h := atom1508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1509 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1509 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1509 = ((g 9) * (g 16) * (g 20)) := by
  norm_num [atom1509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1509_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (66408854078700 : Int) atom1509) := by
  rw [SparsePolynomial.eval_scale, eval_atom1509]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1509Coded : CoefficientMerge.Poly := [(nat_lit 4325, Int.ofNat (nat_lit 1))]
theorem atom1509Coded_decode : atom1509 = SparsePolynomial.decodeCubic 21 atom1509Coded := by decide +kernel
theorem atom1509Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) := by
  have h := atom1509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1510 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1510 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1510 = ((g 9) * (g 17) * (g 17)) := by
  norm_num [atom1510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1510_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41744447539200 : Int) atom1510) := by
  rw [SparsePolynomial.eval_scale, eval_atom1510]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1510Coded : CoefficientMerge.Poly := [(nat_lit 4343, Int.ofNat (nat_lit 1))]
theorem atom1510Coded_decode : atom1510 = SparsePolynomial.decodeCubic 21 atom1510Coded := by decide +kernel
theorem atom1510Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded) := by
  have h := atom1510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1511 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1511 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1511 = ((g 9) * (g 17) * (g 18)) := by
  norm_num [atom1511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1511_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76111510784400 : Int) atom1511) := by
  rw [SparsePolynomial.eval_scale, eval_atom1511]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1511Coded : CoefficientMerge.Poly := [(nat_lit 4344, Int.ofNat (nat_lit 1))]
theorem atom1511Coded_decode : atom1511 = SparsePolynomial.decodeCubic 21 atom1511Coded := by decide +kernel
theorem atom1511Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) := by
  have h := atom1511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1512 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1512 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1512 = ((g 9) * (g 17) * (g 19)) := by
  norm_num [atom1512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1512_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52712801442000 : Int) atom1512) := by
  rw [SparsePolynomial.eval_scale, eval_atom1512]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1512Coded : CoefficientMerge.Poly := [(nat_lit 4345, Int.ofNat (nat_lit 1))]
theorem atom1512Coded_decode : atom1512 = SparsePolynomial.decodeCubic 21 atom1512Coded := by decide +kernel
theorem atom1512Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded) := by
  have h := atom1512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1513 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1513 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1513 = ((g 9) * (g 17) * (g 20)) := by
  norm_num [atom1513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1513_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58566148880400 : Int) atom1513) := by
  rw [SparsePolynomial.eval_scale, eval_atom1513]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1513Coded : CoefficientMerge.Poly := [(nat_lit 4346, Int.ofNat (nat_lit 1))]
theorem atom1513Coded_decode : atom1513 = SparsePolynomial.decodeCubic 21 atom1513Coded := by decide +kernel
theorem atom1513Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) := by
  have h := atom1513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1514 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1514 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1514 = ((g 9) * (g 18) * (g 18)) := by
  norm_num [atom1514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1514_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28394930554200 : Int) atom1514) := by
  rw [SparsePolynomial.eval_scale, eval_atom1514]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1514Coded : CoefficientMerge.Poly := [(nat_lit 4365, Int.ofNat (nat_lit 1))]
theorem atom1514Coded_decode : atom1514 = SparsePolynomial.decodeCubic 21 atom1514Coded := by decide +kernel
theorem atom1514Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) := by
  have h := atom1514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1515 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1515 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1515 = ((g 9) * (g 18) * (g 19)) := by
  norm_num [atom1515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1515_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36513604071000 : Int) atom1515) := by
  rw [SparsePolynomial.eval_scale, eval_atom1515]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1515Coded : CoefficientMerge.Poly := [(nat_lit 4366, Int.ofNat (nat_lit 1))]
theorem atom1515Coded_decode : atom1515 = SparsePolynomial.decodeCubic 21 atom1515Coded := by decide +kernel
theorem atom1515Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded) := by
  have h := atom1515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1516 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1516 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1516 = ((g 9) * (g 18) * (g 20)) := by
  norm_num [atom1516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1516_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44758527817500 : Int) atom1516) := by
  rw [SparsePolynomial.eval_scale, eval_atom1516]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1516Coded : CoefficientMerge.Poly := [(nat_lit 4367, Int.ofNat (nat_lit 1))]
theorem atom1516Coded_decode : atom1516 = SparsePolynomial.decodeCubic 21 atom1516Coded := by decide +kernel
theorem atom1516Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) := by
  have h := atom1516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1517 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1517 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1517 = ((g 9) * (g 19) * (g 19)) := by
  norm_num [atom1517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1517_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3308751684000 : Int) atom1517) := by
  rw [SparsePolynomial.eval_scale, eval_atom1517]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1517Coded : CoefficientMerge.Poly := [(nat_lit 4387, Int.ofNat (nat_lit 1))]
theorem atom1517Coded_decode : atom1517 = SparsePolynomial.decodeCubic 21 atom1517Coded := by decide +kernel
theorem atom1517Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded) := by
  have h := atom1517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1518 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1518 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1518 = ((g 9) * (g 19) * (g 20)) := by
  norm_num [atom1518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1518_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15671181626100 : Int) atom1518) := by
  rw [SparsePolynomial.eval_scale, eval_atom1518]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1518Coded : CoefficientMerge.Poly := [(nat_lit 4388, Int.ofNat (nat_lit 1))]
theorem atom1518Coded_decode : atom1518 = SparsePolynomial.decodeCubic 21 atom1518Coded := by decide +kernel
theorem atom1518Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) := by
  have h := atom1518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1519 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1519 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1519 = ((g 9) * (g 20) * (g 20)) := by
  norm_num [atom1519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1519_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8870673060900 : Int) atom1519) := by
  rw [SparsePolynomial.eval_scale, eval_atom1519]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1519Coded : CoefficientMerge.Poly := [(nat_lit 4409, Int.ofNat (nat_lit 1))]
theorem atom1519Coded_decode : atom1519 = SparsePolynomial.decodeCubic 21 atom1519Coded := by decide +kernel
theorem atom1519Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) := by
  have h := atom1519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1520 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1520 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1520 = ((g 10) * (g 10) * (g 10)) := by
  norm_num [atom1520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1520_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (597600864000 : Int) atom1520) := by
  rw [SparsePolynomial.eval_scale, eval_atom1520]
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 10) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1520Coded : CoefficientMerge.Poly := [(nat_lit 4630, Int.ofNat (nat_lit 1))]
theorem atom1520Coded_decode : atom1520 = SparsePolynomial.decodeCubic 21 atom1520Coded := by decide +kernel
theorem atom1520Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded) := by
  have h := atom1520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1521 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1521 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1521 = ((g 10) * (g 10) * (g 11)) := by
  norm_num [atom1521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1521_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1521) := by
  rw [SparsePolynomial.eval_scale, eval_atom1521]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1521Coded : CoefficientMerge.Poly := [(nat_lit 4631, Int.ofNat (nat_lit 1))]
theorem atom1521Coded_decode : atom1521 = SparsePolynomial.decodeCubic 21 atom1521Coded := by decide +kernel
theorem atom1521Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) := by
  have h := atom1521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1522 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1522 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1522 = ((g 10) * (g 10) * (g 15)) := by
  norm_num [atom1522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1522_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3075590700000 : Int) atom1522) := by
  rw [SparsePolynomial.eval_scale, eval_atom1522]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1522Coded : CoefficientMerge.Poly := [(nat_lit 4635, Int.ofNat (nat_lit 1))]
theorem atom1522Coded_decode : atom1522 = SparsePolynomial.decodeCubic 21 atom1522Coded := by decide +kernel
theorem atom1522Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded) := by
  have h := atom1522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1523 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1523 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1523 = ((g 10) * (g 10) * (g 17)) := by
  norm_num [atom1523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1523_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2234314202400 : Int) atom1523) := by
  rw [SparsePolynomial.eval_scale, eval_atom1523]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1523Coded : CoefficientMerge.Poly := [(nat_lit 4637, Int.ofNat (nat_lit 1))]
theorem atom1523Coded_decode : atom1523 = SparsePolynomial.decodeCubic 21 atom1523Coded := by decide +kernel
theorem atom1523Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) := by
  have h := atom1523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1524 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1524 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1524 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom1524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1524_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (938442758400 : Int) atom1524) := by
  rw [SparsePolynomial.eval_scale, eval_atom1524]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1524Coded : CoefficientMerge.Poly := [(nat_lit 4652, Int.ofNat (nat_lit 1))]
theorem atom1524Coded_decode : atom1524 = SparsePolynomial.decodeCubic 21 atom1524Coded := by decide +kernel
theorem atom1524Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) := by
  have h := atom1524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1525 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1525 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1525 = ((g 10) * (g 11) * (g 13)) := by
  norm_num [atom1525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1525_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1525) := by
  rw [SparsePolynomial.eval_scale, eval_atom1525]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1525Coded : CoefficientMerge.Poly := [(nat_lit 4654, Int.ofNat (nat_lit 1))]
theorem atom1525Coded_decode : atom1525 = SparsePolynomial.decodeCubic 21 atom1525Coded := by decide +kernel
theorem atom1525Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded) := by
  have h := atom1525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1526 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1526 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1526 = ((g 10) * (g 11) * (g 14)) := by
  norm_num [atom1526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1526_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854359833600 : Int) atom1526) := by
  rw [SparsePolynomial.eval_scale, eval_atom1526]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1526Coded : CoefficientMerge.Poly := [(nat_lit 4655, Int.ofNat (nat_lit 1))]
theorem atom1526Coded_decode : atom1526 = SparsePolynomial.decodeCubic 21 atom1526Coded := by decide +kernel
theorem atom1526Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) := by
  have h := atom1526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1527 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1527 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1527 = ((g 10) * (g 11) * (g 15)) := by
  norm_num [atom1527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1527_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5701373284320 : Int) atom1527) := by
  rw [SparsePolynomial.eval_scale, eval_atom1527]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1527Coded : CoefficientMerge.Poly := [(nat_lit 4656, Int.ofNat (nat_lit 1))]
theorem atom1527Coded_decode : atom1527 = SparsePolynomial.decodeCubic 21 atom1527Coded := by decide +kernel
theorem atom1527Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded) := by
  have h := atom1527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1528 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1528 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1528 = ((g 10) * (g 11) * (g 17)) := by
  norm_num [atom1528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1528_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10571867661600 : Int) atom1528) := by
  rw [SparsePolynomial.eval_scale, eval_atom1528]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1528Coded : CoefficientMerge.Poly := [(nat_lit 4658, Int.ofNat (nat_lit 1))]
theorem atom1528Coded_decode : atom1528 = SparsePolynomial.decodeCubic 21 atom1528Coded := by decide +kernel
theorem atom1528Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) := by
  have h := atom1528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1529 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1529 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1529 = ((g 10) * (g 11) * (g 18)) := by
  norm_num [atom1529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1529_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5786258284800 : Int) atom1529) := by
  rw [SparsePolynomial.eval_scale, eval_atom1529]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 10) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1529Coded : CoefficientMerge.Poly := [(nat_lit 4659, Int.ofNat (nat_lit 1))]
theorem atom1529Coded_decode : atom1529 = SparsePolynomial.decodeCubic 21 atom1529Coded := by decide +kernel
theorem atom1529Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) := by
  have h := atom1529_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1529Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1530 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1530 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1530 = ((g 10) * (g 11) * (g 19)) := by
  norm_num [atom1530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1530_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171238059520 : Int) atom1530) := by
  rw [SparsePolynomial.eval_scale, eval_atom1530]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 10) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1530Coded : CoefficientMerge.Poly := [(nat_lit 4660, Int.ofNat (nat_lit 1))]
theorem atom1530Coded_decode : atom1530 = SparsePolynomial.decodeCubic 21 atom1530Coded := by decide +kernel
theorem atom1530Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded) := by
  have h := atom1530_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1530Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1531 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1531 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1531 = ((g 10) * (g 11) * (g 20)) := by
  norm_num [atom1531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1531_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391151612800 : Int) atom1531) := by
  rw [SparsePolynomial.eval_scale, eval_atom1531]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 10) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1531Coded : CoefficientMerge.Poly := [(nat_lit 4661, Int.ofNat (nat_lit 1))]
theorem atom1531Coded_decode : atom1531 = SparsePolynomial.decodeCubic 21 atom1531Coded := by decide +kernel
theorem atom1531Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) := by
  have h := atom1531_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1531Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1532 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1532 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1532 = ((g 10) * (g 12) * (g 12)) := by
  norm_num [atom1532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1532_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1365622675200 : Int) atom1532) := by
  rw [SparsePolynomial.eval_scale, eval_atom1532]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1532Coded : CoefficientMerge.Poly := [(nat_lit 4674, Int.ofNat (nat_lit 1))]
theorem atom1532Coded_decode : atom1532 = SparsePolynomial.decodeCubic 21 atom1532Coded := by decide +kernel
theorem atom1532Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded) := by
  have h := atom1532_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1532Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1533 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1533 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1533 = ((g 10) * (g 12) * (g 13)) := by
  norm_num [atom1533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1533_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2990259417600 : Int) atom1533) := by
  rw [SparsePolynomial.eval_scale, eval_atom1533]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1533Coded : CoefficientMerge.Poly := [(nat_lit 4675, Int.ofNat (nat_lit 1))]
theorem atom1533Coded_decode : atom1533 = SparsePolynomial.decodeCubic 21 atom1533Coded := by decide +kernel
theorem atom1533Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) := by
  have h := atom1533_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1533Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1534 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1534 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1534 = ((g 10) * (g 12) * (g 14)) := by
  norm_num [atom1534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1534_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3676453401600 : Int) atom1534) := by
  rw [SparsePolynomial.eval_scale, eval_atom1534]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1534Coded : CoefficientMerge.Poly := [(nat_lit 4676, Int.ofNat (nat_lit 1))]
theorem atom1534Coded_decode : atom1534 = SparsePolynomial.decodeCubic 21 atom1534Coded := by decide +kernel
theorem atom1534Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) := by
  have h := atom1534_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1534Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1535 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1535 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1535 = ((g 10) * (g 12) * (g 15)) := by
  norm_num [atom1535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1535_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3338277354720 : Int) atom1535) := by
  rw [SparsePolynomial.eval_scale, eval_atom1535]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1535Coded : CoefficientMerge.Poly := [(nat_lit 4677, Int.ofNat (nat_lit 1))]
theorem atom1535Coded_decode : atom1535 = SparsePolynomial.decodeCubic 21 atom1535Coded := by decide +kernel
theorem atom1535Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded) := by
  have h := atom1535_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1535Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block020 : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 182739160800)), (nat_lit 4189, Int.ofNat (nat_lit 770276908800)), (nat_lit 4192, Int.ofNat (nat_lit 427179916800)), (nat_lit 4193, Int.ofNat (nat_lit 854359833600)), (nat_lit 4194, Int.ofNat (nat_lit 5669444229120)), (nat_lit 4196, Int.ofNat (nat_lit 6132165580800)), (nat_lit 4197, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4198, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4199, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4211, Int.ofNat (nat_lit 1533788524800)), (nat_lit 4212, Int.ofNat (nat_lit 1876885516800)), (nat_lit 4213, Int.ofNat (nat_lit 2563079500800)), (nat_lit 4214, Int.ofNat (nat_lit 3249273484800)), (nat_lit 4215, Int.ofNat (nat_lit 6681901564800)), (nat_lit 4216, Int.ofNat (nat_lit 1017686224800)), (nat_lit 4217, Int.ofNat (nat_lit 12075930115200)), (nat_lit 4218, Int.ofNat (nat_lit 10740378448800)), (nat_lit 4219, Int.ofNat (nat_lit 20105092879200)), (nat_lit 4220, Int.ofNat (nat_lit 31025632780800)), (nat_lit 4233, Int.ofNat (nat_lit 3074342342400)), (nat_lit 4234, Int.ofNat (nat_lit 6498546969600)), (nat_lit 4235, Int.ofNat (nat_lit 7275589171200)), (nat_lit 4236, Int.ofNat (nat_lit 8588646595200)), (nat_lit 4237, Int.ofNat (nat_lit 6994941380000)), (nat_lit 4238, Int.ofNat (nat_lit 18707359395200)), (nat_lit 4239, Int.ofNat (nat_lit 19393808039200)), (nat_lit 4240, Int.ofNat (nat_lit 29075845864800)), (nat_lit 4241, Int.ofNat (nat_lit 40801239259200)), (nat_lit 4255, Int.ofNat (nat_lit 5863944096000)), (nat_lit 4256, Int.ofNat (nat_lit 11257079040000)), (nat_lit 4257, Int.ofNat (nat_lit 13909039300800)), (nat_lit 4258, Int.ofNat (nat_lit 13518234338400)), (nat_lit 4259, Int.ofNat (nat_lit 29696485795200)), (nat_lit 4260, Int.ofNat (nat_lit 32840704461600)), (nat_lit 4261, Int.ofNat (nat_lit 37111606192800)), (nat_lit 4262, Int.ofNat (nat_lit 55562141678400)), (nat_lit 4277, Int.ofNat (nat_lit 10101226464000)), (nat_lit 4278, Int.ofNat (nat_lit 19117589904000)), (nat_lit 4279, Int.ofNat (nat_lit 19922377860000)), (nat_lit 4280, Int.ofNat (nat_lit 42879142051200)), (nat_lit 4281, Int.ofNat (nat_lit 48700483725600)), (nat_lit 4282, Int.ofNat (nat_lit 49598093109600)), (nat_lit 4283, Int.ofNat (nat_lit 74906046734400)), (nat_lit 4299, Int.ofNat (nat_lit 16795322611200)), (nat_lit 4300, Int.ofNat (nat_lit 35735021557200)), (nat_lit 4301, Int.ofNat (nat_lit 64884545510400)), (nat_lit 4302, Int.ofNat (nat_lit 69986611724400)), (nat_lit 4303, Int.ofNat (nat_lit 53647060446000)), (nat_lit 4304, Int.ofNat (nat_lit 84256708258800)), (nat_lit 4321, Int.ofNat (nat_lit 14605687272960)), (nat_lit 4322, Int.ofNat (nat_lit 55660876311600)), (nat_lit 4323, Int.ofNat (nat_lit 65795220880200)), (nat_lit 4324, Int.ofNat (nat_lit 48673825250400)), (nat_lit 4325, Int.ofNat (nat_lit 66408854078700)), (nat_lit 4343, Int.ofNat (nat_lit 41744447539200)), (nat_lit 4344, Int.ofNat (nat_lit 76111510784400)), (nat_lit 4345, Int.ofNat (nat_lit 52712801442000)), (nat_lit 4346, Int.ofNat (nat_lit 58566148880400)), (nat_lit 4365, Int.ofNat (nat_lit 28394930554200)), (nat_lit 4366, Int.ofNat (nat_lit 36513604071000)), (nat_lit 4367, Int.ofNat (nat_lit 44758527817500)), (nat_lit 4387, Int.ofNat (nat_lit 3308751684000)), (nat_lit 4388, Int.ofNat (nat_lit 15671181626100)), (nat_lit 4409, Int.ofNat (nat_lit 8870673060900)), (nat_lit 4630, Int.ofNat (nat_lit 597600864000)), (nat_lit 4631, Int.ofNat (nat_lit 427179916800)), (nat_lit 4635, Int.ofNat (nat_lit 3075590700000)), (nat_lit 4637, Int.ofNat (nat_lit 2234314202400)), (nat_lit 4652, Int.ofNat (nat_lit 938442758400)), (nat_lit 4654, Int.ofNat (nat_lit 427179916800)), (nat_lit 4655, Int.ofNat (nat_lit 854359833600)), (nat_lit 4656, Int.ofNat (nat_lit 5701373284320)), (nat_lit 4658, Int.ofNat (nat_lit 10571867661600)), (nat_lit 4659, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4660, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4661, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4674, Int.ofNat (nat_lit 1365622675200)), (nat_lit 4675, Int.ofNat (nat_lit 2990259417600)), (nat_lit 4676, Int.ofNat (nat_lit 3676453401600)), (nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
def block020_data_flat000 : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 182739160800))]
theorem block020_data_flat000_step : block020_data_flat000 = (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) := by decide +kernel
theorem block020_data_flat000_original : block020_data_flat000 = (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) := by
  rw [block020_data_flat000_step]
def block020_data_flat001 : CoefficientMerge.Poly := [(nat_lit 4189, Int.ofNat (nat_lit 770276908800))]
theorem block020_data_flat001_step : block020_data_flat001 = (CoefficientMerge.scale (770276908800 : Int) atom1457Coded) := by decide +kernel
theorem block020_data_flat001_original : block020_data_flat001 = (CoefficientMerge.scale (770276908800 : Int) atom1457Coded) := by
  rw [block020_data_flat001_step]
def block020_data_flat002 : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 182739160800)), (nat_lit 4189, Int.ofNat (nat_lit 770276908800))]
theorem block020_data_flat002_step : block020_data_flat002 = (CoefficientMerge.fastMerge block020_data_flat000 block020_data_flat001) := by decide +kernel
theorem block020_data_flat002_original : block020_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded)) := by
  rw [block020_data_flat002_step, block020_data_flat000_original, block020_data_flat001_original]
def block020_data_flat003 : CoefficientMerge.Poly := [(nat_lit 4192, Int.ofNat (nat_lit 427179916800))]
theorem block020_data_flat003_step : block020_data_flat003 = (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) := by decide +kernel
theorem block020_data_flat003_original : block020_data_flat003 = (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) := by
  rw [block020_data_flat003_step]
def block020_data_flat004 : CoefficientMerge.Poly := [(nat_lit 4193, Int.ofNat (nat_lit 854359833600))]
theorem block020_data_flat004_step : block020_data_flat004 = (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) := by decide +kernel
theorem block020_data_flat004_original : block020_data_flat004 = (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) := by
  rw [block020_data_flat004_step]
def block020_data_flat005 : CoefficientMerge.Poly := [(nat_lit 4194, Int.ofNat (nat_lit 5669444229120))]
theorem block020_data_flat005_step : block020_data_flat005 = (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded) := by decide +kernel
theorem block020_data_flat005_original : block020_data_flat005 = (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded) := by
  rw [block020_data_flat005_step]
def block020_data_flat006 : CoefficientMerge.Poly := [(nat_lit 4193, Int.ofNat (nat_lit 854359833600)), (nat_lit 4194, Int.ofNat (nat_lit 5669444229120))]
theorem block020_data_flat006_step : block020_data_flat006 = (CoefficientMerge.fastMerge block020_data_flat004 block020_data_flat005) := by decide +kernel
theorem block020_data_flat006_original : block020_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded)) := by
  rw [block020_data_flat006_step, block020_data_flat004_original, block020_data_flat005_original]
def block020_data_flat007 : CoefficientMerge.Poly := [(nat_lit 4192, Int.ofNat (nat_lit 427179916800)), (nat_lit 4193, Int.ofNat (nat_lit 854359833600)), (nat_lit 4194, Int.ofNat (nat_lit 5669444229120))]
theorem block020_data_flat007_step : block020_data_flat007 = (CoefficientMerge.fastMerge block020_data_flat003 block020_data_flat006) := by decide +kernel
theorem block020_data_flat007_original : block020_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded))) := by
  rw [block020_data_flat007_step, block020_data_flat003_original, block020_data_flat006_original]
def block020_data_flat008 : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 182739160800)), (nat_lit 4189, Int.ofNat (nat_lit 770276908800)), (nat_lit 4192, Int.ofNat (nat_lit 427179916800)), (nat_lit 4193, Int.ofNat (nat_lit 854359833600)), (nat_lit 4194, Int.ofNat (nat_lit 5669444229120))]
theorem block020_data_flat008_step : block020_data_flat008 = (CoefficientMerge.fastMerge block020_data_flat002 block020_data_flat007) := by decide +kernel
theorem block020_data_flat008_original : block020_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded)))) := by
  rw [block020_data_flat008_step, block020_data_flat002_original, block020_data_flat007_original]
def block020_data_flat009 : CoefficientMerge.Poly := [(nat_lit 4196, Int.ofNat (nat_lit 6132165580800))]
theorem block020_data_flat009_step : block020_data_flat009 = (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) := by decide +kernel
theorem block020_data_flat009_original : block020_data_flat009 = (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) := by
  rw [block020_data_flat009_step]
def block020_data_flat010 : CoefficientMerge.Poly := [(nat_lit 4197, Int.ofNat (nat_lit 5786258284800))]
theorem block020_data_flat010_step : block020_data_flat010 = (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded) := by decide +kernel
theorem block020_data_flat010_original : block020_data_flat010 = (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded) := by
  rw [block020_data_flat010_step]
def block020_data_flat011 : CoefficientMerge.Poly := [(nat_lit 4196, Int.ofNat (nat_lit 6132165580800)), (nat_lit 4197, Int.ofNat (nat_lit 5786258284800))]
theorem block020_data_flat011_step : block020_data_flat011 = (CoefficientMerge.fastMerge block020_data_flat009 block020_data_flat010) := by decide +kernel
theorem block020_data_flat011_original : block020_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded)) := by
  rw [block020_data_flat011_step, block020_data_flat009_original, block020_data_flat010_original]
def block020_data_flat012 : CoefficientMerge.Poly := [(nat_lit 4198, Int.ofNat (nat_lit 11171238059520))]
theorem block020_data_flat012_step : block020_data_flat012 = (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) := by decide +kernel
theorem block020_data_flat012_original : block020_data_flat012 = (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) := by
  rw [block020_data_flat012_step]
def block020_data_flat013 : CoefficientMerge.Poly := [(nat_lit 4199, Int.ofNat (nat_lit 17391151612800))]
theorem block020_data_flat013_step : block020_data_flat013 = (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) := by decide +kernel
theorem block020_data_flat013_original : block020_data_flat013 = (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) := by
  rw [block020_data_flat013_step]
def block020_data_flat014 : CoefficientMerge.Poly := [(nat_lit 4211, Int.ofNat (nat_lit 1533788524800))]
theorem block020_data_flat014_step : block020_data_flat014 = (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded) := by decide +kernel
theorem block020_data_flat014_original : block020_data_flat014 = (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded) := by
  rw [block020_data_flat014_step]
def block020_data_flat015 : CoefficientMerge.Poly := [(nat_lit 4199, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4211, Int.ofNat (nat_lit 1533788524800))]
theorem block020_data_flat015_step : block020_data_flat015 = (CoefficientMerge.fastMerge block020_data_flat013 block020_data_flat014) := by decide +kernel
theorem block020_data_flat015_original : block020_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded)) := by
  rw [block020_data_flat015_step, block020_data_flat013_original, block020_data_flat014_original]
def block020_data_flat016 : CoefficientMerge.Poly := [(nat_lit 4198, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4199, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4211, Int.ofNat (nat_lit 1533788524800))]
theorem block020_data_flat016_step : block020_data_flat016 = (CoefficientMerge.fastMerge block020_data_flat012 block020_data_flat015) := by decide +kernel
theorem block020_data_flat016_original : block020_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded))) := by
  rw [block020_data_flat016_step, block020_data_flat012_original, block020_data_flat015_original]
def block020_data_flat017 : CoefficientMerge.Poly := [(nat_lit 4196, Int.ofNat (nat_lit 6132165580800)), (nat_lit 4197, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4198, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4199, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4211, Int.ofNat (nat_lit 1533788524800))]
theorem block020_data_flat017_step : block020_data_flat017 = (CoefficientMerge.fastMerge block020_data_flat011 block020_data_flat016) := by decide +kernel
theorem block020_data_flat017_original : block020_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded)))) := by
  rw [block020_data_flat017_step, block020_data_flat011_original, block020_data_flat016_original]
def block020_data_flat018 : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 182739160800)), (nat_lit 4189, Int.ofNat (nat_lit 770276908800)), (nat_lit 4192, Int.ofNat (nat_lit 427179916800)), (nat_lit 4193, Int.ofNat (nat_lit 854359833600)), (nat_lit 4194, Int.ofNat (nat_lit 5669444229120)), (nat_lit 4196, Int.ofNat (nat_lit 6132165580800)), (nat_lit 4197, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4198, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4199, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4211, Int.ofNat (nat_lit 1533788524800))]
theorem block020_data_flat018_step : block020_data_flat018 = (CoefficientMerge.fastMerge block020_data_flat008 block020_data_flat017) := by decide +kernel
theorem block020_data_flat018_original : block020_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded))))) := by
  rw [block020_data_flat018_step, block020_data_flat008_original, block020_data_flat017_original]
def block020_data_flat019 : CoefficientMerge.Poly := [(nat_lit 4212, Int.ofNat (nat_lit 1876885516800))]
theorem block020_data_flat019_step : block020_data_flat019 = (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) := by decide +kernel
theorem block020_data_flat019_original : block020_data_flat019 = (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) := by
  rw [block020_data_flat019_step]
def block020_data_flat020 : CoefficientMerge.Poly := [(nat_lit 4213, Int.ofNat (nat_lit 2563079500800))]
theorem block020_data_flat020_step : block020_data_flat020 = (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded) := by decide +kernel
theorem block020_data_flat020_original : block020_data_flat020 = (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded) := by
  rw [block020_data_flat020_step]
def block020_data_flat021 : CoefficientMerge.Poly := [(nat_lit 4212, Int.ofNat (nat_lit 1876885516800)), (nat_lit 4213, Int.ofNat (nat_lit 2563079500800))]
theorem block020_data_flat021_step : block020_data_flat021 = (CoefficientMerge.fastMerge block020_data_flat019 block020_data_flat020) := by decide +kernel
theorem block020_data_flat021_original : block020_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded)) := by
  rw [block020_data_flat021_step, block020_data_flat019_original, block020_data_flat020_original]
def block020_data_flat022 : CoefficientMerge.Poly := [(nat_lit 4214, Int.ofNat (nat_lit 3249273484800))]
theorem block020_data_flat022_step : block020_data_flat022 = (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) := by decide +kernel
theorem block020_data_flat022_original : block020_data_flat022 = (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) := by
  rw [block020_data_flat022_step]
def block020_data_flat023 : CoefficientMerge.Poly := [(nat_lit 4215, Int.ofNat (nat_lit 6681901564800))]
theorem block020_data_flat023_step : block020_data_flat023 = (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) := by decide +kernel
theorem block020_data_flat023_original : block020_data_flat023 = (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) := by
  rw [block020_data_flat023_step]
def block020_data_flat024 : CoefficientMerge.Poly := [(nat_lit 4216, Int.ofNat (nat_lit 1017686224800))]
theorem block020_data_flat024_step : block020_data_flat024 = (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded) := by decide +kernel
theorem block020_data_flat024_original : block020_data_flat024 = (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded) := by
  rw [block020_data_flat024_step]
def block020_data_flat025 : CoefficientMerge.Poly := [(nat_lit 4215, Int.ofNat (nat_lit 6681901564800)), (nat_lit 4216, Int.ofNat (nat_lit 1017686224800))]
theorem block020_data_flat025_step : block020_data_flat025 = (CoefficientMerge.fastMerge block020_data_flat023 block020_data_flat024) := by decide +kernel
theorem block020_data_flat025_original : block020_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded)) := by
  rw [block020_data_flat025_step, block020_data_flat023_original, block020_data_flat024_original]
def block020_data_flat026 : CoefficientMerge.Poly := [(nat_lit 4214, Int.ofNat (nat_lit 3249273484800)), (nat_lit 4215, Int.ofNat (nat_lit 6681901564800)), (nat_lit 4216, Int.ofNat (nat_lit 1017686224800))]
theorem block020_data_flat026_step : block020_data_flat026 = (CoefficientMerge.fastMerge block020_data_flat022 block020_data_flat025) := by decide +kernel
theorem block020_data_flat026_original : block020_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded))) := by
  rw [block020_data_flat026_step, block020_data_flat022_original, block020_data_flat025_original]
def block020_data_flat027 : CoefficientMerge.Poly := [(nat_lit 4212, Int.ofNat (nat_lit 1876885516800)), (nat_lit 4213, Int.ofNat (nat_lit 2563079500800)), (nat_lit 4214, Int.ofNat (nat_lit 3249273484800)), (nat_lit 4215, Int.ofNat (nat_lit 6681901564800)), (nat_lit 4216, Int.ofNat (nat_lit 1017686224800))]
theorem block020_data_flat027_step : block020_data_flat027 = (CoefficientMerge.fastMerge block020_data_flat021 block020_data_flat026) := by decide +kernel
theorem block020_data_flat027_original : block020_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded)))) := by
  rw [block020_data_flat027_step, block020_data_flat021_original, block020_data_flat026_original]
def block020_data_flat028 : CoefficientMerge.Poly := [(nat_lit 4217, Int.ofNat (nat_lit 12075930115200))]
theorem block020_data_flat028_step : block020_data_flat028 = (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) := by decide +kernel
theorem block020_data_flat028_original : block020_data_flat028 = (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) := by
  rw [block020_data_flat028_step]
def block020_data_flat029 : CoefficientMerge.Poly := [(nat_lit 4218, Int.ofNat (nat_lit 10740378448800))]
theorem block020_data_flat029_step : block020_data_flat029 = (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded) := by decide +kernel
theorem block020_data_flat029_original : block020_data_flat029 = (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded) := by
  rw [block020_data_flat029_step]
def block020_data_flat030 : CoefficientMerge.Poly := [(nat_lit 4217, Int.ofNat (nat_lit 12075930115200)), (nat_lit 4218, Int.ofNat (nat_lit 10740378448800))]
theorem block020_data_flat030_step : block020_data_flat030 = (CoefficientMerge.fastMerge block020_data_flat028 block020_data_flat029) := by decide +kernel
theorem block020_data_flat030_original : block020_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded)) := by
  rw [block020_data_flat030_step, block020_data_flat028_original, block020_data_flat029_original]
def block020_data_flat031 : CoefficientMerge.Poly := [(nat_lit 4219, Int.ofNat (nat_lit 20105092879200))]
theorem block020_data_flat031_step : block020_data_flat031 = (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) := by decide +kernel
theorem block020_data_flat031_original : block020_data_flat031 = (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) := by
  rw [block020_data_flat031_step]
def block020_data_flat032 : CoefficientMerge.Poly := [(nat_lit 4220, Int.ofNat (nat_lit 31025632780800))]
theorem block020_data_flat032_step : block020_data_flat032 = (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) := by decide +kernel
theorem block020_data_flat032_original : block020_data_flat032 = (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) := by
  rw [block020_data_flat032_step]
def block020_data_flat033 : CoefficientMerge.Poly := [(nat_lit 4233, Int.ofNat (nat_lit 3074342342400))]
theorem block020_data_flat033_step : block020_data_flat033 = (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded) := by decide +kernel
theorem block020_data_flat033_original : block020_data_flat033 = (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded) := by
  rw [block020_data_flat033_step]
def block020_data_flat034 : CoefficientMerge.Poly := [(nat_lit 4220, Int.ofNat (nat_lit 31025632780800)), (nat_lit 4233, Int.ofNat (nat_lit 3074342342400))]
theorem block020_data_flat034_step : block020_data_flat034 = (CoefficientMerge.fastMerge block020_data_flat032 block020_data_flat033) := by decide +kernel
theorem block020_data_flat034_original : block020_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded)) := by
  rw [block020_data_flat034_step, block020_data_flat032_original, block020_data_flat033_original]
def block020_data_flat035 : CoefficientMerge.Poly := [(nat_lit 4219, Int.ofNat (nat_lit 20105092879200)), (nat_lit 4220, Int.ofNat (nat_lit 31025632780800)), (nat_lit 4233, Int.ofNat (nat_lit 3074342342400))]
theorem block020_data_flat035_step : block020_data_flat035 = (CoefficientMerge.fastMerge block020_data_flat031 block020_data_flat034) := by decide +kernel
theorem block020_data_flat035_original : block020_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded))) := by
  rw [block020_data_flat035_step, block020_data_flat031_original, block020_data_flat034_original]
def block020_data_flat036 : CoefficientMerge.Poly := [(nat_lit 4217, Int.ofNat (nat_lit 12075930115200)), (nat_lit 4218, Int.ofNat (nat_lit 10740378448800)), (nat_lit 4219, Int.ofNat (nat_lit 20105092879200)), (nat_lit 4220, Int.ofNat (nat_lit 31025632780800)), (nat_lit 4233, Int.ofNat (nat_lit 3074342342400))]
theorem block020_data_flat036_step : block020_data_flat036 = (CoefficientMerge.fastMerge block020_data_flat030 block020_data_flat035) := by decide +kernel
theorem block020_data_flat036_original : block020_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded)))) := by
  rw [block020_data_flat036_step, block020_data_flat030_original, block020_data_flat035_original]
def block020_data_flat037 : CoefficientMerge.Poly := [(nat_lit 4212, Int.ofNat (nat_lit 1876885516800)), (nat_lit 4213, Int.ofNat (nat_lit 2563079500800)), (nat_lit 4214, Int.ofNat (nat_lit 3249273484800)), (nat_lit 4215, Int.ofNat (nat_lit 6681901564800)), (nat_lit 4216, Int.ofNat (nat_lit 1017686224800)), (nat_lit 4217, Int.ofNat (nat_lit 12075930115200)), (nat_lit 4218, Int.ofNat (nat_lit 10740378448800)), (nat_lit 4219, Int.ofNat (nat_lit 20105092879200)), (nat_lit 4220, Int.ofNat (nat_lit 31025632780800)), (nat_lit 4233, Int.ofNat (nat_lit 3074342342400))]
theorem block020_data_flat037_step : block020_data_flat037 = (CoefficientMerge.fastMerge block020_data_flat027 block020_data_flat036) := by decide +kernel
theorem block020_data_flat037_original : block020_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded))))) := by
  rw [block020_data_flat037_step, block020_data_flat027_original, block020_data_flat036_original]
def block020_data_flat038 : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 182739160800)), (nat_lit 4189, Int.ofNat (nat_lit 770276908800)), (nat_lit 4192, Int.ofNat (nat_lit 427179916800)), (nat_lit 4193, Int.ofNat (nat_lit 854359833600)), (nat_lit 4194, Int.ofNat (nat_lit 5669444229120)), (nat_lit 4196, Int.ofNat (nat_lit 6132165580800)), (nat_lit 4197, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4198, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4199, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4211, Int.ofNat (nat_lit 1533788524800)), (nat_lit 4212, Int.ofNat (nat_lit 1876885516800)), (nat_lit 4213, Int.ofNat (nat_lit 2563079500800)), (nat_lit 4214, Int.ofNat (nat_lit 3249273484800)), (nat_lit 4215, Int.ofNat (nat_lit 6681901564800)), (nat_lit 4216, Int.ofNat (nat_lit 1017686224800)), (nat_lit 4217, Int.ofNat (nat_lit 12075930115200)), (nat_lit 4218, Int.ofNat (nat_lit 10740378448800)), (nat_lit 4219, Int.ofNat (nat_lit 20105092879200)), (nat_lit 4220, Int.ofNat (nat_lit 31025632780800)), (nat_lit 4233, Int.ofNat (nat_lit 3074342342400))]
theorem block020_data_flat038_step : block020_data_flat038 = (CoefficientMerge.fastMerge block020_data_flat018 block020_data_flat037) := by decide +kernel
theorem block020_data_flat038_original : block020_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded)))))) := by
  rw [block020_data_flat038_step, block020_data_flat018_original, block020_data_flat037_original]
def block020_data_flat039 : CoefficientMerge.Poly := [(nat_lit 4234, Int.ofNat (nat_lit 6498546969600))]
theorem block020_data_flat039_step : block020_data_flat039 = (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) := by decide +kernel
theorem block020_data_flat039_original : block020_data_flat039 = (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) := by
  rw [block020_data_flat039_step]
def block020_data_flat040 : CoefficientMerge.Poly := [(nat_lit 4235, Int.ofNat (nat_lit 7275589171200))]
theorem block020_data_flat040_step : block020_data_flat040 = (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded) := by decide +kernel
theorem block020_data_flat040_original : block020_data_flat040 = (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded) := by
  rw [block020_data_flat040_step]
def block020_data_flat041 : CoefficientMerge.Poly := [(nat_lit 4234, Int.ofNat (nat_lit 6498546969600)), (nat_lit 4235, Int.ofNat (nat_lit 7275589171200))]
theorem block020_data_flat041_step : block020_data_flat041 = (CoefficientMerge.fastMerge block020_data_flat039 block020_data_flat040) := by decide +kernel
theorem block020_data_flat041_original : block020_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded)) := by
  rw [block020_data_flat041_step, block020_data_flat039_original, block020_data_flat040_original]
def block020_data_flat042 : CoefficientMerge.Poly := [(nat_lit 4236, Int.ofNat (nat_lit 8588646595200))]
theorem block020_data_flat042_step : block020_data_flat042 = (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) := by decide +kernel
theorem block020_data_flat042_original : block020_data_flat042 = (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) := by
  rw [block020_data_flat042_step]
def block020_data_flat043 : CoefficientMerge.Poly := [(nat_lit 4237, Int.ofNat (nat_lit 6994941380000))]
theorem block020_data_flat043_step : block020_data_flat043 = (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) := by decide +kernel
theorem block020_data_flat043_original : block020_data_flat043 = (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) := by
  rw [block020_data_flat043_step]
def block020_data_flat044 : CoefficientMerge.Poly := [(nat_lit 4238, Int.ofNat (nat_lit 18707359395200))]
theorem block020_data_flat044_step : block020_data_flat044 = (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded) := by decide +kernel
theorem block020_data_flat044_original : block020_data_flat044 = (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded) := by
  rw [block020_data_flat044_step]
def block020_data_flat045 : CoefficientMerge.Poly := [(nat_lit 4237, Int.ofNat (nat_lit 6994941380000)), (nat_lit 4238, Int.ofNat (nat_lit 18707359395200))]
theorem block020_data_flat045_step : block020_data_flat045 = (CoefficientMerge.fastMerge block020_data_flat043 block020_data_flat044) := by decide +kernel
theorem block020_data_flat045_original : block020_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded)) := by
  rw [block020_data_flat045_step, block020_data_flat043_original, block020_data_flat044_original]
def block020_data_flat046 : CoefficientMerge.Poly := [(nat_lit 4236, Int.ofNat (nat_lit 8588646595200)), (nat_lit 4237, Int.ofNat (nat_lit 6994941380000)), (nat_lit 4238, Int.ofNat (nat_lit 18707359395200))]
theorem block020_data_flat046_step : block020_data_flat046 = (CoefficientMerge.fastMerge block020_data_flat042 block020_data_flat045) := by decide +kernel
theorem block020_data_flat046_original : block020_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded))) := by
  rw [block020_data_flat046_step, block020_data_flat042_original, block020_data_flat045_original]
def block020_data_flat047 : CoefficientMerge.Poly := [(nat_lit 4234, Int.ofNat (nat_lit 6498546969600)), (nat_lit 4235, Int.ofNat (nat_lit 7275589171200)), (nat_lit 4236, Int.ofNat (nat_lit 8588646595200)), (nat_lit 4237, Int.ofNat (nat_lit 6994941380000)), (nat_lit 4238, Int.ofNat (nat_lit 18707359395200))]
theorem block020_data_flat047_step : block020_data_flat047 = (CoefficientMerge.fastMerge block020_data_flat041 block020_data_flat046) := by decide +kernel
theorem block020_data_flat047_original : block020_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded)))) := by
  rw [block020_data_flat047_step, block020_data_flat041_original, block020_data_flat046_original]
def block020_data_flat048 : CoefficientMerge.Poly := [(nat_lit 4239, Int.ofNat (nat_lit 19393808039200))]
theorem block020_data_flat048_step : block020_data_flat048 = (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) := by decide +kernel
theorem block020_data_flat048_original : block020_data_flat048 = (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) := by
  rw [block020_data_flat048_step]
def block020_data_flat049 : CoefficientMerge.Poly := [(nat_lit 4240, Int.ofNat (nat_lit 29075845864800))]
theorem block020_data_flat049_step : block020_data_flat049 = (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded) := by decide +kernel
theorem block020_data_flat049_original : block020_data_flat049 = (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded) := by
  rw [block020_data_flat049_step]
def block020_data_flat050 : CoefficientMerge.Poly := [(nat_lit 4239, Int.ofNat (nat_lit 19393808039200)), (nat_lit 4240, Int.ofNat (nat_lit 29075845864800))]
theorem block020_data_flat050_step : block020_data_flat050 = (CoefficientMerge.fastMerge block020_data_flat048 block020_data_flat049) := by decide +kernel
theorem block020_data_flat050_original : block020_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded)) := by
  rw [block020_data_flat050_step, block020_data_flat048_original, block020_data_flat049_original]
def block020_data_flat051 : CoefficientMerge.Poly := [(nat_lit 4241, Int.ofNat (nat_lit 40801239259200))]
theorem block020_data_flat051_step : block020_data_flat051 = (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) := by decide +kernel
theorem block020_data_flat051_original : block020_data_flat051 = (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) := by
  rw [block020_data_flat051_step]
def block020_data_flat052 : CoefficientMerge.Poly := [(nat_lit 4255, Int.ofNat (nat_lit 5863944096000))]
theorem block020_data_flat052_step : block020_data_flat052 = (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) := by decide +kernel
theorem block020_data_flat052_original : block020_data_flat052 = (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) := by
  rw [block020_data_flat052_step]
def block020_data_flat053 : CoefficientMerge.Poly := [(nat_lit 4256, Int.ofNat (nat_lit 11257079040000))]
theorem block020_data_flat053_step : block020_data_flat053 = (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded) := by decide +kernel
theorem block020_data_flat053_original : block020_data_flat053 = (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded) := by
  rw [block020_data_flat053_step]
def block020_data_flat054 : CoefficientMerge.Poly := [(nat_lit 4255, Int.ofNat (nat_lit 5863944096000)), (nat_lit 4256, Int.ofNat (nat_lit 11257079040000))]
theorem block020_data_flat054_step : block020_data_flat054 = (CoefficientMerge.fastMerge block020_data_flat052 block020_data_flat053) := by decide +kernel
theorem block020_data_flat054_original : block020_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded)) := by
  rw [block020_data_flat054_step, block020_data_flat052_original, block020_data_flat053_original]
def block020_data_flat055 : CoefficientMerge.Poly := [(nat_lit 4241, Int.ofNat (nat_lit 40801239259200)), (nat_lit 4255, Int.ofNat (nat_lit 5863944096000)), (nat_lit 4256, Int.ofNat (nat_lit 11257079040000))]
theorem block020_data_flat055_step : block020_data_flat055 = (CoefficientMerge.fastMerge block020_data_flat051 block020_data_flat054) := by decide +kernel
theorem block020_data_flat055_original : block020_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded))) := by
  rw [block020_data_flat055_step, block020_data_flat051_original, block020_data_flat054_original]
def block020_data_flat056 : CoefficientMerge.Poly := [(nat_lit 4239, Int.ofNat (nat_lit 19393808039200)), (nat_lit 4240, Int.ofNat (nat_lit 29075845864800)), (nat_lit 4241, Int.ofNat (nat_lit 40801239259200)), (nat_lit 4255, Int.ofNat (nat_lit 5863944096000)), (nat_lit 4256, Int.ofNat (nat_lit 11257079040000))]
theorem block020_data_flat056_step : block020_data_flat056 = (CoefficientMerge.fastMerge block020_data_flat050 block020_data_flat055) := by decide +kernel
theorem block020_data_flat056_original : block020_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded)))) := by
  rw [block020_data_flat056_step, block020_data_flat050_original, block020_data_flat055_original]
def block020_data_flat057 : CoefficientMerge.Poly := [(nat_lit 4234, Int.ofNat (nat_lit 6498546969600)), (nat_lit 4235, Int.ofNat (nat_lit 7275589171200)), (nat_lit 4236, Int.ofNat (nat_lit 8588646595200)), (nat_lit 4237, Int.ofNat (nat_lit 6994941380000)), (nat_lit 4238, Int.ofNat (nat_lit 18707359395200)), (nat_lit 4239, Int.ofNat (nat_lit 19393808039200)), (nat_lit 4240, Int.ofNat (nat_lit 29075845864800)), (nat_lit 4241, Int.ofNat (nat_lit 40801239259200)), (nat_lit 4255, Int.ofNat (nat_lit 5863944096000)), (nat_lit 4256, Int.ofNat (nat_lit 11257079040000))]
theorem block020_data_flat057_step : block020_data_flat057 = (CoefficientMerge.fastMerge block020_data_flat047 block020_data_flat056) := by decide +kernel
theorem block020_data_flat057_original : block020_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded))))) := by
  rw [block020_data_flat057_step, block020_data_flat047_original, block020_data_flat056_original]
def block020_data_flat058 : CoefficientMerge.Poly := [(nat_lit 4257, Int.ofNat (nat_lit 13909039300800))]
theorem block020_data_flat058_step : block020_data_flat058 = (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) := by decide +kernel
theorem block020_data_flat058_original : block020_data_flat058 = (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) := by
  rw [block020_data_flat058_step]
def block020_data_flat059 : CoefficientMerge.Poly := [(nat_lit 4258, Int.ofNat (nat_lit 13518234338400))]
theorem block020_data_flat059_step : block020_data_flat059 = (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded) := by decide +kernel
theorem block020_data_flat059_original : block020_data_flat059 = (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded) := by
  rw [block020_data_flat059_step]
def block020_data_flat060 : CoefficientMerge.Poly := [(nat_lit 4257, Int.ofNat (nat_lit 13909039300800)), (nat_lit 4258, Int.ofNat (nat_lit 13518234338400))]
theorem block020_data_flat060_step : block020_data_flat060 = (CoefficientMerge.fastMerge block020_data_flat058 block020_data_flat059) := by decide +kernel
theorem block020_data_flat060_original : block020_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded)) := by
  rw [block020_data_flat060_step, block020_data_flat058_original, block020_data_flat059_original]
def block020_data_flat061 : CoefficientMerge.Poly := [(nat_lit 4259, Int.ofNat (nat_lit 29696485795200))]
theorem block020_data_flat061_step : block020_data_flat061 = (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) := by decide +kernel
theorem block020_data_flat061_original : block020_data_flat061 = (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) := by
  rw [block020_data_flat061_step]
def block020_data_flat062 : CoefficientMerge.Poly := [(nat_lit 4260, Int.ofNat (nat_lit 32840704461600))]
theorem block020_data_flat062_step : block020_data_flat062 = (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) := by decide +kernel
theorem block020_data_flat062_original : block020_data_flat062 = (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) := by
  rw [block020_data_flat062_step]
def block020_data_flat063 : CoefficientMerge.Poly := [(nat_lit 4261, Int.ofNat (nat_lit 37111606192800))]
theorem block020_data_flat063_step : block020_data_flat063 = (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded) := by decide +kernel
theorem block020_data_flat063_original : block020_data_flat063 = (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded) := by
  rw [block020_data_flat063_step]
def block020_data_flat064 : CoefficientMerge.Poly := [(nat_lit 4260, Int.ofNat (nat_lit 32840704461600)), (nat_lit 4261, Int.ofNat (nat_lit 37111606192800))]
theorem block020_data_flat064_step : block020_data_flat064 = (CoefficientMerge.fastMerge block020_data_flat062 block020_data_flat063) := by decide +kernel
theorem block020_data_flat064_original : block020_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded)) := by
  rw [block020_data_flat064_step, block020_data_flat062_original, block020_data_flat063_original]
def block020_data_flat065 : CoefficientMerge.Poly := [(nat_lit 4259, Int.ofNat (nat_lit 29696485795200)), (nat_lit 4260, Int.ofNat (nat_lit 32840704461600)), (nat_lit 4261, Int.ofNat (nat_lit 37111606192800))]
theorem block020_data_flat065_step : block020_data_flat065 = (CoefficientMerge.fastMerge block020_data_flat061 block020_data_flat064) := by decide +kernel
theorem block020_data_flat065_original : block020_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded))) := by
  rw [block020_data_flat065_step, block020_data_flat061_original, block020_data_flat064_original]
def block020_data_flat066 : CoefficientMerge.Poly := [(nat_lit 4257, Int.ofNat (nat_lit 13909039300800)), (nat_lit 4258, Int.ofNat (nat_lit 13518234338400)), (nat_lit 4259, Int.ofNat (nat_lit 29696485795200)), (nat_lit 4260, Int.ofNat (nat_lit 32840704461600)), (nat_lit 4261, Int.ofNat (nat_lit 37111606192800))]
theorem block020_data_flat066_step : block020_data_flat066 = (CoefficientMerge.fastMerge block020_data_flat060 block020_data_flat065) := by decide +kernel
theorem block020_data_flat066_original : block020_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded)))) := by
  rw [block020_data_flat066_step, block020_data_flat060_original, block020_data_flat065_original]
def block020_data_flat067 : CoefficientMerge.Poly := [(nat_lit 4262, Int.ofNat (nat_lit 55562141678400))]
theorem block020_data_flat067_step : block020_data_flat067 = (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) := by decide +kernel
theorem block020_data_flat067_original : block020_data_flat067 = (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) := by
  rw [block020_data_flat067_step]
def block020_data_flat068 : CoefficientMerge.Poly := [(nat_lit 4277, Int.ofNat (nat_lit 10101226464000))]
theorem block020_data_flat068_step : block020_data_flat068 = (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded) := by decide +kernel
theorem block020_data_flat068_original : block020_data_flat068 = (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded) := by
  rw [block020_data_flat068_step]
def block020_data_flat069 : CoefficientMerge.Poly := [(nat_lit 4262, Int.ofNat (nat_lit 55562141678400)), (nat_lit 4277, Int.ofNat (nat_lit 10101226464000))]
theorem block020_data_flat069_step : block020_data_flat069 = (CoefficientMerge.fastMerge block020_data_flat067 block020_data_flat068) := by decide +kernel
theorem block020_data_flat069_original : block020_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded)) := by
  rw [block020_data_flat069_step, block020_data_flat067_original, block020_data_flat068_original]
def block020_data_flat070 : CoefficientMerge.Poly := [(nat_lit 4278, Int.ofNat (nat_lit 19117589904000))]
theorem block020_data_flat070_step : block020_data_flat070 = (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) := by decide +kernel
theorem block020_data_flat070_original : block020_data_flat070 = (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) := by
  rw [block020_data_flat070_step]
def block020_data_flat071 : CoefficientMerge.Poly := [(nat_lit 4279, Int.ofNat (nat_lit 19922377860000))]
theorem block020_data_flat071_step : block020_data_flat071 = (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) := by decide +kernel
theorem block020_data_flat071_original : block020_data_flat071 = (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) := by
  rw [block020_data_flat071_step]
def block020_data_flat072 : CoefficientMerge.Poly := [(nat_lit 4280, Int.ofNat (nat_lit 42879142051200))]
theorem block020_data_flat072_step : block020_data_flat072 = (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded) := by decide +kernel
theorem block020_data_flat072_original : block020_data_flat072 = (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded) := by
  rw [block020_data_flat072_step]
def block020_data_flat073 : CoefficientMerge.Poly := [(nat_lit 4279, Int.ofNat (nat_lit 19922377860000)), (nat_lit 4280, Int.ofNat (nat_lit 42879142051200))]
theorem block020_data_flat073_step : block020_data_flat073 = (CoefficientMerge.fastMerge block020_data_flat071 block020_data_flat072) := by decide +kernel
theorem block020_data_flat073_original : block020_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded)) := by
  rw [block020_data_flat073_step, block020_data_flat071_original, block020_data_flat072_original]
def block020_data_flat074 : CoefficientMerge.Poly := [(nat_lit 4278, Int.ofNat (nat_lit 19117589904000)), (nat_lit 4279, Int.ofNat (nat_lit 19922377860000)), (nat_lit 4280, Int.ofNat (nat_lit 42879142051200))]
theorem block020_data_flat074_step : block020_data_flat074 = (CoefficientMerge.fastMerge block020_data_flat070 block020_data_flat073) := by decide +kernel
theorem block020_data_flat074_original : block020_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded))) := by
  rw [block020_data_flat074_step, block020_data_flat070_original, block020_data_flat073_original]
def block020_data_flat075 : CoefficientMerge.Poly := [(nat_lit 4262, Int.ofNat (nat_lit 55562141678400)), (nat_lit 4277, Int.ofNat (nat_lit 10101226464000)), (nat_lit 4278, Int.ofNat (nat_lit 19117589904000)), (nat_lit 4279, Int.ofNat (nat_lit 19922377860000)), (nat_lit 4280, Int.ofNat (nat_lit 42879142051200))]
theorem block020_data_flat075_step : block020_data_flat075 = (CoefficientMerge.fastMerge block020_data_flat069 block020_data_flat074) := by decide +kernel
theorem block020_data_flat075_original : block020_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded)))) := by
  rw [block020_data_flat075_step, block020_data_flat069_original, block020_data_flat074_original]
def block020_data_flat076 : CoefficientMerge.Poly := [(nat_lit 4257, Int.ofNat (nat_lit 13909039300800)), (nat_lit 4258, Int.ofNat (nat_lit 13518234338400)), (nat_lit 4259, Int.ofNat (nat_lit 29696485795200)), (nat_lit 4260, Int.ofNat (nat_lit 32840704461600)), (nat_lit 4261, Int.ofNat (nat_lit 37111606192800)), (nat_lit 4262, Int.ofNat (nat_lit 55562141678400)), (nat_lit 4277, Int.ofNat (nat_lit 10101226464000)), (nat_lit 4278, Int.ofNat (nat_lit 19117589904000)), (nat_lit 4279, Int.ofNat (nat_lit 19922377860000)), (nat_lit 4280, Int.ofNat (nat_lit 42879142051200))]
theorem block020_data_flat076_step : block020_data_flat076 = (CoefficientMerge.fastMerge block020_data_flat066 block020_data_flat075) := by decide +kernel
theorem block020_data_flat076_original : block020_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded))))) := by
  rw [block020_data_flat076_step, block020_data_flat066_original, block020_data_flat075_original]
def block020_data_flat077 : CoefficientMerge.Poly := [(nat_lit 4234, Int.ofNat (nat_lit 6498546969600)), (nat_lit 4235, Int.ofNat (nat_lit 7275589171200)), (nat_lit 4236, Int.ofNat (nat_lit 8588646595200)), (nat_lit 4237, Int.ofNat (nat_lit 6994941380000)), (nat_lit 4238, Int.ofNat (nat_lit 18707359395200)), (nat_lit 4239, Int.ofNat (nat_lit 19393808039200)), (nat_lit 4240, Int.ofNat (nat_lit 29075845864800)), (nat_lit 4241, Int.ofNat (nat_lit 40801239259200)), (nat_lit 4255, Int.ofNat (nat_lit 5863944096000)), (nat_lit 4256, Int.ofNat (nat_lit 11257079040000)), (nat_lit 4257, Int.ofNat (nat_lit 13909039300800)), (nat_lit 4258, Int.ofNat (nat_lit 13518234338400)), (nat_lit 4259, Int.ofNat (nat_lit 29696485795200)), (nat_lit 4260, Int.ofNat (nat_lit 32840704461600)), (nat_lit 4261, Int.ofNat (nat_lit 37111606192800)), (nat_lit 4262, Int.ofNat (nat_lit 55562141678400)), (nat_lit 4277, Int.ofNat (nat_lit 10101226464000)), (nat_lit 4278, Int.ofNat (nat_lit 19117589904000)), (nat_lit 4279, Int.ofNat (nat_lit 19922377860000)), (nat_lit 4280, Int.ofNat (nat_lit 42879142051200))]
theorem block020_data_flat077_step : block020_data_flat077 = (CoefficientMerge.fastMerge block020_data_flat057 block020_data_flat076) := by decide +kernel
theorem block020_data_flat077_original : block020_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded)))))) := by
  rw [block020_data_flat077_step, block020_data_flat057_original, block020_data_flat076_original]
def block020_data_flat078 : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 182739160800)), (nat_lit 4189, Int.ofNat (nat_lit 770276908800)), (nat_lit 4192, Int.ofNat (nat_lit 427179916800)), (nat_lit 4193, Int.ofNat (nat_lit 854359833600)), (nat_lit 4194, Int.ofNat (nat_lit 5669444229120)), (nat_lit 4196, Int.ofNat (nat_lit 6132165580800)), (nat_lit 4197, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4198, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4199, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4211, Int.ofNat (nat_lit 1533788524800)), (nat_lit 4212, Int.ofNat (nat_lit 1876885516800)), (nat_lit 4213, Int.ofNat (nat_lit 2563079500800)), (nat_lit 4214, Int.ofNat (nat_lit 3249273484800)), (nat_lit 4215, Int.ofNat (nat_lit 6681901564800)), (nat_lit 4216, Int.ofNat (nat_lit 1017686224800)), (nat_lit 4217, Int.ofNat (nat_lit 12075930115200)), (nat_lit 4218, Int.ofNat (nat_lit 10740378448800)), (nat_lit 4219, Int.ofNat (nat_lit 20105092879200)), (nat_lit 4220, Int.ofNat (nat_lit 31025632780800)), (nat_lit 4233, Int.ofNat (nat_lit 3074342342400)), (nat_lit 4234, Int.ofNat (nat_lit 6498546969600)), (nat_lit 4235, Int.ofNat (nat_lit 7275589171200)), (nat_lit 4236, Int.ofNat (nat_lit 8588646595200)), (nat_lit 4237, Int.ofNat (nat_lit 6994941380000)), (nat_lit 4238, Int.ofNat (nat_lit 18707359395200)), (nat_lit 4239, Int.ofNat (nat_lit 19393808039200)), (nat_lit 4240, Int.ofNat (nat_lit 29075845864800)), (nat_lit 4241, Int.ofNat (nat_lit 40801239259200)), (nat_lit 4255, Int.ofNat (nat_lit 5863944096000)), (nat_lit 4256, Int.ofNat (nat_lit 11257079040000)), (nat_lit 4257, Int.ofNat (nat_lit 13909039300800)), (nat_lit 4258, Int.ofNat (nat_lit 13518234338400)), (nat_lit 4259, Int.ofNat (nat_lit 29696485795200)), (nat_lit 4260, Int.ofNat (nat_lit 32840704461600)), (nat_lit 4261, Int.ofNat (nat_lit 37111606192800)), (nat_lit 4262, Int.ofNat (nat_lit 55562141678400)), (nat_lit 4277, Int.ofNat (nat_lit 10101226464000)), (nat_lit 4278, Int.ofNat (nat_lit 19117589904000)), (nat_lit 4279, Int.ofNat (nat_lit 19922377860000)), (nat_lit 4280, Int.ofNat (nat_lit 42879142051200))]
theorem block020_data_flat078_step : block020_data_flat078 = (CoefficientMerge.fastMerge block020_data_flat038 block020_data_flat077) := by decide +kernel
theorem block020_data_flat078_original : block020_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded))))))) := by
  rw [block020_data_flat078_step, block020_data_flat038_original, block020_data_flat077_original]
def block020_data_flat079 : CoefficientMerge.Poly := [(nat_lit 4281, Int.ofNat (nat_lit 48700483725600))]
theorem block020_data_flat079_step : block020_data_flat079 = (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) := by decide +kernel
theorem block020_data_flat079_original : block020_data_flat079 = (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) := by
  rw [block020_data_flat079_step]
def block020_data_flat080 : CoefficientMerge.Poly := [(nat_lit 4282, Int.ofNat (nat_lit 49598093109600))]
theorem block020_data_flat080_step : block020_data_flat080 = (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded) := by decide +kernel
theorem block020_data_flat080_original : block020_data_flat080 = (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded) := by
  rw [block020_data_flat080_step]
def block020_data_flat081 : CoefficientMerge.Poly := [(nat_lit 4281, Int.ofNat (nat_lit 48700483725600)), (nat_lit 4282, Int.ofNat (nat_lit 49598093109600))]
theorem block020_data_flat081_step : block020_data_flat081 = (CoefficientMerge.fastMerge block020_data_flat079 block020_data_flat080) := by decide +kernel
theorem block020_data_flat081_original : block020_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded)) := by
  rw [block020_data_flat081_step, block020_data_flat079_original, block020_data_flat080_original]
def block020_data_flat082 : CoefficientMerge.Poly := [(nat_lit 4283, Int.ofNat (nat_lit 74906046734400))]
theorem block020_data_flat082_step : block020_data_flat082 = (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) := by decide +kernel
theorem block020_data_flat082_original : block020_data_flat082 = (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) := by
  rw [block020_data_flat082_step]
def block020_data_flat083 : CoefficientMerge.Poly := [(nat_lit 4299, Int.ofNat (nat_lit 16795322611200))]
theorem block020_data_flat083_step : block020_data_flat083 = (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) := by decide +kernel
theorem block020_data_flat083_original : block020_data_flat083 = (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) := by
  rw [block020_data_flat083_step]
def block020_data_flat084 : CoefficientMerge.Poly := [(nat_lit 4300, Int.ofNat (nat_lit 35735021557200))]
theorem block020_data_flat084_step : block020_data_flat084 = (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded) := by decide +kernel
theorem block020_data_flat084_original : block020_data_flat084 = (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded) := by
  rw [block020_data_flat084_step]
def block020_data_flat085 : CoefficientMerge.Poly := [(nat_lit 4299, Int.ofNat (nat_lit 16795322611200)), (nat_lit 4300, Int.ofNat (nat_lit 35735021557200))]
theorem block020_data_flat085_step : block020_data_flat085 = (CoefficientMerge.fastMerge block020_data_flat083 block020_data_flat084) := by decide +kernel
theorem block020_data_flat085_original : block020_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded)) := by
  rw [block020_data_flat085_step, block020_data_flat083_original, block020_data_flat084_original]
def block020_data_flat086 : CoefficientMerge.Poly := [(nat_lit 4283, Int.ofNat (nat_lit 74906046734400)), (nat_lit 4299, Int.ofNat (nat_lit 16795322611200)), (nat_lit 4300, Int.ofNat (nat_lit 35735021557200))]
theorem block020_data_flat086_step : block020_data_flat086 = (CoefficientMerge.fastMerge block020_data_flat082 block020_data_flat085) := by decide +kernel
theorem block020_data_flat086_original : block020_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded))) := by
  rw [block020_data_flat086_step, block020_data_flat082_original, block020_data_flat085_original]
def block020_data_flat087 : CoefficientMerge.Poly := [(nat_lit 4281, Int.ofNat (nat_lit 48700483725600)), (nat_lit 4282, Int.ofNat (nat_lit 49598093109600)), (nat_lit 4283, Int.ofNat (nat_lit 74906046734400)), (nat_lit 4299, Int.ofNat (nat_lit 16795322611200)), (nat_lit 4300, Int.ofNat (nat_lit 35735021557200))]
theorem block020_data_flat087_step : block020_data_flat087 = (CoefficientMerge.fastMerge block020_data_flat081 block020_data_flat086) := by decide +kernel
theorem block020_data_flat087_original : block020_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded)))) := by
  rw [block020_data_flat087_step, block020_data_flat081_original, block020_data_flat086_original]
def block020_data_flat088 : CoefficientMerge.Poly := [(nat_lit 4301, Int.ofNat (nat_lit 64884545510400))]
theorem block020_data_flat088_step : block020_data_flat088 = (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) := by decide +kernel
theorem block020_data_flat088_original : block020_data_flat088 = (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) := by
  rw [block020_data_flat088_step]
def block020_data_flat089 : CoefficientMerge.Poly := [(nat_lit 4302, Int.ofNat (nat_lit 69986611724400))]
theorem block020_data_flat089_step : block020_data_flat089 = (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded) := by decide +kernel
theorem block020_data_flat089_original : block020_data_flat089 = (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded) := by
  rw [block020_data_flat089_step]
def block020_data_flat090 : CoefficientMerge.Poly := [(nat_lit 4301, Int.ofNat (nat_lit 64884545510400)), (nat_lit 4302, Int.ofNat (nat_lit 69986611724400))]
theorem block020_data_flat090_step : block020_data_flat090 = (CoefficientMerge.fastMerge block020_data_flat088 block020_data_flat089) := by decide +kernel
theorem block020_data_flat090_original : block020_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded)) := by
  rw [block020_data_flat090_step, block020_data_flat088_original, block020_data_flat089_original]
def block020_data_flat091 : CoefficientMerge.Poly := [(nat_lit 4303, Int.ofNat (nat_lit 53647060446000))]
theorem block020_data_flat091_step : block020_data_flat091 = (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) := by decide +kernel
theorem block020_data_flat091_original : block020_data_flat091 = (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) := by
  rw [block020_data_flat091_step]
def block020_data_flat092 : CoefficientMerge.Poly := [(nat_lit 4304, Int.ofNat (nat_lit 84256708258800))]
theorem block020_data_flat092_step : block020_data_flat092 = (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) := by decide +kernel
theorem block020_data_flat092_original : block020_data_flat092 = (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) := by
  rw [block020_data_flat092_step]
def block020_data_flat093 : CoefficientMerge.Poly := [(nat_lit 4321, Int.ofNat (nat_lit 14605687272960))]
theorem block020_data_flat093_step : block020_data_flat093 = (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded) := by decide +kernel
theorem block020_data_flat093_original : block020_data_flat093 = (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded) := by
  rw [block020_data_flat093_step]
def block020_data_flat094 : CoefficientMerge.Poly := [(nat_lit 4304, Int.ofNat (nat_lit 84256708258800)), (nat_lit 4321, Int.ofNat (nat_lit 14605687272960))]
theorem block020_data_flat094_step : block020_data_flat094 = (CoefficientMerge.fastMerge block020_data_flat092 block020_data_flat093) := by decide +kernel
theorem block020_data_flat094_original : block020_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded)) := by
  rw [block020_data_flat094_step, block020_data_flat092_original, block020_data_flat093_original]
def block020_data_flat095 : CoefficientMerge.Poly := [(nat_lit 4303, Int.ofNat (nat_lit 53647060446000)), (nat_lit 4304, Int.ofNat (nat_lit 84256708258800)), (nat_lit 4321, Int.ofNat (nat_lit 14605687272960))]
theorem block020_data_flat095_step : block020_data_flat095 = (CoefficientMerge.fastMerge block020_data_flat091 block020_data_flat094) := by decide +kernel
theorem block020_data_flat095_original : block020_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded))) := by
  rw [block020_data_flat095_step, block020_data_flat091_original, block020_data_flat094_original]
def block020_data_flat096 : CoefficientMerge.Poly := [(nat_lit 4301, Int.ofNat (nat_lit 64884545510400)), (nat_lit 4302, Int.ofNat (nat_lit 69986611724400)), (nat_lit 4303, Int.ofNat (nat_lit 53647060446000)), (nat_lit 4304, Int.ofNat (nat_lit 84256708258800)), (nat_lit 4321, Int.ofNat (nat_lit 14605687272960))]
theorem block020_data_flat096_step : block020_data_flat096 = (CoefficientMerge.fastMerge block020_data_flat090 block020_data_flat095) := by decide +kernel
theorem block020_data_flat096_original : block020_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded)))) := by
  rw [block020_data_flat096_step, block020_data_flat090_original, block020_data_flat095_original]
def block020_data_flat097 : CoefficientMerge.Poly := [(nat_lit 4281, Int.ofNat (nat_lit 48700483725600)), (nat_lit 4282, Int.ofNat (nat_lit 49598093109600)), (nat_lit 4283, Int.ofNat (nat_lit 74906046734400)), (nat_lit 4299, Int.ofNat (nat_lit 16795322611200)), (nat_lit 4300, Int.ofNat (nat_lit 35735021557200)), (nat_lit 4301, Int.ofNat (nat_lit 64884545510400)), (nat_lit 4302, Int.ofNat (nat_lit 69986611724400)), (nat_lit 4303, Int.ofNat (nat_lit 53647060446000)), (nat_lit 4304, Int.ofNat (nat_lit 84256708258800)), (nat_lit 4321, Int.ofNat (nat_lit 14605687272960))]
theorem block020_data_flat097_step : block020_data_flat097 = (CoefficientMerge.fastMerge block020_data_flat087 block020_data_flat096) := by decide +kernel
theorem block020_data_flat097_original : block020_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded))))) := by
  rw [block020_data_flat097_step, block020_data_flat087_original, block020_data_flat096_original]
def block020_data_flat098 : CoefficientMerge.Poly := [(nat_lit 4322, Int.ofNat (nat_lit 55660876311600))]
theorem block020_data_flat098_step : block020_data_flat098 = (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) := by decide +kernel
theorem block020_data_flat098_original : block020_data_flat098 = (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) := by
  rw [block020_data_flat098_step]
def block020_data_flat099 : CoefficientMerge.Poly := [(nat_lit 4323, Int.ofNat (nat_lit 65795220880200))]
theorem block020_data_flat099_step : block020_data_flat099 = (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded) := by decide +kernel
theorem block020_data_flat099_original : block020_data_flat099 = (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded) := by
  rw [block020_data_flat099_step]
def block020_data_flat100 : CoefficientMerge.Poly := [(nat_lit 4322, Int.ofNat (nat_lit 55660876311600)), (nat_lit 4323, Int.ofNat (nat_lit 65795220880200))]
theorem block020_data_flat100_step : block020_data_flat100 = (CoefficientMerge.fastMerge block020_data_flat098 block020_data_flat099) := by decide +kernel
theorem block020_data_flat100_original : block020_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded)) := by
  rw [block020_data_flat100_step, block020_data_flat098_original, block020_data_flat099_original]
def block020_data_flat101 : CoefficientMerge.Poly := [(nat_lit 4324, Int.ofNat (nat_lit 48673825250400))]
theorem block020_data_flat101_step : block020_data_flat101 = (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) := by decide +kernel
theorem block020_data_flat101_original : block020_data_flat101 = (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) := by
  rw [block020_data_flat101_step]
def block020_data_flat102 : CoefficientMerge.Poly := [(nat_lit 4325, Int.ofNat (nat_lit 66408854078700))]
theorem block020_data_flat102_step : block020_data_flat102 = (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) := by decide +kernel
theorem block020_data_flat102_original : block020_data_flat102 = (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) := by
  rw [block020_data_flat102_step]
def block020_data_flat103 : CoefficientMerge.Poly := [(nat_lit 4343, Int.ofNat (nat_lit 41744447539200))]
theorem block020_data_flat103_step : block020_data_flat103 = (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded) := by decide +kernel
theorem block020_data_flat103_original : block020_data_flat103 = (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded) := by
  rw [block020_data_flat103_step]
def block020_data_flat104 : CoefficientMerge.Poly := [(nat_lit 4325, Int.ofNat (nat_lit 66408854078700)), (nat_lit 4343, Int.ofNat (nat_lit 41744447539200))]
theorem block020_data_flat104_step : block020_data_flat104 = (CoefficientMerge.fastMerge block020_data_flat102 block020_data_flat103) := by decide +kernel
theorem block020_data_flat104_original : block020_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded)) := by
  rw [block020_data_flat104_step, block020_data_flat102_original, block020_data_flat103_original]
def block020_data_flat105 : CoefficientMerge.Poly := [(nat_lit 4324, Int.ofNat (nat_lit 48673825250400)), (nat_lit 4325, Int.ofNat (nat_lit 66408854078700)), (nat_lit 4343, Int.ofNat (nat_lit 41744447539200))]
theorem block020_data_flat105_step : block020_data_flat105 = (CoefficientMerge.fastMerge block020_data_flat101 block020_data_flat104) := by decide +kernel
theorem block020_data_flat105_original : block020_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded))) := by
  rw [block020_data_flat105_step, block020_data_flat101_original, block020_data_flat104_original]
def block020_data_flat106 : CoefficientMerge.Poly := [(nat_lit 4322, Int.ofNat (nat_lit 55660876311600)), (nat_lit 4323, Int.ofNat (nat_lit 65795220880200)), (nat_lit 4324, Int.ofNat (nat_lit 48673825250400)), (nat_lit 4325, Int.ofNat (nat_lit 66408854078700)), (nat_lit 4343, Int.ofNat (nat_lit 41744447539200))]
theorem block020_data_flat106_step : block020_data_flat106 = (CoefficientMerge.fastMerge block020_data_flat100 block020_data_flat105) := by decide +kernel
theorem block020_data_flat106_original : block020_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded)))) := by
  rw [block020_data_flat106_step, block020_data_flat100_original, block020_data_flat105_original]
def block020_data_flat107 : CoefficientMerge.Poly := [(nat_lit 4344, Int.ofNat (nat_lit 76111510784400))]
theorem block020_data_flat107_step : block020_data_flat107 = (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) := by decide +kernel
theorem block020_data_flat107_original : block020_data_flat107 = (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) := by
  rw [block020_data_flat107_step]
def block020_data_flat108 : CoefficientMerge.Poly := [(nat_lit 4345, Int.ofNat (nat_lit 52712801442000))]
theorem block020_data_flat108_step : block020_data_flat108 = (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded) := by decide +kernel
theorem block020_data_flat108_original : block020_data_flat108 = (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded) := by
  rw [block020_data_flat108_step]
def block020_data_flat109 : CoefficientMerge.Poly := [(nat_lit 4344, Int.ofNat (nat_lit 76111510784400)), (nat_lit 4345, Int.ofNat (nat_lit 52712801442000))]
theorem block020_data_flat109_step : block020_data_flat109 = (CoefficientMerge.fastMerge block020_data_flat107 block020_data_flat108) := by decide +kernel
theorem block020_data_flat109_original : block020_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded)) := by
  rw [block020_data_flat109_step, block020_data_flat107_original, block020_data_flat108_original]
def block020_data_flat110 : CoefficientMerge.Poly := [(nat_lit 4346, Int.ofNat (nat_lit 58566148880400))]
theorem block020_data_flat110_step : block020_data_flat110 = (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) := by decide +kernel
theorem block020_data_flat110_original : block020_data_flat110 = (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) := by
  rw [block020_data_flat110_step]
def block020_data_flat111 : CoefficientMerge.Poly := [(nat_lit 4365, Int.ofNat (nat_lit 28394930554200))]
theorem block020_data_flat111_step : block020_data_flat111 = (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) := by decide +kernel
theorem block020_data_flat111_original : block020_data_flat111 = (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) := by
  rw [block020_data_flat111_step]
def block020_data_flat112 : CoefficientMerge.Poly := [(nat_lit 4366, Int.ofNat (nat_lit 36513604071000))]
theorem block020_data_flat112_step : block020_data_flat112 = (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded) := by decide +kernel
theorem block020_data_flat112_original : block020_data_flat112 = (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded) := by
  rw [block020_data_flat112_step]
def block020_data_flat113 : CoefficientMerge.Poly := [(nat_lit 4365, Int.ofNat (nat_lit 28394930554200)), (nat_lit 4366, Int.ofNat (nat_lit 36513604071000))]
theorem block020_data_flat113_step : block020_data_flat113 = (CoefficientMerge.fastMerge block020_data_flat111 block020_data_flat112) := by decide +kernel
theorem block020_data_flat113_original : block020_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded)) := by
  rw [block020_data_flat113_step, block020_data_flat111_original, block020_data_flat112_original]
def block020_data_flat114 : CoefficientMerge.Poly := [(nat_lit 4346, Int.ofNat (nat_lit 58566148880400)), (nat_lit 4365, Int.ofNat (nat_lit 28394930554200)), (nat_lit 4366, Int.ofNat (nat_lit 36513604071000))]
theorem block020_data_flat114_step : block020_data_flat114 = (CoefficientMerge.fastMerge block020_data_flat110 block020_data_flat113) := by decide +kernel
theorem block020_data_flat114_original : block020_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded))) := by
  rw [block020_data_flat114_step, block020_data_flat110_original, block020_data_flat113_original]
def block020_data_flat115 : CoefficientMerge.Poly := [(nat_lit 4344, Int.ofNat (nat_lit 76111510784400)), (nat_lit 4345, Int.ofNat (nat_lit 52712801442000)), (nat_lit 4346, Int.ofNat (nat_lit 58566148880400)), (nat_lit 4365, Int.ofNat (nat_lit 28394930554200)), (nat_lit 4366, Int.ofNat (nat_lit 36513604071000))]
theorem block020_data_flat115_step : block020_data_flat115 = (CoefficientMerge.fastMerge block020_data_flat109 block020_data_flat114) := by decide +kernel
theorem block020_data_flat115_original : block020_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded)))) := by
  rw [block020_data_flat115_step, block020_data_flat109_original, block020_data_flat114_original]
def block020_data_flat116 : CoefficientMerge.Poly := [(nat_lit 4322, Int.ofNat (nat_lit 55660876311600)), (nat_lit 4323, Int.ofNat (nat_lit 65795220880200)), (nat_lit 4324, Int.ofNat (nat_lit 48673825250400)), (nat_lit 4325, Int.ofNat (nat_lit 66408854078700)), (nat_lit 4343, Int.ofNat (nat_lit 41744447539200)), (nat_lit 4344, Int.ofNat (nat_lit 76111510784400)), (nat_lit 4345, Int.ofNat (nat_lit 52712801442000)), (nat_lit 4346, Int.ofNat (nat_lit 58566148880400)), (nat_lit 4365, Int.ofNat (nat_lit 28394930554200)), (nat_lit 4366, Int.ofNat (nat_lit 36513604071000))]
theorem block020_data_flat116_step : block020_data_flat116 = (CoefficientMerge.fastMerge block020_data_flat106 block020_data_flat115) := by decide +kernel
theorem block020_data_flat116_original : block020_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded))))) := by
  rw [block020_data_flat116_step, block020_data_flat106_original, block020_data_flat115_original]
def block020_data_flat117 : CoefficientMerge.Poly := [(nat_lit 4281, Int.ofNat (nat_lit 48700483725600)), (nat_lit 4282, Int.ofNat (nat_lit 49598093109600)), (nat_lit 4283, Int.ofNat (nat_lit 74906046734400)), (nat_lit 4299, Int.ofNat (nat_lit 16795322611200)), (nat_lit 4300, Int.ofNat (nat_lit 35735021557200)), (nat_lit 4301, Int.ofNat (nat_lit 64884545510400)), (nat_lit 4302, Int.ofNat (nat_lit 69986611724400)), (nat_lit 4303, Int.ofNat (nat_lit 53647060446000)), (nat_lit 4304, Int.ofNat (nat_lit 84256708258800)), (nat_lit 4321, Int.ofNat (nat_lit 14605687272960)), (nat_lit 4322, Int.ofNat (nat_lit 55660876311600)), (nat_lit 4323, Int.ofNat (nat_lit 65795220880200)), (nat_lit 4324, Int.ofNat (nat_lit 48673825250400)), (nat_lit 4325, Int.ofNat (nat_lit 66408854078700)), (nat_lit 4343, Int.ofNat (nat_lit 41744447539200)), (nat_lit 4344, Int.ofNat (nat_lit 76111510784400)), (nat_lit 4345, Int.ofNat (nat_lit 52712801442000)), (nat_lit 4346, Int.ofNat (nat_lit 58566148880400)), (nat_lit 4365, Int.ofNat (nat_lit 28394930554200)), (nat_lit 4366, Int.ofNat (nat_lit 36513604071000))]
theorem block020_data_flat117_step : block020_data_flat117 = (CoefficientMerge.fastMerge block020_data_flat097 block020_data_flat116) := by decide +kernel
theorem block020_data_flat117_original : block020_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded)))))) := by
  rw [block020_data_flat117_step, block020_data_flat097_original, block020_data_flat116_original]
def block020_data_flat118 : CoefficientMerge.Poly := [(nat_lit 4367, Int.ofNat (nat_lit 44758527817500))]
theorem block020_data_flat118_step : block020_data_flat118 = (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) := by decide +kernel
theorem block020_data_flat118_original : block020_data_flat118 = (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) := by
  rw [block020_data_flat118_step]
def block020_data_flat119 : CoefficientMerge.Poly := [(nat_lit 4387, Int.ofNat (nat_lit 3308751684000))]
theorem block020_data_flat119_step : block020_data_flat119 = (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded) := by decide +kernel
theorem block020_data_flat119_original : block020_data_flat119 = (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded) := by
  rw [block020_data_flat119_step]
def block020_data_flat120 : CoefficientMerge.Poly := [(nat_lit 4367, Int.ofNat (nat_lit 44758527817500)), (nat_lit 4387, Int.ofNat (nat_lit 3308751684000))]
theorem block020_data_flat120_step : block020_data_flat120 = (CoefficientMerge.fastMerge block020_data_flat118 block020_data_flat119) := by decide +kernel
theorem block020_data_flat120_original : block020_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded)) := by
  rw [block020_data_flat120_step, block020_data_flat118_original, block020_data_flat119_original]
def block020_data_flat121 : CoefficientMerge.Poly := [(nat_lit 4388, Int.ofNat (nat_lit 15671181626100))]
theorem block020_data_flat121_step : block020_data_flat121 = (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) := by decide +kernel
theorem block020_data_flat121_original : block020_data_flat121 = (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) := by
  rw [block020_data_flat121_step]
def block020_data_flat122 : CoefficientMerge.Poly := [(nat_lit 4409, Int.ofNat (nat_lit 8870673060900))]
theorem block020_data_flat122_step : block020_data_flat122 = (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) := by decide +kernel
theorem block020_data_flat122_original : block020_data_flat122 = (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) := by
  rw [block020_data_flat122_step]
def block020_data_flat123 : CoefficientMerge.Poly := [(nat_lit 4630, Int.ofNat (nat_lit 597600864000))]
theorem block020_data_flat123_step : block020_data_flat123 = (CoefficientMerge.scale (597600864000 : Int) atom1520Coded) := by decide +kernel
theorem block020_data_flat123_original : block020_data_flat123 = (CoefficientMerge.scale (597600864000 : Int) atom1520Coded) := by
  rw [block020_data_flat123_step]
def block020_data_flat124 : CoefficientMerge.Poly := [(nat_lit 4409, Int.ofNat (nat_lit 8870673060900)), (nat_lit 4630, Int.ofNat (nat_lit 597600864000))]
theorem block020_data_flat124_step : block020_data_flat124 = (CoefficientMerge.fastMerge block020_data_flat122 block020_data_flat123) := by decide +kernel
theorem block020_data_flat124_original : block020_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded)) := by
  rw [block020_data_flat124_step, block020_data_flat122_original, block020_data_flat123_original]
def block020_data_flat125 : CoefficientMerge.Poly := [(nat_lit 4388, Int.ofNat (nat_lit 15671181626100)), (nat_lit 4409, Int.ofNat (nat_lit 8870673060900)), (nat_lit 4630, Int.ofNat (nat_lit 597600864000))]
theorem block020_data_flat125_step : block020_data_flat125 = (CoefficientMerge.fastMerge block020_data_flat121 block020_data_flat124) := by decide +kernel
theorem block020_data_flat125_original : block020_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded))) := by
  rw [block020_data_flat125_step, block020_data_flat121_original, block020_data_flat124_original]
def block020_data_flat126 : CoefficientMerge.Poly := [(nat_lit 4367, Int.ofNat (nat_lit 44758527817500)), (nat_lit 4387, Int.ofNat (nat_lit 3308751684000)), (nat_lit 4388, Int.ofNat (nat_lit 15671181626100)), (nat_lit 4409, Int.ofNat (nat_lit 8870673060900)), (nat_lit 4630, Int.ofNat (nat_lit 597600864000))]
theorem block020_data_flat126_step : block020_data_flat126 = (CoefficientMerge.fastMerge block020_data_flat120 block020_data_flat125) := by decide +kernel
theorem block020_data_flat126_original : block020_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded)))) := by
  rw [block020_data_flat126_step, block020_data_flat120_original, block020_data_flat125_original]
def block020_data_flat127 : CoefficientMerge.Poly := [(nat_lit 4631, Int.ofNat (nat_lit 427179916800))]
theorem block020_data_flat127_step : block020_data_flat127 = (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) := by decide +kernel
theorem block020_data_flat127_original : block020_data_flat127 = (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) := by
  rw [block020_data_flat127_step]
def block020_data_flat128 : CoefficientMerge.Poly := [(nat_lit 4635, Int.ofNat (nat_lit 3075590700000))]
theorem block020_data_flat128_step : block020_data_flat128 = (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded) := by decide +kernel
theorem block020_data_flat128_original : block020_data_flat128 = (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded) := by
  rw [block020_data_flat128_step]
def block020_data_flat129 : CoefficientMerge.Poly := [(nat_lit 4631, Int.ofNat (nat_lit 427179916800)), (nat_lit 4635, Int.ofNat (nat_lit 3075590700000))]
theorem block020_data_flat129_step : block020_data_flat129 = (CoefficientMerge.fastMerge block020_data_flat127 block020_data_flat128) := by decide +kernel
theorem block020_data_flat129_original : block020_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded)) := by
  rw [block020_data_flat129_step, block020_data_flat127_original, block020_data_flat128_original]
def block020_data_flat130 : CoefficientMerge.Poly := [(nat_lit 4637, Int.ofNat (nat_lit 2234314202400))]
theorem block020_data_flat130_step : block020_data_flat130 = (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) := by decide +kernel
theorem block020_data_flat130_original : block020_data_flat130 = (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) := by
  rw [block020_data_flat130_step]
def block020_data_flat131 : CoefficientMerge.Poly := [(nat_lit 4652, Int.ofNat (nat_lit 938442758400))]
theorem block020_data_flat131_step : block020_data_flat131 = (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) := by decide +kernel
theorem block020_data_flat131_original : block020_data_flat131 = (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) := by
  rw [block020_data_flat131_step]
def block020_data_flat132 : CoefficientMerge.Poly := [(nat_lit 4654, Int.ofNat (nat_lit 427179916800))]
theorem block020_data_flat132_step : block020_data_flat132 = (CoefficientMerge.scale (427179916800 : Int) atom1525Coded) := by decide +kernel
theorem block020_data_flat132_original : block020_data_flat132 = (CoefficientMerge.scale (427179916800 : Int) atom1525Coded) := by
  rw [block020_data_flat132_step]
def block020_data_flat133 : CoefficientMerge.Poly := [(nat_lit 4652, Int.ofNat (nat_lit 938442758400)), (nat_lit 4654, Int.ofNat (nat_lit 427179916800))]
theorem block020_data_flat133_step : block020_data_flat133 = (CoefficientMerge.fastMerge block020_data_flat131 block020_data_flat132) := by decide +kernel
theorem block020_data_flat133_original : block020_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded)) := by
  rw [block020_data_flat133_step, block020_data_flat131_original, block020_data_flat132_original]
def block020_data_flat134 : CoefficientMerge.Poly := [(nat_lit 4637, Int.ofNat (nat_lit 2234314202400)), (nat_lit 4652, Int.ofNat (nat_lit 938442758400)), (nat_lit 4654, Int.ofNat (nat_lit 427179916800))]
theorem block020_data_flat134_step : block020_data_flat134 = (CoefficientMerge.fastMerge block020_data_flat130 block020_data_flat133) := by decide +kernel
theorem block020_data_flat134_original : block020_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded))) := by
  rw [block020_data_flat134_step, block020_data_flat130_original, block020_data_flat133_original]
def block020_data_flat135 : CoefficientMerge.Poly := [(nat_lit 4631, Int.ofNat (nat_lit 427179916800)), (nat_lit 4635, Int.ofNat (nat_lit 3075590700000)), (nat_lit 4637, Int.ofNat (nat_lit 2234314202400)), (nat_lit 4652, Int.ofNat (nat_lit 938442758400)), (nat_lit 4654, Int.ofNat (nat_lit 427179916800))]
theorem block020_data_flat135_step : block020_data_flat135 = (CoefficientMerge.fastMerge block020_data_flat129 block020_data_flat134) := by decide +kernel
theorem block020_data_flat135_original : block020_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded)))) := by
  rw [block020_data_flat135_step, block020_data_flat129_original, block020_data_flat134_original]
def block020_data_flat136 : CoefficientMerge.Poly := [(nat_lit 4367, Int.ofNat (nat_lit 44758527817500)), (nat_lit 4387, Int.ofNat (nat_lit 3308751684000)), (nat_lit 4388, Int.ofNat (nat_lit 15671181626100)), (nat_lit 4409, Int.ofNat (nat_lit 8870673060900)), (nat_lit 4630, Int.ofNat (nat_lit 597600864000)), (nat_lit 4631, Int.ofNat (nat_lit 427179916800)), (nat_lit 4635, Int.ofNat (nat_lit 3075590700000)), (nat_lit 4637, Int.ofNat (nat_lit 2234314202400)), (nat_lit 4652, Int.ofNat (nat_lit 938442758400)), (nat_lit 4654, Int.ofNat (nat_lit 427179916800))]
theorem block020_data_flat136_step : block020_data_flat136 = (CoefficientMerge.fastMerge block020_data_flat126 block020_data_flat135) := by decide +kernel
theorem block020_data_flat136_original : block020_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded))))) := by
  rw [block020_data_flat136_step, block020_data_flat126_original, block020_data_flat135_original]
def block020_data_flat137 : CoefficientMerge.Poly := [(nat_lit 4655, Int.ofNat (nat_lit 854359833600))]
theorem block020_data_flat137_step : block020_data_flat137 = (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) := by decide +kernel
theorem block020_data_flat137_original : block020_data_flat137 = (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) := by
  rw [block020_data_flat137_step]
def block020_data_flat138 : CoefficientMerge.Poly := [(nat_lit 4656, Int.ofNat (nat_lit 5701373284320))]
theorem block020_data_flat138_step : block020_data_flat138 = (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded) := by decide +kernel
theorem block020_data_flat138_original : block020_data_flat138 = (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded) := by
  rw [block020_data_flat138_step]
def block020_data_flat139 : CoefficientMerge.Poly := [(nat_lit 4655, Int.ofNat (nat_lit 854359833600)), (nat_lit 4656, Int.ofNat (nat_lit 5701373284320))]
theorem block020_data_flat139_step : block020_data_flat139 = (CoefficientMerge.fastMerge block020_data_flat137 block020_data_flat138) := by decide +kernel
theorem block020_data_flat139_original : block020_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded)) := by
  rw [block020_data_flat139_step, block020_data_flat137_original, block020_data_flat138_original]
def block020_data_flat140 : CoefficientMerge.Poly := [(nat_lit 4658, Int.ofNat (nat_lit 10571867661600))]
theorem block020_data_flat140_step : block020_data_flat140 = (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) := by decide +kernel
theorem block020_data_flat140_original : block020_data_flat140 = (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) := by
  rw [block020_data_flat140_step]
def block020_data_flat141 : CoefficientMerge.Poly := [(nat_lit 4659, Int.ofNat (nat_lit 5786258284800))]
theorem block020_data_flat141_step : block020_data_flat141 = (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) := by decide +kernel
theorem block020_data_flat141_original : block020_data_flat141 = (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) := by
  rw [block020_data_flat141_step]
def block020_data_flat142 : CoefficientMerge.Poly := [(nat_lit 4660, Int.ofNat (nat_lit 11171238059520))]
theorem block020_data_flat142_step : block020_data_flat142 = (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded) := by decide +kernel
theorem block020_data_flat142_original : block020_data_flat142 = (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded) := by
  rw [block020_data_flat142_step]
def block020_data_flat143 : CoefficientMerge.Poly := [(nat_lit 4659, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4660, Int.ofNat (nat_lit 11171238059520))]
theorem block020_data_flat143_step : block020_data_flat143 = (CoefficientMerge.fastMerge block020_data_flat141 block020_data_flat142) := by decide +kernel
theorem block020_data_flat143_original : block020_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded)) := by
  rw [block020_data_flat143_step, block020_data_flat141_original, block020_data_flat142_original]
def block020_data_flat144 : CoefficientMerge.Poly := [(nat_lit 4658, Int.ofNat (nat_lit 10571867661600)), (nat_lit 4659, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4660, Int.ofNat (nat_lit 11171238059520))]
theorem block020_data_flat144_step : block020_data_flat144 = (CoefficientMerge.fastMerge block020_data_flat140 block020_data_flat143) := by decide +kernel
theorem block020_data_flat144_original : block020_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded))) := by
  rw [block020_data_flat144_step, block020_data_flat140_original, block020_data_flat143_original]
def block020_data_flat145 : CoefficientMerge.Poly := [(nat_lit 4655, Int.ofNat (nat_lit 854359833600)), (nat_lit 4656, Int.ofNat (nat_lit 5701373284320)), (nat_lit 4658, Int.ofNat (nat_lit 10571867661600)), (nat_lit 4659, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4660, Int.ofNat (nat_lit 11171238059520))]
theorem block020_data_flat145_step : block020_data_flat145 = (CoefficientMerge.fastMerge block020_data_flat139 block020_data_flat144) := by decide +kernel
theorem block020_data_flat145_original : block020_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded)))) := by
  rw [block020_data_flat145_step, block020_data_flat139_original, block020_data_flat144_original]
def block020_data_flat146 : CoefficientMerge.Poly := [(nat_lit 4661, Int.ofNat (nat_lit 17391151612800))]
theorem block020_data_flat146_step : block020_data_flat146 = (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) := by decide +kernel
theorem block020_data_flat146_original : block020_data_flat146 = (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) := by
  rw [block020_data_flat146_step]
def block020_data_flat147 : CoefficientMerge.Poly := [(nat_lit 4674, Int.ofNat (nat_lit 1365622675200))]
theorem block020_data_flat147_step : block020_data_flat147 = (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded) := by decide +kernel
theorem block020_data_flat147_original : block020_data_flat147 = (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded) := by
  rw [block020_data_flat147_step]
def block020_data_flat148 : CoefficientMerge.Poly := [(nat_lit 4661, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4674, Int.ofNat (nat_lit 1365622675200))]
theorem block020_data_flat148_step : block020_data_flat148 = (CoefficientMerge.fastMerge block020_data_flat146 block020_data_flat147) := by decide +kernel
theorem block020_data_flat148_original : block020_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded)) := by
  rw [block020_data_flat148_step, block020_data_flat146_original, block020_data_flat147_original]
def block020_data_flat149 : CoefficientMerge.Poly := [(nat_lit 4675, Int.ofNat (nat_lit 2990259417600))]
theorem block020_data_flat149_step : block020_data_flat149 = (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) := by decide +kernel
theorem block020_data_flat149_original : block020_data_flat149 = (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) := by
  rw [block020_data_flat149_step]
def block020_data_flat150 : CoefficientMerge.Poly := [(nat_lit 4676, Int.ofNat (nat_lit 3676453401600))]
theorem block020_data_flat150_step : block020_data_flat150 = (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) := by decide +kernel
theorem block020_data_flat150_original : block020_data_flat150 = (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) := by
  rw [block020_data_flat150_step]
def block020_data_flat151 : CoefficientMerge.Poly := [(nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
theorem block020_data_flat151_step : block020_data_flat151 = (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded) := by decide +kernel
theorem block020_data_flat151_original : block020_data_flat151 = (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded) := by
  rw [block020_data_flat151_step]
def block020_data_flat152 : CoefficientMerge.Poly := [(nat_lit 4676, Int.ofNat (nat_lit 3676453401600)), (nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
theorem block020_data_flat152_step : block020_data_flat152 = (CoefficientMerge.fastMerge block020_data_flat150 block020_data_flat151) := by decide +kernel
theorem block020_data_flat152_original : block020_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded)) := by
  rw [block020_data_flat152_step, block020_data_flat150_original, block020_data_flat151_original]
def block020_data_flat153 : CoefficientMerge.Poly := [(nat_lit 4675, Int.ofNat (nat_lit 2990259417600)), (nat_lit 4676, Int.ofNat (nat_lit 3676453401600)), (nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
theorem block020_data_flat153_step : block020_data_flat153 = (CoefficientMerge.fastMerge block020_data_flat149 block020_data_flat152) := by decide +kernel
theorem block020_data_flat153_original : block020_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded))) := by
  rw [block020_data_flat153_step, block020_data_flat149_original, block020_data_flat152_original]
def block020_data_flat154 : CoefficientMerge.Poly := [(nat_lit 4661, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4674, Int.ofNat (nat_lit 1365622675200)), (nat_lit 4675, Int.ofNat (nat_lit 2990259417600)), (nat_lit 4676, Int.ofNat (nat_lit 3676453401600)), (nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
theorem block020_data_flat154_step : block020_data_flat154 = (CoefficientMerge.fastMerge block020_data_flat148 block020_data_flat153) := by decide +kernel
theorem block020_data_flat154_original : block020_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded)))) := by
  rw [block020_data_flat154_step, block020_data_flat148_original, block020_data_flat153_original]
def block020_data_flat155 : CoefficientMerge.Poly := [(nat_lit 4655, Int.ofNat (nat_lit 854359833600)), (nat_lit 4656, Int.ofNat (nat_lit 5701373284320)), (nat_lit 4658, Int.ofNat (nat_lit 10571867661600)), (nat_lit 4659, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4660, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4661, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4674, Int.ofNat (nat_lit 1365622675200)), (nat_lit 4675, Int.ofNat (nat_lit 2990259417600)), (nat_lit 4676, Int.ofNat (nat_lit 3676453401600)), (nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
theorem block020_data_flat155_step : block020_data_flat155 = (CoefficientMerge.fastMerge block020_data_flat145 block020_data_flat154) := by decide +kernel
theorem block020_data_flat155_original : block020_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded))))) := by
  rw [block020_data_flat155_step, block020_data_flat145_original, block020_data_flat154_original]
def block020_data_flat156 : CoefficientMerge.Poly := [(nat_lit 4367, Int.ofNat (nat_lit 44758527817500)), (nat_lit 4387, Int.ofNat (nat_lit 3308751684000)), (nat_lit 4388, Int.ofNat (nat_lit 15671181626100)), (nat_lit 4409, Int.ofNat (nat_lit 8870673060900)), (nat_lit 4630, Int.ofNat (nat_lit 597600864000)), (nat_lit 4631, Int.ofNat (nat_lit 427179916800)), (nat_lit 4635, Int.ofNat (nat_lit 3075590700000)), (nat_lit 4637, Int.ofNat (nat_lit 2234314202400)), (nat_lit 4652, Int.ofNat (nat_lit 938442758400)), (nat_lit 4654, Int.ofNat (nat_lit 427179916800)), (nat_lit 4655, Int.ofNat (nat_lit 854359833600)), (nat_lit 4656, Int.ofNat (nat_lit 5701373284320)), (nat_lit 4658, Int.ofNat (nat_lit 10571867661600)), (nat_lit 4659, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4660, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4661, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4674, Int.ofNat (nat_lit 1365622675200)), (nat_lit 4675, Int.ofNat (nat_lit 2990259417600)), (nat_lit 4676, Int.ofNat (nat_lit 3676453401600)), (nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
theorem block020_data_flat156_step : block020_data_flat156 = (CoefficientMerge.fastMerge block020_data_flat136 block020_data_flat155) := by decide +kernel
theorem block020_data_flat156_original : block020_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded)))))) := by
  rw [block020_data_flat156_step, block020_data_flat136_original, block020_data_flat155_original]
def block020_data_flat157 : CoefficientMerge.Poly := [(nat_lit 4281, Int.ofNat (nat_lit 48700483725600)), (nat_lit 4282, Int.ofNat (nat_lit 49598093109600)), (nat_lit 4283, Int.ofNat (nat_lit 74906046734400)), (nat_lit 4299, Int.ofNat (nat_lit 16795322611200)), (nat_lit 4300, Int.ofNat (nat_lit 35735021557200)), (nat_lit 4301, Int.ofNat (nat_lit 64884545510400)), (nat_lit 4302, Int.ofNat (nat_lit 69986611724400)), (nat_lit 4303, Int.ofNat (nat_lit 53647060446000)), (nat_lit 4304, Int.ofNat (nat_lit 84256708258800)), (nat_lit 4321, Int.ofNat (nat_lit 14605687272960)), (nat_lit 4322, Int.ofNat (nat_lit 55660876311600)), (nat_lit 4323, Int.ofNat (nat_lit 65795220880200)), (nat_lit 4324, Int.ofNat (nat_lit 48673825250400)), (nat_lit 4325, Int.ofNat (nat_lit 66408854078700)), (nat_lit 4343, Int.ofNat (nat_lit 41744447539200)), (nat_lit 4344, Int.ofNat (nat_lit 76111510784400)), (nat_lit 4345, Int.ofNat (nat_lit 52712801442000)), (nat_lit 4346, Int.ofNat (nat_lit 58566148880400)), (nat_lit 4365, Int.ofNat (nat_lit 28394930554200)), (nat_lit 4366, Int.ofNat (nat_lit 36513604071000)), (nat_lit 4367, Int.ofNat (nat_lit 44758527817500)), (nat_lit 4387, Int.ofNat (nat_lit 3308751684000)), (nat_lit 4388, Int.ofNat (nat_lit 15671181626100)), (nat_lit 4409, Int.ofNat (nat_lit 8870673060900)), (nat_lit 4630, Int.ofNat (nat_lit 597600864000)), (nat_lit 4631, Int.ofNat (nat_lit 427179916800)), (nat_lit 4635, Int.ofNat (nat_lit 3075590700000)), (nat_lit 4637, Int.ofNat (nat_lit 2234314202400)), (nat_lit 4652, Int.ofNat (nat_lit 938442758400)), (nat_lit 4654, Int.ofNat (nat_lit 427179916800)), (nat_lit 4655, Int.ofNat (nat_lit 854359833600)), (nat_lit 4656, Int.ofNat (nat_lit 5701373284320)), (nat_lit 4658, Int.ofNat (nat_lit 10571867661600)), (nat_lit 4659, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4660, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4661, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4674, Int.ofNat (nat_lit 1365622675200)), (nat_lit 4675, Int.ofNat (nat_lit 2990259417600)), (nat_lit 4676, Int.ofNat (nat_lit 3676453401600)), (nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
theorem block020_data_flat157_step : block020_data_flat157 = (CoefficientMerge.fastMerge block020_data_flat117 block020_data_flat156) := by decide +kernel
theorem block020_data_flat157_original : block020_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded))))))) := by
  rw [block020_data_flat157_step, block020_data_flat117_original, block020_data_flat156_original]
def block020_data_flat158 : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 182739160800)), (nat_lit 4189, Int.ofNat (nat_lit 770276908800)), (nat_lit 4192, Int.ofNat (nat_lit 427179916800)), (nat_lit 4193, Int.ofNat (nat_lit 854359833600)), (nat_lit 4194, Int.ofNat (nat_lit 5669444229120)), (nat_lit 4196, Int.ofNat (nat_lit 6132165580800)), (nat_lit 4197, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4198, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4199, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4211, Int.ofNat (nat_lit 1533788524800)), (nat_lit 4212, Int.ofNat (nat_lit 1876885516800)), (nat_lit 4213, Int.ofNat (nat_lit 2563079500800)), (nat_lit 4214, Int.ofNat (nat_lit 3249273484800)), (nat_lit 4215, Int.ofNat (nat_lit 6681901564800)), (nat_lit 4216, Int.ofNat (nat_lit 1017686224800)), (nat_lit 4217, Int.ofNat (nat_lit 12075930115200)), (nat_lit 4218, Int.ofNat (nat_lit 10740378448800)), (nat_lit 4219, Int.ofNat (nat_lit 20105092879200)), (nat_lit 4220, Int.ofNat (nat_lit 31025632780800)), (nat_lit 4233, Int.ofNat (nat_lit 3074342342400)), (nat_lit 4234, Int.ofNat (nat_lit 6498546969600)), (nat_lit 4235, Int.ofNat (nat_lit 7275589171200)), (nat_lit 4236, Int.ofNat (nat_lit 8588646595200)), (nat_lit 4237, Int.ofNat (nat_lit 6994941380000)), (nat_lit 4238, Int.ofNat (nat_lit 18707359395200)), (nat_lit 4239, Int.ofNat (nat_lit 19393808039200)), (nat_lit 4240, Int.ofNat (nat_lit 29075845864800)), (nat_lit 4241, Int.ofNat (nat_lit 40801239259200)), (nat_lit 4255, Int.ofNat (nat_lit 5863944096000)), (nat_lit 4256, Int.ofNat (nat_lit 11257079040000)), (nat_lit 4257, Int.ofNat (nat_lit 13909039300800)), (nat_lit 4258, Int.ofNat (nat_lit 13518234338400)), (nat_lit 4259, Int.ofNat (nat_lit 29696485795200)), (nat_lit 4260, Int.ofNat (nat_lit 32840704461600)), (nat_lit 4261, Int.ofNat (nat_lit 37111606192800)), (nat_lit 4262, Int.ofNat (nat_lit 55562141678400)), (nat_lit 4277, Int.ofNat (nat_lit 10101226464000)), (nat_lit 4278, Int.ofNat (nat_lit 19117589904000)), (nat_lit 4279, Int.ofNat (nat_lit 19922377860000)), (nat_lit 4280, Int.ofNat (nat_lit 42879142051200)), (nat_lit 4281, Int.ofNat (nat_lit 48700483725600)), (nat_lit 4282, Int.ofNat (nat_lit 49598093109600)), (nat_lit 4283, Int.ofNat (nat_lit 74906046734400)), (nat_lit 4299, Int.ofNat (nat_lit 16795322611200)), (nat_lit 4300, Int.ofNat (nat_lit 35735021557200)), (nat_lit 4301, Int.ofNat (nat_lit 64884545510400)), (nat_lit 4302, Int.ofNat (nat_lit 69986611724400)), (nat_lit 4303, Int.ofNat (nat_lit 53647060446000)), (nat_lit 4304, Int.ofNat (nat_lit 84256708258800)), (nat_lit 4321, Int.ofNat (nat_lit 14605687272960)), (nat_lit 4322, Int.ofNat (nat_lit 55660876311600)), (nat_lit 4323, Int.ofNat (nat_lit 65795220880200)), (nat_lit 4324, Int.ofNat (nat_lit 48673825250400)), (nat_lit 4325, Int.ofNat (nat_lit 66408854078700)), (nat_lit 4343, Int.ofNat (nat_lit 41744447539200)), (nat_lit 4344, Int.ofNat (nat_lit 76111510784400)), (nat_lit 4345, Int.ofNat (nat_lit 52712801442000)), (nat_lit 4346, Int.ofNat (nat_lit 58566148880400)), (nat_lit 4365, Int.ofNat (nat_lit 28394930554200)), (nat_lit 4366, Int.ofNat (nat_lit 36513604071000)), (nat_lit 4367, Int.ofNat (nat_lit 44758527817500)), (nat_lit 4387, Int.ofNat (nat_lit 3308751684000)), (nat_lit 4388, Int.ofNat (nat_lit 15671181626100)), (nat_lit 4409, Int.ofNat (nat_lit 8870673060900)), (nat_lit 4630, Int.ofNat (nat_lit 597600864000)), (nat_lit 4631, Int.ofNat (nat_lit 427179916800)), (nat_lit 4635, Int.ofNat (nat_lit 3075590700000)), (nat_lit 4637, Int.ofNat (nat_lit 2234314202400)), (nat_lit 4652, Int.ofNat (nat_lit 938442758400)), (nat_lit 4654, Int.ofNat (nat_lit 427179916800)), (nat_lit 4655, Int.ofNat (nat_lit 854359833600)), (nat_lit 4656, Int.ofNat (nat_lit 5701373284320)), (nat_lit 4658, Int.ofNat (nat_lit 10571867661600)), (nat_lit 4659, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4660, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4661, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4674, Int.ofNat (nat_lit 1365622675200)), (nat_lit 4675, Int.ofNat (nat_lit 2990259417600)), (nat_lit 4676, Int.ofNat (nat_lit 3676453401600)), (nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
theorem block020_data_flat158_step : block020_data_flat158 = (CoefficientMerge.fastMerge block020_data_flat078 block020_data_flat157) := by decide +kernel
theorem block020_data_flat158_original : block020_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded)))))))) := by
  rw [block020_data_flat158_step, block020_data_flat078_original, block020_data_flat157_original]
def block020_data_flat159 : CoefficientMerge.Poly := [(nat_lit 4175, Int.ofNat (nat_lit 182739160800)), (nat_lit 4189, Int.ofNat (nat_lit 770276908800)), (nat_lit 4192, Int.ofNat (nat_lit 427179916800)), (nat_lit 4193, Int.ofNat (nat_lit 854359833600)), (nat_lit 4194, Int.ofNat (nat_lit 5669444229120)), (nat_lit 4196, Int.ofNat (nat_lit 6132165580800)), (nat_lit 4197, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4198, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4199, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4211, Int.ofNat (nat_lit 1533788524800)), (nat_lit 4212, Int.ofNat (nat_lit 1876885516800)), (nat_lit 4213, Int.ofNat (nat_lit 2563079500800)), (nat_lit 4214, Int.ofNat (nat_lit 3249273484800)), (nat_lit 4215, Int.ofNat (nat_lit 6681901564800)), (nat_lit 4216, Int.ofNat (nat_lit 1017686224800)), (nat_lit 4217, Int.ofNat (nat_lit 12075930115200)), (nat_lit 4218, Int.ofNat (nat_lit 10740378448800)), (nat_lit 4219, Int.ofNat (nat_lit 20105092879200)), (nat_lit 4220, Int.ofNat (nat_lit 31025632780800)), (nat_lit 4233, Int.ofNat (nat_lit 3074342342400)), (nat_lit 4234, Int.ofNat (nat_lit 6498546969600)), (nat_lit 4235, Int.ofNat (nat_lit 7275589171200)), (nat_lit 4236, Int.ofNat (nat_lit 8588646595200)), (nat_lit 4237, Int.ofNat (nat_lit 6994941380000)), (nat_lit 4238, Int.ofNat (nat_lit 18707359395200)), (nat_lit 4239, Int.ofNat (nat_lit 19393808039200)), (nat_lit 4240, Int.ofNat (nat_lit 29075845864800)), (nat_lit 4241, Int.ofNat (nat_lit 40801239259200)), (nat_lit 4255, Int.ofNat (nat_lit 5863944096000)), (nat_lit 4256, Int.ofNat (nat_lit 11257079040000)), (nat_lit 4257, Int.ofNat (nat_lit 13909039300800)), (nat_lit 4258, Int.ofNat (nat_lit 13518234338400)), (nat_lit 4259, Int.ofNat (nat_lit 29696485795200)), (nat_lit 4260, Int.ofNat (nat_lit 32840704461600)), (nat_lit 4261, Int.ofNat (nat_lit 37111606192800)), (nat_lit 4262, Int.ofNat (nat_lit 55562141678400)), (nat_lit 4277, Int.ofNat (nat_lit 10101226464000)), (nat_lit 4278, Int.ofNat (nat_lit 19117589904000)), (nat_lit 4279, Int.ofNat (nat_lit 19922377860000)), (nat_lit 4280, Int.ofNat (nat_lit 42879142051200)), (nat_lit 4281, Int.ofNat (nat_lit 48700483725600)), (nat_lit 4282, Int.ofNat (nat_lit 49598093109600)), (nat_lit 4283, Int.ofNat (nat_lit 74906046734400)), (nat_lit 4299, Int.ofNat (nat_lit 16795322611200)), (nat_lit 4300, Int.ofNat (nat_lit 35735021557200)), (nat_lit 4301, Int.ofNat (nat_lit 64884545510400)), (nat_lit 4302, Int.ofNat (nat_lit 69986611724400)), (nat_lit 4303, Int.ofNat (nat_lit 53647060446000)), (nat_lit 4304, Int.ofNat (nat_lit 84256708258800)), (nat_lit 4321, Int.ofNat (nat_lit 14605687272960)), (nat_lit 4322, Int.ofNat (nat_lit 55660876311600)), (nat_lit 4323, Int.ofNat (nat_lit 65795220880200)), (nat_lit 4324, Int.ofNat (nat_lit 48673825250400)), (nat_lit 4325, Int.ofNat (nat_lit 66408854078700)), (nat_lit 4343, Int.ofNat (nat_lit 41744447539200)), (nat_lit 4344, Int.ofNat (nat_lit 76111510784400)), (nat_lit 4345, Int.ofNat (nat_lit 52712801442000)), (nat_lit 4346, Int.ofNat (nat_lit 58566148880400)), (nat_lit 4365, Int.ofNat (nat_lit 28394930554200)), (nat_lit 4366, Int.ofNat (nat_lit 36513604071000)), (nat_lit 4367, Int.ofNat (nat_lit 44758527817500)), (nat_lit 4387, Int.ofNat (nat_lit 3308751684000)), (nat_lit 4388, Int.ofNat (nat_lit 15671181626100)), (nat_lit 4409, Int.ofNat (nat_lit 8870673060900)), (nat_lit 4630, Int.ofNat (nat_lit 597600864000)), (nat_lit 4631, Int.ofNat (nat_lit 427179916800)), (nat_lit 4635, Int.ofNat (nat_lit 3075590700000)), (nat_lit 4637, Int.ofNat (nat_lit 2234314202400)), (nat_lit 4652, Int.ofNat (nat_lit 938442758400)), (nat_lit 4654, Int.ofNat (nat_lit 427179916800)), (nat_lit 4655, Int.ofNat (nat_lit 854359833600)), (nat_lit 4656, Int.ofNat (nat_lit 5701373284320)), (nat_lit 4658, Int.ofNat (nat_lit 10571867661600)), (nat_lit 4659, Int.ofNat (nat_lit 5786258284800)), (nat_lit 4660, Int.ofNat (nat_lit 11171238059520)), (nat_lit 4661, Int.ofNat (nat_lit 17391151612800)), (nat_lit 4674, Int.ofNat (nat_lit 1365622675200)), (nat_lit 4675, Int.ofNat (nat_lit 2990259417600)), (nat_lit 4676, Int.ofNat (nat_lit 3676453401600)), (nat_lit 4677, Int.ofNat (nat_lit 3338277354720))]
theorem block020_data_flat159_step : block020_data_flat159 = (CoefficientMerge.trim block020_data_flat158) := by decide +kernel
theorem block020_data_flat159_original : block020_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded))))))))) := by
  rw [block020_data_flat159_step, block020_data_flat158_original]
theorem block020_data : block020 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded)))))))) := by
  have h : block020 = block020_data_flat159 := by decide +kernel
  exact h.trans block020_data_flat159_original
theorem block020_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block020 := by
  rw [block020_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1456Coded_nonneg g hg hA hB) (atom1457Coded_nonneg g hg hA hB)) (add_nonneg (atom1458Coded_nonneg g hg hA hB) (add_nonneg (atom1459Coded_nonneg g hg hA hB) (atom1460Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1461Coded_nonneg g hg hA hB) (atom1462Coded_nonneg g hg hA hB)) (add_nonneg (atom1463Coded_nonneg g hg hA hB) (add_nonneg (atom1464Coded_nonneg g hg hA hB) (atom1465Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1466Coded_nonneg g hg hA hB) (atom1467Coded_nonneg g hg hA hB)) (add_nonneg (atom1468Coded_nonneg g hg hA hB) (add_nonneg (atom1469Coded_nonneg g hg hA hB) (atom1470Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1471Coded_nonneg g hg hA hB) (atom1472Coded_nonneg g hg hA hB)) (add_nonneg (atom1473Coded_nonneg g hg hA hB) (add_nonneg (atom1474Coded_nonneg g hg hA hB) (atom1475Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1476Coded_nonneg g hg hA hB) (atom1477Coded_nonneg g hg hA hB)) (add_nonneg (atom1478Coded_nonneg g hg hA hB) (add_nonneg (atom1479Coded_nonneg g hg hA hB) (atom1480Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1481Coded_nonneg g hg hA hB) (atom1482Coded_nonneg g hg hA hB)) (add_nonneg (atom1483Coded_nonneg g hg hA hB) (add_nonneg (atom1484Coded_nonneg g hg hA hB) (atom1485Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1486Coded_nonneg g hg hA hB) (atom1487Coded_nonneg g hg hA hB)) (add_nonneg (atom1488Coded_nonneg g hg hA hB) (add_nonneg (atom1489Coded_nonneg g hg hA hB) (atom1490Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1491Coded_nonneg g hg hA hB) (atom1492Coded_nonneg g hg hA hB)) (add_nonneg (atom1493Coded_nonneg g hg hA hB) (add_nonneg (atom1494Coded_nonneg g hg hA hB) (atom1495Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1496Coded_nonneg g hg hA hB) (atom1497Coded_nonneg g hg hA hB)) (add_nonneg (atom1498Coded_nonneg g hg hA hB) (add_nonneg (atom1499Coded_nonneg g hg hA hB) (atom1500Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1501Coded_nonneg g hg hA hB) (atom1502Coded_nonneg g hg hA hB)) (add_nonneg (atom1503Coded_nonneg g hg hA hB) (add_nonneg (atom1504Coded_nonneg g hg hA hB) (atom1505Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1506Coded_nonneg g hg hA hB) (atom1507Coded_nonneg g hg hA hB)) (add_nonneg (atom1508Coded_nonneg g hg hA hB) (add_nonneg (atom1509Coded_nonneg g hg hA hB) (atom1510Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1511Coded_nonneg g hg hA hB) (atom1512Coded_nonneg g hg hA hB)) (add_nonneg (atom1513Coded_nonneg g hg hA hB) (add_nonneg (atom1514Coded_nonneg g hg hA hB) (atom1515Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1516Coded_nonneg g hg hA hB) (atom1517Coded_nonneg g hg hA hB)) (add_nonneg (atom1518Coded_nonneg g hg hA hB) (add_nonneg (atom1519Coded_nonneg g hg hA hB) (atom1520Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1521Coded_nonneg g hg hA hB) (atom1522Coded_nonneg g hg hA hB)) (add_nonneg (atom1523Coded_nonneg g hg hA hB) (add_nonneg (atom1524Coded_nonneg g hg hA hB) (atom1525Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1526Coded_nonneg g hg hA hB) (atom1527Coded_nonneg g hg hA hB)) (add_nonneg (atom1528Coded_nonneg g hg hA hB) (add_nonneg (atom1529Coded_nonneg g hg hA hB) (atom1530Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1531Coded_nonneg g hg hA hB) (atom1532Coded_nonneg g hg hA hB)) (add_nonneg (atom1533Coded_nonneg g hg hA hB) (add_nonneg (atom1534Coded_nonneg g hg hA hB) (atom1535Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
