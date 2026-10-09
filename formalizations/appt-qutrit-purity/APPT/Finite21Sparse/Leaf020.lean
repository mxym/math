import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1456 : SparsePolynomial.Poly := [([9,9,17], 1)]
theorem eval_atom1456 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1456 = ((g 9) * (g 9) * (g 17)) := by
  norm_num [atom1456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1456_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182739160800 : Int) atom1456) := by
  rw [SparsePolynomial.eval_scale, eval_atom1456]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1456Coded : CoefficientMerge.Poly := [(4175, 1)]
theorem atom1456Coded_decode : atom1456 = SparsePolynomial.decodeCubic 21 atom1456Coded := by decide +kernel
theorem atom1456Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) := by
  have h := atom1456_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1456Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1457 : SparsePolynomial.Poly := [([9,10,10], 1)]
theorem eval_atom1457 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1457 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom1457, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1457_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (770276908800 : Int) atom1457) := by
  rw [SparsePolynomial.eval_scale, eval_atom1457]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1457Coded : CoefficientMerge.Poly := [(4189, 1)]
theorem atom1457Coded_decode : atom1457 = SparsePolynomial.decodeCubic 21 atom1457Coded := by decide +kernel
theorem atom1457Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded) := by
  have h := atom1457_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1457Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1458 : SparsePolynomial.Poly := [([9,10,13], 1)]
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
def atom1458Coded : CoefficientMerge.Poly := [(4192, 1)]
theorem atom1458Coded_decode : atom1458 = SparsePolynomial.decodeCubic 21 atom1458Coded := by decide +kernel
theorem atom1458Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) := by
  have h := atom1458_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1458Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1459 : SparsePolynomial.Poly := [([9,10,14], 1)]
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
def atom1459Coded : CoefficientMerge.Poly := [(4193, 1)]
theorem atom1459Coded_decode : atom1459 = SparsePolynomial.decodeCubic 21 atom1459Coded := by decide +kernel
theorem atom1459Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) := by
  have h := atom1459_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1459Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1460 : SparsePolynomial.Poly := [([9,10,15], 1)]
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
def atom1460Coded : CoefficientMerge.Poly := [(4194, 1)]
theorem atom1460Coded_decode : atom1460 = SparsePolynomial.decodeCubic 21 atom1460Coded := by decide +kernel
theorem atom1460Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded) := by
  have h := atom1460_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1460Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1461 : SparsePolynomial.Poly := [([9,10,17], 1)]
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
def atom1461Coded : CoefficientMerge.Poly := [(4196, 1)]
theorem atom1461Coded_decode : atom1461 = SparsePolynomial.decodeCubic 21 atom1461Coded := by decide +kernel
theorem atom1461Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) := by
  have h := atom1461_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1461Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1462 : SparsePolynomial.Poly := [([9,10,18], 1)]
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
def atom1462Coded : CoefficientMerge.Poly := [(4197, 1)]
theorem atom1462Coded_decode : atom1462 = SparsePolynomial.decodeCubic 21 atom1462Coded := by decide +kernel
theorem atom1462Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded) := by
  have h := atom1462_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1462Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1463 : SparsePolynomial.Poly := [([9,10,19], 1)]
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
def atom1463Coded : CoefficientMerge.Poly := [(4198, 1)]
theorem atom1463Coded_decode : atom1463 = SparsePolynomial.decodeCubic 21 atom1463Coded := by decide +kernel
theorem atom1463Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) := by
  have h := atom1463_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1463Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1464 : SparsePolynomial.Poly := [([9,10,20], 1)]
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
def atom1464Coded : CoefficientMerge.Poly := [(4199, 1)]
theorem atom1464Coded_decode : atom1464 = SparsePolynomial.decodeCubic 21 atom1464Coded := by decide +kernel
theorem atom1464Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) := by
  have h := atom1464_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1464Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1465 : SparsePolynomial.Poly := [([9,11,11], 1)]
theorem eval_atom1465 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1465 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom1465, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1465_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1533788524800 : Int) atom1465) := by
  rw [SparsePolynomial.eval_scale, eval_atom1465]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1465Coded : CoefficientMerge.Poly := [(4211, 1)]
theorem atom1465Coded_decode : atom1465 = SparsePolynomial.decodeCubic 21 atom1465Coded := by decide +kernel
theorem atom1465Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded) := by
  have h := atom1465_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1465Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1466 : SparsePolynomial.Poly := [([9,11,12], 1)]
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
def atom1466Coded : CoefficientMerge.Poly := [(4212, 1)]
theorem atom1466Coded_decode : atom1466 = SparsePolynomial.decodeCubic 21 atom1466Coded := by decide +kernel
theorem atom1466Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) := by
  have h := atom1466_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1466Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1467 : SparsePolynomial.Poly := [([9,11,13], 1)]
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
def atom1467Coded : CoefficientMerge.Poly := [(4213, 1)]
theorem atom1467Coded_decode : atom1467 = SparsePolynomial.decodeCubic 21 atom1467Coded := by decide +kernel
theorem atom1467Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded) := by
  have h := atom1467_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1467Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1468 : SparsePolynomial.Poly := [([9,11,14], 1)]
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
def atom1468Coded : CoefficientMerge.Poly := [(4214, 1)]
theorem atom1468Coded_decode : atom1468 = SparsePolynomial.decodeCubic 21 atom1468Coded := by decide +kernel
theorem atom1468Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) := by
  have h := atom1468_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1468Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1469 : SparsePolynomial.Poly := [([9,11,15], 1)]
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
def atom1469Coded : CoefficientMerge.Poly := [(4215, 1)]
theorem atom1469Coded_decode : atom1469 = SparsePolynomial.decodeCubic 21 atom1469Coded := by decide +kernel
theorem atom1469Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) := by
  have h := atom1469_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1469Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1470 : SparsePolynomial.Poly := [([9,11,16], 1)]
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
def atom1470Coded : CoefficientMerge.Poly := [(4216, 1)]
theorem atom1470Coded_decode : atom1470 = SparsePolynomial.decodeCubic 21 atom1470Coded := by decide +kernel
theorem atom1470Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded) := by
  have h := atom1470_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1470Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1471 : SparsePolynomial.Poly := [([9,11,17], 1)]
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
def atom1471Coded : CoefficientMerge.Poly := [(4217, 1)]
theorem atom1471Coded_decode : atom1471 = SparsePolynomial.decodeCubic 21 atom1471Coded := by decide +kernel
theorem atom1471Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) := by
  have h := atom1471_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1471Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1472 : SparsePolynomial.Poly := [([9,11,18], 1)]
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
def atom1472Coded : CoefficientMerge.Poly := [(4218, 1)]
theorem atom1472Coded_decode : atom1472 = SparsePolynomial.decodeCubic 21 atom1472Coded := by decide +kernel
theorem atom1472Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded) := by
  have h := atom1472_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1472Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1473 : SparsePolynomial.Poly := [([9,11,19], 1)]
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
def atom1473Coded : CoefficientMerge.Poly := [(4219, 1)]
theorem atom1473Coded_decode : atom1473 = SparsePolynomial.decodeCubic 21 atom1473Coded := by decide +kernel
theorem atom1473Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) := by
  have h := atom1473_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1473Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1474 : SparsePolynomial.Poly := [([9,11,20], 1)]
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
def atom1474Coded : CoefficientMerge.Poly := [(4220, 1)]
theorem atom1474Coded_decode : atom1474 = SparsePolynomial.decodeCubic 21 atom1474Coded := by decide +kernel
theorem atom1474Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) := by
  have h := atom1474_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1474Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1475 : SparsePolynomial.Poly := [([9,12,12], 1)]
theorem eval_atom1475 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1475 = ((g 9) * (g 12) * (g 12)) := by
  norm_num [atom1475, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1475_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3074342342400 : Int) atom1475) := by
  rw [SparsePolynomial.eval_scale, eval_atom1475]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1475Coded : CoefficientMerge.Poly := [(4233, 1)]
theorem atom1475Coded_decode : atom1475 = SparsePolynomial.decodeCubic 21 atom1475Coded := by decide +kernel
theorem atom1475Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded) := by
  have h := atom1475_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1475Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1476 : SparsePolynomial.Poly := [([9,12,13], 1)]
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
def atom1476Coded : CoefficientMerge.Poly := [(4234, 1)]
theorem atom1476Coded_decode : atom1476 = SparsePolynomial.decodeCubic 21 atom1476Coded := by decide +kernel
theorem atom1476Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) := by
  have h := atom1476_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1476Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1477 : SparsePolynomial.Poly := [([9,12,14], 1)]
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
def atom1477Coded : CoefficientMerge.Poly := [(4235, 1)]
theorem atom1477Coded_decode : atom1477 = SparsePolynomial.decodeCubic 21 atom1477Coded := by decide +kernel
theorem atom1477Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded) := by
  have h := atom1477_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1477Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1478 : SparsePolynomial.Poly := [([9,12,15], 1)]
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
def atom1478Coded : CoefficientMerge.Poly := [(4236, 1)]
theorem atom1478Coded_decode : atom1478 = SparsePolynomial.decodeCubic 21 atom1478Coded := by decide +kernel
theorem atom1478Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) := by
  have h := atom1478_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1478Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1479 : SparsePolynomial.Poly := [([9,12,16], 1)]
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
def atom1479Coded : CoefficientMerge.Poly := [(4237, 1)]
theorem atom1479Coded_decode : atom1479 = SparsePolynomial.decodeCubic 21 atom1479Coded := by decide +kernel
theorem atom1479Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) := by
  have h := atom1479_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1479Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1480 : SparsePolynomial.Poly := [([9,12,17], 1)]
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
def atom1480Coded : CoefficientMerge.Poly := [(4238, 1)]
theorem atom1480Coded_decode : atom1480 = SparsePolynomial.decodeCubic 21 atom1480Coded := by decide +kernel
theorem atom1480Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded) := by
  have h := atom1480_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1480Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1481 : SparsePolynomial.Poly := [([9,12,18], 1)]
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
def atom1481Coded : CoefficientMerge.Poly := [(4239, 1)]
theorem atom1481Coded_decode : atom1481 = SparsePolynomial.decodeCubic 21 atom1481Coded := by decide +kernel
theorem atom1481Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) := by
  have h := atom1481_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1481Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1482 : SparsePolynomial.Poly := [([9,12,19], 1)]
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
def atom1482Coded : CoefficientMerge.Poly := [(4240, 1)]
theorem atom1482Coded_decode : atom1482 = SparsePolynomial.decodeCubic 21 atom1482Coded := by decide +kernel
theorem atom1482Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded) := by
  have h := atom1482_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1482Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1483 : SparsePolynomial.Poly := [([9,12,20], 1)]
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
def atom1483Coded : CoefficientMerge.Poly := [(4241, 1)]
theorem atom1483Coded_decode : atom1483 = SparsePolynomial.decodeCubic 21 atom1483Coded := by decide +kernel
theorem atom1483Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) := by
  have h := atom1483_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1483Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1484 : SparsePolynomial.Poly := [([9,13,13], 1)]
theorem eval_atom1484 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1484 = ((g 9) * (g 13) * (g 13)) := by
  norm_num [atom1484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1484_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5863944096000 : Int) atom1484) := by
  rw [SparsePolynomial.eval_scale, eval_atom1484]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1484Coded : CoefficientMerge.Poly := [(4255, 1)]
theorem atom1484Coded_decode : atom1484 = SparsePolynomial.decodeCubic 21 atom1484Coded := by decide +kernel
theorem atom1484Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) := by
  have h := atom1484_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1484Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1485 : SparsePolynomial.Poly := [([9,13,14], 1)]
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
def atom1485Coded : CoefficientMerge.Poly := [(4256, 1)]
theorem atom1485Coded_decode : atom1485 = SparsePolynomial.decodeCubic 21 atom1485Coded := by decide +kernel
theorem atom1485Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded) := by
  have h := atom1485_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1485Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1486 : SparsePolynomial.Poly := [([9,13,15], 1)]
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
def atom1486Coded : CoefficientMerge.Poly := [(4257, 1)]
theorem atom1486Coded_decode : atom1486 = SparsePolynomial.decodeCubic 21 atom1486Coded := by decide +kernel
theorem atom1486Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) := by
  have h := atom1486_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1486Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1487 : SparsePolynomial.Poly := [([9,13,16], 1)]
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
def atom1487Coded : CoefficientMerge.Poly := [(4258, 1)]
theorem atom1487Coded_decode : atom1487 = SparsePolynomial.decodeCubic 21 atom1487Coded := by decide +kernel
theorem atom1487Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded) := by
  have h := atom1487_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1487Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1488 : SparsePolynomial.Poly := [([9,13,17], 1)]
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
def atom1488Coded : CoefficientMerge.Poly := [(4259, 1)]
theorem atom1488Coded_decode : atom1488 = SparsePolynomial.decodeCubic 21 atom1488Coded := by decide +kernel
theorem atom1488Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) := by
  have h := atom1488_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1488Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1489 : SparsePolynomial.Poly := [([9,13,18], 1)]
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
def atom1489Coded : CoefficientMerge.Poly := [(4260, 1)]
theorem atom1489Coded_decode : atom1489 = SparsePolynomial.decodeCubic 21 atom1489Coded := by decide +kernel
theorem atom1489Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) := by
  have h := atom1489_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1489Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1490 : SparsePolynomial.Poly := [([9,13,19], 1)]
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
def atom1490Coded : CoefficientMerge.Poly := [(4261, 1)]
theorem atom1490Coded_decode : atom1490 = SparsePolynomial.decodeCubic 21 atom1490Coded := by decide +kernel
theorem atom1490Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded) := by
  have h := atom1490_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1490Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1491 : SparsePolynomial.Poly := [([9,13,20], 1)]
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
def atom1491Coded : CoefficientMerge.Poly := [(4262, 1)]
theorem atom1491Coded_decode : atom1491 = SparsePolynomial.decodeCubic 21 atom1491Coded := by decide +kernel
theorem atom1491Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) := by
  have h := atom1491_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1491Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1492 : SparsePolynomial.Poly := [([9,14,14], 1)]
theorem eval_atom1492 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1492 = ((g 9) * (g 14) * (g 14)) := by
  norm_num [atom1492, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1492_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10101226464000 : Int) atom1492) := by
  rw [SparsePolynomial.eval_scale, eval_atom1492]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1492Coded : CoefficientMerge.Poly := [(4277, 1)]
theorem atom1492Coded_decode : atom1492 = SparsePolynomial.decodeCubic 21 atom1492Coded := by decide +kernel
theorem atom1492Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded) := by
  have h := atom1492_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1492Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1493 : SparsePolynomial.Poly := [([9,14,15], 1)]
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
def atom1493Coded : CoefficientMerge.Poly := [(4278, 1)]
theorem atom1493Coded_decode : atom1493 = SparsePolynomial.decodeCubic 21 atom1493Coded := by decide +kernel
theorem atom1493Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) := by
  have h := atom1493_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1493Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1494 : SparsePolynomial.Poly := [([9,14,16], 1)]
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
def atom1494Coded : CoefficientMerge.Poly := [(4279, 1)]
theorem atom1494Coded_decode : atom1494 = SparsePolynomial.decodeCubic 21 atom1494Coded := by decide +kernel
theorem atom1494Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) := by
  have h := atom1494_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1494Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1495 : SparsePolynomial.Poly := [([9,14,17], 1)]
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
def atom1495Coded : CoefficientMerge.Poly := [(4280, 1)]
theorem atom1495Coded_decode : atom1495 = SparsePolynomial.decodeCubic 21 atom1495Coded := by decide +kernel
theorem atom1495Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded) := by
  have h := atom1495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1496 : SparsePolynomial.Poly := [([9,14,18], 1)]
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
def atom1496Coded : CoefficientMerge.Poly := [(4281, 1)]
theorem atom1496Coded_decode : atom1496 = SparsePolynomial.decodeCubic 21 atom1496Coded := by decide +kernel
theorem atom1496Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) := by
  have h := atom1496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1497 : SparsePolynomial.Poly := [([9,14,19], 1)]
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
def atom1497Coded : CoefficientMerge.Poly := [(4282, 1)]
theorem atom1497Coded_decode : atom1497 = SparsePolynomial.decodeCubic 21 atom1497Coded := by decide +kernel
theorem atom1497Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded) := by
  have h := atom1497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1498 : SparsePolynomial.Poly := [([9,14,20], 1)]
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
def atom1498Coded : CoefficientMerge.Poly := [(4283, 1)]
theorem atom1498Coded_decode : atom1498 = SparsePolynomial.decodeCubic 21 atom1498Coded := by decide +kernel
theorem atom1498Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) := by
  have h := atom1498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1499 : SparsePolynomial.Poly := [([9,15,15], 1)]
theorem eval_atom1499 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1499 = ((g 9) * (g 15) * (g 15)) := by
  norm_num [atom1499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1499_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16795322611200 : Int) atom1499) := by
  rw [SparsePolynomial.eval_scale, eval_atom1499]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1499Coded : CoefficientMerge.Poly := [(4299, 1)]
theorem atom1499Coded_decode : atom1499 = SparsePolynomial.decodeCubic 21 atom1499Coded := by decide +kernel
theorem atom1499Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) := by
  have h := atom1499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1500 : SparsePolynomial.Poly := [([9,15,16], 1)]
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
def atom1500Coded : CoefficientMerge.Poly := [(4300, 1)]
theorem atom1500Coded_decode : atom1500 = SparsePolynomial.decodeCubic 21 atom1500Coded := by decide +kernel
theorem atom1500Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded) := by
  have h := atom1500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1501 : SparsePolynomial.Poly := [([9,15,17], 1)]
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
def atom1501Coded : CoefficientMerge.Poly := [(4301, 1)]
theorem atom1501Coded_decode : atom1501 = SparsePolynomial.decodeCubic 21 atom1501Coded := by decide +kernel
theorem atom1501Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) := by
  have h := atom1501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1502 : SparsePolynomial.Poly := [([9,15,18], 1)]
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
def atom1502Coded : CoefficientMerge.Poly := [(4302, 1)]
theorem atom1502Coded_decode : atom1502 = SparsePolynomial.decodeCubic 21 atom1502Coded := by decide +kernel
theorem atom1502Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded) := by
  have h := atom1502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1503 : SparsePolynomial.Poly := [([9,15,19], 1)]
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
def atom1503Coded : CoefficientMerge.Poly := [(4303, 1)]
theorem atom1503Coded_decode : atom1503 = SparsePolynomial.decodeCubic 21 atom1503Coded := by decide +kernel
theorem atom1503Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) := by
  have h := atom1503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1504 : SparsePolynomial.Poly := [([9,15,20], 1)]
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
def atom1504Coded : CoefficientMerge.Poly := [(4304, 1)]
theorem atom1504Coded_decode : atom1504 = SparsePolynomial.decodeCubic 21 atom1504Coded := by decide +kernel
theorem atom1504Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) := by
  have h := atom1504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1505 : SparsePolynomial.Poly := [([9,16,16], 1)]
theorem eval_atom1505 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1505 = ((g 9) * (g 16) * (g 16)) := by
  norm_num [atom1505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1505_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14605687272960 : Int) atom1505) := by
  rw [SparsePolynomial.eval_scale, eval_atom1505]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 9) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1505Coded : CoefficientMerge.Poly := [(4321, 1)]
theorem atom1505Coded_decode : atom1505 = SparsePolynomial.decodeCubic 21 atom1505Coded := by decide +kernel
theorem atom1505Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded) := by
  have h := atom1505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1506 : SparsePolynomial.Poly := [([9,16,17], 1)]
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
def atom1506Coded : CoefficientMerge.Poly := [(4322, 1)]
theorem atom1506Coded_decode : atom1506 = SparsePolynomial.decodeCubic 21 atom1506Coded := by decide +kernel
theorem atom1506Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) := by
  have h := atom1506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1507 : SparsePolynomial.Poly := [([9,16,18], 1)]
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
def atom1507Coded : CoefficientMerge.Poly := [(4323, 1)]
theorem atom1507Coded_decode : atom1507 = SparsePolynomial.decodeCubic 21 atom1507Coded := by decide +kernel
theorem atom1507Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded) := by
  have h := atom1507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1508 : SparsePolynomial.Poly := [([9,16,19], 1)]
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
def atom1508Coded : CoefficientMerge.Poly := [(4324, 1)]
theorem atom1508Coded_decode : atom1508 = SparsePolynomial.decodeCubic 21 atom1508Coded := by decide +kernel
theorem atom1508Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) := by
  have h := atom1508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1509 : SparsePolynomial.Poly := [([9,16,20], 1)]
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
def atom1509Coded : CoefficientMerge.Poly := [(4325, 1)]
theorem atom1509Coded_decode : atom1509 = SparsePolynomial.decodeCubic 21 atom1509Coded := by decide +kernel
theorem atom1509Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) := by
  have h := atom1509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1510 : SparsePolynomial.Poly := [([9,17,17], 1)]
theorem eval_atom1510 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1510 = ((g 9) * (g 17) * (g 17)) := by
  norm_num [atom1510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1510_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41744447539200 : Int) atom1510) := by
  rw [SparsePolynomial.eval_scale, eval_atom1510]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 9) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1510Coded : CoefficientMerge.Poly := [(4343, 1)]
theorem atom1510Coded_decode : atom1510 = SparsePolynomial.decodeCubic 21 atom1510Coded := by decide +kernel
theorem atom1510Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded) := by
  have h := atom1510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1511 : SparsePolynomial.Poly := [([9,17,18], 1)]
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
def atom1511Coded : CoefficientMerge.Poly := [(4344, 1)]
theorem atom1511Coded_decode : atom1511 = SparsePolynomial.decodeCubic 21 atom1511Coded := by decide +kernel
theorem atom1511Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) := by
  have h := atom1511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1512 : SparsePolynomial.Poly := [([9,17,19], 1)]
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
def atom1512Coded : CoefficientMerge.Poly := [(4345, 1)]
theorem atom1512Coded_decode : atom1512 = SparsePolynomial.decodeCubic 21 atom1512Coded := by decide +kernel
theorem atom1512Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded) := by
  have h := atom1512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1513 : SparsePolynomial.Poly := [([9,17,20], 1)]
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
def atom1513Coded : CoefficientMerge.Poly := [(4346, 1)]
theorem atom1513Coded_decode : atom1513 = SparsePolynomial.decodeCubic 21 atom1513Coded := by decide +kernel
theorem atom1513Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) := by
  have h := atom1513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1514 : SparsePolynomial.Poly := [([9,18,18], 1)]
theorem eval_atom1514 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1514 = ((g 9) * (g 18) * (g 18)) := by
  norm_num [atom1514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1514_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28394930554200 : Int) atom1514) := by
  rw [SparsePolynomial.eval_scale, eval_atom1514]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 9) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1514Coded : CoefficientMerge.Poly := [(4365, 1)]
theorem atom1514Coded_decode : atom1514 = SparsePolynomial.decodeCubic 21 atom1514Coded := by decide +kernel
theorem atom1514Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) := by
  have h := atom1514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1515 : SparsePolynomial.Poly := [([9,18,19], 1)]
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
def atom1515Coded : CoefficientMerge.Poly := [(4366, 1)]
theorem atom1515Coded_decode : atom1515 = SparsePolynomial.decodeCubic 21 atom1515Coded := by decide +kernel
theorem atom1515Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded) := by
  have h := atom1515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1516 : SparsePolynomial.Poly := [([9,18,20], 1)]
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
def atom1516Coded : CoefficientMerge.Poly := [(4367, 1)]
theorem atom1516Coded_decode : atom1516 = SparsePolynomial.decodeCubic 21 atom1516Coded := by decide +kernel
theorem atom1516Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) := by
  have h := atom1516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1517 : SparsePolynomial.Poly := [([9,19,19], 1)]
theorem eval_atom1517 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1517 = ((g 9) * (g 19) * (g 19)) := by
  norm_num [atom1517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1517_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3308751684000 : Int) atom1517) := by
  rw [SparsePolynomial.eval_scale, eval_atom1517]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 9) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1517Coded : CoefficientMerge.Poly := [(4387, 1)]
theorem atom1517Coded_decode : atom1517 = SparsePolynomial.decodeCubic 21 atom1517Coded := by decide +kernel
theorem atom1517Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded) := by
  have h := atom1517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1518 : SparsePolynomial.Poly := [([9,19,20], 1)]
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
def atom1518Coded : CoefficientMerge.Poly := [(4388, 1)]
theorem atom1518Coded_decode : atom1518 = SparsePolynomial.decodeCubic 21 atom1518Coded := by decide +kernel
theorem atom1518Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) := by
  have h := atom1518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1519 : SparsePolynomial.Poly := [([9,20,20], 1)]
theorem eval_atom1519 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1519 = ((g 9) * (g 20) * (g 20)) := by
  norm_num [atom1519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1519_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8870673060900 : Int) atom1519) := by
  rw [SparsePolynomial.eval_scale, eval_atom1519]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 9) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1519Coded : CoefficientMerge.Poly := [(4409, 1)]
theorem atom1519Coded_decode : atom1519 = SparsePolynomial.decodeCubic 21 atom1519Coded := by decide +kernel
theorem atom1519Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) := by
  have h := atom1519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1520 : SparsePolynomial.Poly := [([10,10,10], 1)]
theorem eval_atom1520 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1520 = ((g 10) * (g 10) * (g 10)) := by
  norm_num [atom1520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1520_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (597600864000 : Int) atom1520) := by
  rw [SparsePolynomial.eval_scale, eval_atom1520]
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 10) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1520Coded : CoefficientMerge.Poly := [(4630, 1)]
theorem atom1520Coded_decode : atom1520 = SparsePolynomial.decodeCubic 21 atom1520Coded := by decide +kernel
theorem atom1520Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded) := by
  have h := atom1520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1521 : SparsePolynomial.Poly := [([10,10,11], 1)]
theorem eval_atom1521 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1521 = ((g 10) * (g 10) * (g 11)) := by
  norm_num [atom1521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1521_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1521) := by
  rw [SparsePolynomial.eval_scale, eval_atom1521]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1521Coded : CoefficientMerge.Poly := [(4631, 1)]
theorem atom1521Coded_decode : atom1521 = SparsePolynomial.decodeCubic 21 atom1521Coded := by decide +kernel
theorem atom1521Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) := by
  have h := atom1521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1522 : SparsePolynomial.Poly := [([10,10,15], 1)]
theorem eval_atom1522 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1522 = ((g 10) * (g 10) * (g 15)) := by
  norm_num [atom1522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1522_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3075590700000 : Int) atom1522) := by
  rw [SparsePolynomial.eval_scale, eval_atom1522]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1522Coded : CoefficientMerge.Poly := [(4635, 1)]
theorem atom1522Coded_decode : atom1522 = SparsePolynomial.decodeCubic 21 atom1522Coded := by decide +kernel
theorem atom1522Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded) := by
  have h := atom1522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1523 : SparsePolynomial.Poly := [([10,10,17], 1)]
theorem eval_atom1523 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1523 = ((g 10) * (g 10) * (g 17)) := by
  norm_num [atom1523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1523_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2234314202400 : Int) atom1523) := by
  rw [SparsePolynomial.eval_scale, eval_atom1523]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1523Coded : CoefficientMerge.Poly := [(4637, 1)]
theorem atom1523Coded_decode : atom1523 = SparsePolynomial.decodeCubic 21 atom1523Coded := by decide +kernel
theorem atom1523Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) := by
  have h := atom1523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1524 : SparsePolynomial.Poly := [([10,11,11], 1)]
theorem eval_atom1524 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1524 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom1524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1524_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (938442758400 : Int) atom1524) := by
  rw [SparsePolynomial.eval_scale, eval_atom1524]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1524Coded : CoefficientMerge.Poly := [(4652, 1)]
theorem atom1524Coded_decode : atom1524 = SparsePolynomial.decodeCubic 21 atom1524Coded := by decide +kernel
theorem atom1524Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) := by
  have h := atom1524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1525 : SparsePolynomial.Poly := [([10,11,13], 1)]
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
def atom1525Coded : CoefficientMerge.Poly := [(4654, 1)]
theorem atom1525Coded_decode : atom1525 = SparsePolynomial.decodeCubic 21 atom1525Coded := by decide +kernel
theorem atom1525Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded) := by
  have h := atom1525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1526 : SparsePolynomial.Poly := [([10,11,14], 1)]
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
def atom1526Coded : CoefficientMerge.Poly := [(4655, 1)]
theorem atom1526Coded_decode : atom1526 = SparsePolynomial.decodeCubic 21 atom1526Coded := by decide +kernel
theorem atom1526Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) := by
  have h := atom1526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1527 : SparsePolynomial.Poly := [([10,11,15], 1)]
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
def atom1527Coded : CoefficientMerge.Poly := [(4656, 1)]
theorem atom1527Coded_decode : atom1527 = SparsePolynomial.decodeCubic 21 atom1527Coded := by decide +kernel
theorem atom1527Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded) := by
  have h := atom1527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1528 : SparsePolynomial.Poly := [([10,11,17], 1)]
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
def atom1528Coded : CoefficientMerge.Poly := [(4658, 1)]
theorem atom1528Coded_decode : atom1528 = SparsePolynomial.decodeCubic 21 atom1528Coded := by decide +kernel
theorem atom1528Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) := by
  have h := atom1528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1529 : SparsePolynomial.Poly := [([10,11,18], 1)]
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
def atom1529Coded : CoefficientMerge.Poly := [(4659, 1)]
theorem atom1529Coded_decode : atom1529 = SparsePolynomial.decodeCubic 21 atom1529Coded := by decide +kernel
theorem atom1529Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) := by
  have h := atom1529_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1529Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1530 : SparsePolynomial.Poly := [([10,11,19], 1)]
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
def atom1530Coded : CoefficientMerge.Poly := [(4660, 1)]
theorem atom1530Coded_decode : atom1530 = SparsePolynomial.decodeCubic 21 atom1530Coded := by decide +kernel
theorem atom1530Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded) := by
  have h := atom1530_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1530Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1531 : SparsePolynomial.Poly := [([10,11,20], 1)]
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
def atom1531Coded : CoefficientMerge.Poly := [(4661, 1)]
theorem atom1531Coded_decode : atom1531 = SparsePolynomial.decodeCubic 21 atom1531Coded := by decide +kernel
theorem atom1531Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) := by
  have h := atom1531_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1531Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1532 : SparsePolynomial.Poly := [([10,12,12], 1)]
theorem eval_atom1532 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1532 = ((g 10) * (g 12) * (g 12)) := by
  norm_num [atom1532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1532_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1365622675200 : Int) atom1532) := by
  rw [SparsePolynomial.eval_scale, eval_atom1532]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1532Coded : CoefficientMerge.Poly := [(4674, 1)]
theorem atom1532Coded_decode : atom1532 = SparsePolynomial.decodeCubic 21 atom1532Coded := by decide +kernel
theorem atom1532Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded) := by
  have h := atom1532_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1532Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1533 : SparsePolynomial.Poly := [([10,12,13], 1)]
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
def atom1533Coded : CoefficientMerge.Poly := [(4675, 1)]
theorem atom1533Coded_decode : atom1533 = SparsePolynomial.decodeCubic 21 atom1533Coded := by decide +kernel
theorem atom1533Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) := by
  have h := atom1533_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1533Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1534 : SparsePolynomial.Poly := [([10,12,14], 1)]
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
def atom1534Coded : CoefficientMerge.Poly := [(4676, 1)]
theorem atom1534Coded_decode : atom1534 = SparsePolynomial.decodeCubic 21 atom1534Coded := by decide +kernel
theorem atom1534Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) := by
  have h := atom1534_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1534Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1535 : SparsePolynomial.Poly := [([10,12,15], 1)]
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
def atom1535Coded : CoefficientMerge.Poly := [(4677, 1)]
theorem atom1535Coded_decode : atom1535 = SparsePolynomial.decodeCubic 21 atom1535Coded := by decide +kernel
theorem atom1535Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded) := by
  have h := atom1535_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1535Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block020 : CoefficientMerge.Poly := [(4175, 182739160800), (4189, 770276908800), (4192, 427179916800), (4193, 854359833600), (4194, 5669444229120), (4196, 6132165580800), (4197, 5786258284800), (4198, 11171238059520), (4199, 17391151612800), (4211, 1533788524800), (4212, 1876885516800), (4213, 2563079500800), (4214, 3249273484800), (4215, 6681901564800), (4216, 1017686224800), (4217, 12075930115200), (4218, 10740378448800), (4219, 20105092879200), (4220, 31025632780800), (4233, 3074342342400), (4234, 6498546969600), (4235, 7275589171200), (4236, 8588646595200), (4237, 6994941380000), (4238, 18707359395200), (4239, 19393808039200), (4240, 29075845864800), (4241, 40801239259200), (4255, 5863944096000), (4256, 11257079040000), (4257, 13909039300800), (4258, 13518234338400), (4259, 29696485795200), (4260, 32840704461600), (4261, 37111606192800), (4262, 55562141678400), (4277, 10101226464000), (4278, 19117589904000), (4279, 19922377860000), (4280, 42879142051200), (4281, 48700483725600), (4282, 49598093109600), (4283, 74906046734400), (4299, 16795322611200), (4300, 35735021557200), (4301, 64884545510400), (4302, 69986611724400), (4303, 53647060446000), (4304, 84256708258800), (4321, 14605687272960), (4322, 55660876311600), (4323, 65795220880200), (4324, 48673825250400), (4325, 66408854078700), (4343, 41744447539200), (4344, 76111510784400), (4345, 52712801442000), (4346, 58566148880400), (4365, 28394930554200), (4366, 36513604071000), (4367, 44758527817500), (4387, 3308751684000), (4388, 15671181626100), (4409, 8870673060900), (4630, 597600864000), (4631, 427179916800), (4635, 3075590700000), (4637, 2234314202400), (4652, 938442758400), (4654, 427179916800), (4655, 854359833600), (4656, 5701373284320), (4658, 10571867661600), (4659, 5786258284800), (4660, 11171238059520), (4661, 17391151612800), (4674, 1365622675200), (4675, 2990259417600), (4676, 3676453401600), (4677, 3338277354720)]
theorem block020_data : block020 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182739160800 : Int) atom1456Coded) (CoefficientMerge.scale (770276908800 : Int) atom1457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1459Coded) (CoefficientMerge.scale (5669444229120 : Int) atom1460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6132165580800 : Int) atom1461Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1464Coded) (CoefficientMerge.scale (1533788524800 : Int) atom1465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1876885516800 : Int) atom1466Coded) (CoefficientMerge.scale (2563079500800 : Int) atom1467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3249273484800 : Int) atom1468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6681901564800 : Int) atom1469Coded) (CoefficientMerge.scale (1017686224800 : Int) atom1470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12075930115200 : Int) atom1471Coded) (CoefficientMerge.scale (10740378448800 : Int) atom1472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20105092879200 : Int) atom1473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31025632780800 : Int) atom1474Coded) (CoefficientMerge.scale (3074342342400 : Int) atom1475Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6498546969600 : Int) atom1476Coded) (CoefficientMerge.scale (7275589171200 : Int) atom1477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8588646595200 : Int) atom1478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6994941380000 : Int) atom1479Coded) (CoefficientMerge.scale (18707359395200 : Int) atom1480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19393808039200 : Int) atom1481Coded) (CoefficientMerge.scale (29075845864800 : Int) atom1482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40801239259200 : Int) atom1483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5863944096000 : Int) atom1484Coded) (CoefficientMerge.scale (11257079040000 : Int) atom1485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13909039300800 : Int) atom1486Coded) (CoefficientMerge.scale (13518234338400 : Int) atom1487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29696485795200 : Int) atom1488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32840704461600 : Int) atom1489Coded) (CoefficientMerge.scale (37111606192800 : Int) atom1490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55562141678400 : Int) atom1491Coded) (CoefficientMerge.scale (10101226464000 : Int) atom1492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19117589904000 : Int) atom1493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19922377860000 : Int) atom1494Coded) (CoefficientMerge.scale (42879142051200 : Int) atom1495Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48700483725600 : Int) atom1496Coded) (CoefficientMerge.scale (49598093109600 : Int) atom1497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74906046734400 : Int) atom1498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16795322611200 : Int) atom1499Coded) (CoefficientMerge.scale (35735021557200 : Int) atom1500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64884545510400 : Int) atom1501Coded) (CoefficientMerge.scale (69986611724400 : Int) atom1502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53647060446000 : Int) atom1503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84256708258800 : Int) atom1504Coded) (CoefficientMerge.scale (14605687272960 : Int) atom1505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55660876311600 : Int) atom1506Coded) (CoefficientMerge.scale (65795220880200 : Int) atom1507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48673825250400 : Int) atom1508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66408854078700 : Int) atom1509Coded) (CoefficientMerge.scale (41744447539200 : Int) atom1510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76111510784400 : Int) atom1511Coded) (CoefficientMerge.scale (52712801442000 : Int) atom1512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58566148880400 : Int) atom1513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28394930554200 : Int) atom1514Coded) (CoefficientMerge.scale (36513604071000 : Int) atom1515Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44758527817500 : Int) atom1516Coded) (CoefficientMerge.scale (3308751684000 : Int) atom1517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15671181626100 : Int) atom1518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8870673060900 : Int) atom1519Coded) (CoefficientMerge.scale (597600864000 : Int) atom1520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1521Coded) (CoefficientMerge.scale (3075590700000 : Int) atom1522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2234314202400 : Int) atom1523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (938442758400 : Int) atom1524Coded) (CoefficientMerge.scale (427179916800 : Int) atom1525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1526Coded) (CoefficientMerge.scale (5701373284320 : Int) atom1527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10571867661600 : Int) atom1528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1529Coded) (CoefficientMerge.scale (11171238059520 : Int) atom1530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17391151612800 : Int) atom1531Coded) (CoefficientMerge.scale (1365622675200 : Int) atom1532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2990259417600 : Int) atom1533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3676453401600 : Int) atom1534Coded) (CoefficientMerge.scale (3338277354720 : Int) atom1535Coded)))))))) := by decide +kernel
theorem block020_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block020 := by
  rw [block020_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1456Coded_nonneg g hg hA hB) (atom1457Coded_nonneg g hg hA hB)) (add_nonneg (atom1458Coded_nonneg g hg hA hB) (add_nonneg (atom1459Coded_nonneg g hg hA hB) (atom1460Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1461Coded_nonneg g hg hA hB) (atom1462Coded_nonneg g hg hA hB)) (add_nonneg (atom1463Coded_nonneg g hg hA hB) (add_nonneg (atom1464Coded_nonneg g hg hA hB) (atom1465Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1466Coded_nonneg g hg hA hB) (atom1467Coded_nonneg g hg hA hB)) (add_nonneg (atom1468Coded_nonneg g hg hA hB) (add_nonneg (atom1469Coded_nonneg g hg hA hB) (atom1470Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1471Coded_nonneg g hg hA hB) (atom1472Coded_nonneg g hg hA hB)) (add_nonneg (atom1473Coded_nonneg g hg hA hB) (add_nonneg (atom1474Coded_nonneg g hg hA hB) (atom1475Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1476Coded_nonneg g hg hA hB) (atom1477Coded_nonneg g hg hA hB)) (add_nonneg (atom1478Coded_nonneg g hg hA hB) (add_nonneg (atom1479Coded_nonneg g hg hA hB) (atom1480Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1481Coded_nonneg g hg hA hB) (atom1482Coded_nonneg g hg hA hB)) (add_nonneg (atom1483Coded_nonneg g hg hA hB) (add_nonneg (atom1484Coded_nonneg g hg hA hB) (atom1485Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1486Coded_nonneg g hg hA hB) (atom1487Coded_nonneg g hg hA hB)) (add_nonneg (atom1488Coded_nonneg g hg hA hB) (add_nonneg (atom1489Coded_nonneg g hg hA hB) (atom1490Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1491Coded_nonneg g hg hA hB) (atom1492Coded_nonneg g hg hA hB)) (add_nonneg (atom1493Coded_nonneg g hg hA hB) (add_nonneg (atom1494Coded_nonneg g hg hA hB) (atom1495Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1496Coded_nonneg g hg hA hB) (atom1497Coded_nonneg g hg hA hB)) (add_nonneg (atom1498Coded_nonneg g hg hA hB) (add_nonneg (atom1499Coded_nonneg g hg hA hB) (atom1500Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1501Coded_nonneg g hg hA hB) (atom1502Coded_nonneg g hg hA hB)) (add_nonneg (atom1503Coded_nonneg g hg hA hB) (add_nonneg (atom1504Coded_nonneg g hg hA hB) (atom1505Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1506Coded_nonneg g hg hA hB) (atom1507Coded_nonneg g hg hA hB)) (add_nonneg (atom1508Coded_nonneg g hg hA hB) (add_nonneg (atom1509Coded_nonneg g hg hA hB) (atom1510Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1511Coded_nonneg g hg hA hB) (atom1512Coded_nonneg g hg hA hB)) (add_nonneg (atom1513Coded_nonneg g hg hA hB) (add_nonneg (atom1514Coded_nonneg g hg hA hB) (atom1515Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1516Coded_nonneg g hg hA hB) (atom1517Coded_nonneg g hg hA hB)) (add_nonneg (atom1518Coded_nonneg g hg hA hB) (add_nonneg (atom1519Coded_nonneg g hg hA hB) (atom1520Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1521Coded_nonneg g hg hA hB) (atom1522Coded_nonneg g hg hA hB)) (add_nonneg (atom1523Coded_nonneg g hg hA hB) (add_nonneg (atom1524Coded_nonneg g hg hA hB) (atom1525Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1526Coded_nonneg g hg hA hB) (atom1527Coded_nonneg g hg hA hB)) (add_nonneg (atom1528Coded_nonneg g hg hA hB) (add_nonneg (atom1529Coded_nonneg g hg hA hB) (atom1530Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1531Coded_nonneg g hg hA hB) (atom1532Coded_nonneg g hg hA hB)) (add_nonneg (atom1533Coded_nonneg g hg hA hB) (add_nonneg (atom1534Coded_nonneg g hg hA hB) (atom1535Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
