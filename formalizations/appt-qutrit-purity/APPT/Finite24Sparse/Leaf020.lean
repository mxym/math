-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1409 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1409 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1409 = ((g 4) * (g 14) * (g 19)) := by
  norm_num [atom1409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1409_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (330838724412000 : Int) atom1409) := by
  rw [SparsePolynomial.eval_scale, eval_atom1409]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1409Coded : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 1))]
theorem atom1409Coded_decode : atom1409 = SparsePolynomial.decodeCubic 24 atom1409Coded := by decide +kernel
theorem atom1409Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) := by
  have h := atom1409_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1409Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1410 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1410 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1410 = ((g 4) * (g 14) * (g 20)) := by
  norm_num [atom1410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1410_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (432262826251200 : Int) atom1410) := by
  rw [SparsePolynomial.eval_scale, eval_atom1410]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1410Coded : CoefficientMerge.Poly := [(nat_lit 2660, Int.ofNat (nat_lit 1))]
theorem atom1410Coded_decode : atom1410 = SparsePolynomial.decodeCubic 24 atom1410Coded := by decide +kernel
theorem atom1410Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded) := by
  have h := atom1410_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1410Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1411 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1411 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1411 = ((g 4) * (g 14) * (g 21)) := by
  norm_num [atom1411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1411_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (416309943672000 : Int) atom1411) := by
  rw [SparsePolynomial.eval_scale, eval_atom1411]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1411Coded : CoefficientMerge.Poly := [(nat_lit 2661, Int.ofNat (nat_lit 1))]
theorem atom1411Coded_decode : atom1411 = SparsePolynomial.decodeCubic 24 atom1411Coded := by decide +kernel
theorem atom1411Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) := by
  have h := atom1411_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1411Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1412 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1412 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1412 = ((g 4) * (g 14) * (g 22)) := by
  norm_num [atom1412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1412_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (457356545604000 : Int) atom1412) := by
  rw [SparsePolynomial.eval_scale, eval_atom1412]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1412Coded : CoefficientMerge.Poly := [(nat_lit 2662, Int.ofNat (nat_lit 1))]
theorem atom1412Coded_decode : atom1412 = SparsePolynomial.decodeCubic 24 atom1412Coded := by decide +kernel
theorem atom1412Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) := by
  have h := atom1412_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1412Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1413 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1413 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1413 = ((g 4) * (g 14) * (g 23)) := by
  norm_num [atom1413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1413_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (510982927610400 : Int) atom1413) := by
  rw [SparsePolynomial.eval_scale, eval_atom1413]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1413Coded : CoefficientMerge.Poly := [(nat_lit 2663, Int.ofNat (nat_lit 1))]
theorem atom1413Coded_decode : atom1413 = SparsePolynomial.decodeCubic 24 atom1413Coded := by decide +kernel
theorem atom1413Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded) := by
  have h := atom1413_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1413Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1414 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1414 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1414 = ((g 4) * (g 15) * (g 15)) := by
  norm_num [atom1414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1414_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208278237081600 : Int) atom1414) := by
  rw [SparsePolynomial.eval_scale, eval_atom1414]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1414Coded : CoefficientMerge.Poly := [(nat_lit 2679, Int.ofNat (nat_lit 1))]
theorem atom1414Coded_decode : atom1414 = SparsePolynomial.decodeCubic 24 atom1414Coded := by decide +kernel
theorem atom1414Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) := by
  have h := atom1414_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1414Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1415 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1415 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1415 = ((g 4) * (g 15) * (g 16)) := by
  norm_num [atom1415, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1415_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (366404392166400 : Int) atom1415) := by
  rw [SparsePolynomial.eval_scale, eval_atom1415]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1415Coded : CoefficientMerge.Poly := [(nat_lit 2680, Int.ofNat (nat_lit 1))]
theorem atom1415Coded_decode : atom1415 = SparsePolynomial.decodeCubic 24 atom1415Coded := by decide +kernel
theorem atom1415Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded) := by
  have h := atom1415_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1415Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1416 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1416 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1416 = ((g 4) * (g 15) * (g 17)) := by
  norm_num [atom1416, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1416_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344185237670400 : Int) atom1416) := by
  rw [SparsePolynomial.eval_scale, eval_atom1416]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1416Coded : CoefficientMerge.Poly := [(nat_lit 2681, Int.ofNat (nat_lit 1))]
theorem atom1416Coded_decode : atom1416 = SparsePolynomial.decodeCubic 24 atom1416Coded := by decide +kernel
theorem atom1416Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) := by
  have h := atom1416_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1416Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1417 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1417 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1417 = ((g 4) * (g 15) * (g 18)) := by
  norm_num [atom1417, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1417_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (380141158118400 : Int) atom1417) := by
  rw [SparsePolynomial.eval_scale, eval_atom1417]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1417Coded : CoefficientMerge.Poly := [(nat_lit 2682, Int.ofNat (nat_lit 1))]
theorem atom1417Coded_decode : atom1417 = SparsePolynomial.decodeCubic 24 atom1417Coded := by decide +kernel
theorem atom1417Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) := by
  have h := atom1417_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1417Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1418 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1418 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1418 = ((g 4) * (g 15) * (g 19)) := by
  norm_num [atom1418, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1418_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (346793499662400 : Int) atom1418) := by
  rw [SparsePolynomial.eval_scale, eval_atom1418]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1418Coded : CoefficientMerge.Poly := [(nat_lit 2683, Int.ofNat (nat_lit 1))]
theorem atom1418Coded_decode : atom1418 = SparsePolynomial.decodeCubic 24 atom1418Coded := by decide +kernel
theorem atom1418Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded) := by
  have h := atom1418_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1418Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1419 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1419 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1419 = ((g 4) * (g 15) * (g 20)) := by
  norm_num [atom1419, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1419_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (472461551755200 : Int) atom1419) := by
  rw [SparsePolynomial.eval_scale, eval_atom1419]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1419Coded : CoefficientMerge.Poly := [(nat_lit 2684, Int.ofNat (nat_lit 1))]
theorem atom1419Coded_decode : atom1419 = SparsePolynomial.decodeCubic 24 atom1419Coded := by decide +kernel
theorem atom1419Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) := by
  have h := atom1419_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1419Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1420 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1420 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1420 = ((g 4) * (g 15) * (g 21)) := by
  norm_num [atom1420, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1420_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (461611632888000 : Int) atom1420) := by
  rw [SparsePolynomial.eval_scale, eval_atom1420]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1420Coded : CoefficientMerge.Poly := [(nat_lit 2685, Int.ofNat (nat_lit 1))]
theorem atom1420Coded_decode : atom1420 = SparsePolynomial.decodeCubic 24 atom1420Coded := by decide +kernel
theorem atom1420Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded) := by
  have h := atom1420_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1420Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1421 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1421 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1421 = ((g 4) * (g 15) * (g 22)) := by
  norm_num [atom1421, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1421_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (436957939454400 : Int) atom1421) := by
  rw [SparsePolynomial.eval_scale, eval_atom1421]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1421Coded : CoefficientMerge.Poly := [(nat_lit 2686, Int.ofNat (nat_lit 1))]
theorem atom1421Coded_decode : atom1421 = SparsePolynomial.decodeCubic 24 atom1421Coded := by decide +kernel
theorem atom1421Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) := by
  have h := atom1421_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1421Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1422 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1422 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1422 = ((g 4) * (g 15) * (g 23)) := by
  norm_num [atom1422, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1422_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (482678754667200 : Int) atom1422) := by
  rw [SparsePolynomial.eval_scale, eval_atom1422]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1422Coded : CoefficientMerge.Poly := [(nat_lit 2687, Int.ofNat (nat_lit 1))]
theorem atom1422Coded_decode : atom1422 = SparsePolynomial.decodeCubic 24 atom1422Coded := by decide +kernel
theorem atom1422Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) := by
  have h := atom1422_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1422Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1423 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1423 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1423 = ((g 4) * (g 16) * (g 16)) := by
  norm_num [atom1423, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1423_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (205392356467200 : Int) atom1423) := by
  rw [SparsePolynomial.eval_scale, eval_atom1423]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1423Coded : CoefficientMerge.Poly := [(nat_lit 2704, Int.ofNat (nat_lit 1))]
theorem atom1423Coded_decode : atom1423 = SparsePolynomial.decodeCubic 24 atom1423Coded := by decide +kernel
theorem atom1423Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded) := by
  have h := atom1423_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1423Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1424 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1424 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1424 = ((g 4) * (g 16) * (g 17)) := by
  norm_num [atom1424, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1424_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (377339038272000 : Int) atom1424) := by
  rw [SparsePolynomial.eval_scale, eval_atom1424]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1424Coded : CoefficientMerge.Poly := [(nat_lit 2705, Int.ofNat (nat_lit 1))]
theorem atom1424Coded_decode : atom1424 = SparsePolynomial.decodeCubic 24 atom1424Coded := by decide +kernel
theorem atom1424Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) := by
  have h := atom1424_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1424Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1425 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1425 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1425 = ((g 4) * (g 16) * (g 18)) := by
  norm_num [atom1425, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1425_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (386488935705600 : Int) atom1425) := by
  rw [SparsePolynomial.eval_scale, eval_atom1425]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1425Coded : CoefficientMerge.Poly := [(nat_lit 2706, Int.ofNat (nat_lit 1))]
theorem atom1425Coded_decode : atom1425 = SparsePolynomial.decodeCubic 24 atom1425Coded := by decide +kernel
theorem atom1425Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded) := by
  have h := atom1425_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1425Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1426 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1426 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1426 = ((g 4) * (g 16) * (g 19)) := by
  norm_num [atom1426, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1426_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (358244240961600 : Int) atom1426) := by
  rw [SparsePolynomial.eval_scale, eval_atom1426]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1426Coded : CoefficientMerge.Poly := [(nat_lit 2707, Int.ofNat (nat_lit 1))]
theorem atom1426Coded_decode : atom1426 = SparsePolynomial.decodeCubic 24 atom1426Coded := by decide +kernel
theorem atom1426Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) := by
  have h := atom1426_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1426Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1427 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1427 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1427 = ((g 4) * (g 16) * (g 20)) := by
  norm_num [atom1427, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1427_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (489015256766400 : Int) atom1427) := by
  rw [SparsePolynomial.eval_scale, eval_atom1427]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1427Coded : CoefficientMerge.Poly := [(nat_lit 2708, Int.ofNat (nat_lit 1))]
theorem atom1427Coded_decode : atom1427 = SparsePolynomial.decodeCubic 24 atom1427Coded := by decide +kernel
theorem atom1427Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) := by
  have h := atom1427_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1427Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1428 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1428 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1428 = ((g 4) * (g 16) * (g 21)) := by
  norm_num [atom1428, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1428_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (483268301611200 : Int) atom1428) := by
  rw [SparsePolynomial.eval_scale, eval_atom1428]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1428Coded : CoefficientMerge.Poly := [(nat_lit 2709, Int.ofNat (nat_lit 1))]
theorem atom1428Coded_decode : atom1428 = SparsePolynomial.decodeCubic 24 atom1428Coded := by decide +kernel
theorem atom1428Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded) := by
  have h := atom1428_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1428Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1429 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1429 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1429 = ((g 4) * (g 16) * (g 22)) := by
  norm_num [atom1429, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1429_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (405924574910400 : Int) atom1429) := by
  rw [SparsePolynomial.eval_scale, eval_atom1429]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1429Coded : CoefficientMerge.Poly := [(nat_lit 2710, Int.ofNat (nat_lit 1))]
theorem atom1429Coded_decode : atom1429 = SparsePolynomial.decodeCubic 24 atom1429Coded := by decide +kernel
theorem atom1429Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) := by
  have h := atom1429_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1429Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1430 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1430 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1430 = ((g 4) * (g 16) * (g 23)) := by
  norm_num [atom1430, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1430_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (533283144811200 : Int) atom1430) := by
  rw [SparsePolynomial.eval_scale, eval_atom1430]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1430Coded : CoefficientMerge.Poly := [(nat_lit 2711, Int.ofNat (nat_lit 1))]
theorem atom1430Coded_decode : atom1430 = SparsePolynomial.decodeCubic 24 atom1430Coded := by decide +kernel
theorem atom1430Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded) := by
  have h := atom1430_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1430Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1431 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1431 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1431 = ((g 4) * (g 17) * (g 17)) := by
  norm_num [atom1431, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1431_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (214421767257600 : Int) atom1431) := by
  rw [SparsePolynomial.eval_scale, eval_atom1431]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1431Coded : CoefficientMerge.Poly := [(nat_lit 2729, Int.ofNat (nat_lit 1))]
theorem atom1431Coded_decode : atom1431 = SparsePolynomial.decodeCubic 24 atom1431Coded := by decide +kernel
theorem atom1431Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) := by
  have h := atom1431_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1431Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1432 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1432 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1432 = ((g 4) * (g 17) * (g 18)) := by
  norm_num [atom1432, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1432_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415025907206400 : Int) atom1432) := by
  rw [SparsePolynomial.eval_scale, eval_atom1432]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1432Coded : CoefficientMerge.Poly := [(nat_lit 2730, Int.ofNat (nat_lit 1))]
theorem atom1432Coded_decode : atom1432 = SparsePolynomial.decodeCubic 24 atom1432Coded := by decide +kernel
theorem atom1432Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) := by
  have h := atom1432_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1432Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1433 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1433 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1433 = ((g 4) * (g 17) * (g 19)) := by
  norm_num [atom1433, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1433_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (389560459176000 : Int) atom1433) := by
  rw [SparsePolynomial.eval_scale, eval_atom1433]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1433Coded : CoefficientMerge.Poly := [(nat_lit 2731, Int.ofNat (nat_lit 1))]
theorem atom1433Coded_decode : atom1433 = SparsePolynomial.decodeCubic 24 atom1433Coded := by decide +kernel
theorem atom1433Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded) := by
  have h := atom1433_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1433Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1434 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1434 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1434 = ((g 4) * (g 17) * (g 20)) := by
  norm_num [atom1434, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1434_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (523110721694400 : Int) atom1434) := by
  rw [SparsePolynomial.eval_scale, eval_atom1434]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1434Coded : CoefficientMerge.Poly := [(nat_lit 2732, Int.ofNat (nat_lit 1))]
theorem atom1434Coded_decode : atom1434 = SparsePolynomial.decodeCubic 24 atom1434Coded := by decide +kernel
theorem atom1434Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) := by
  have h := atom1434_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1434Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1435 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1435 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1435 = ((g 4) * (g 17) * (g 21)) := by
  norm_num [atom1435, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1435_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (521304871752000 : Int) atom1435) := by
  rw [SparsePolynomial.eval_scale, eval_atom1435]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1435Coded : CoefficientMerge.Poly := [(nat_lit 2733, Int.ofNat (nat_lit 1))]
theorem atom1435Coded_decode : atom1435 = SparsePolynomial.decodeCubic 24 atom1435Coded := by decide +kernel
theorem atom1435Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded) := by
  have h := atom1435_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1435Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1436 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1436 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1436 = ((g 4) * (g 17) * (g 22)) := by
  norm_num [atom1436, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1436_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (446778567345600 : Int) atom1436) := by
  rw [SparsePolynomial.eval_scale, eval_atom1436]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1436Coded : CoefficientMerge.Poly := [(nat_lit 2734, Int.ofNat (nat_lit 1))]
theorem atom1436Coded_decode : atom1436 = SparsePolynomial.decodeCubic 24 atom1436Coded := by decide +kernel
theorem atom1436Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) := by
  have h := atom1436_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1436Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1437 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1437 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1437 = ((g 4) * (g 17) * (g 23)) := by
  norm_num [atom1437, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1437_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (578659171708800 : Int) atom1437) := by
  rw [SparsePolynomial.eval_scale, eval_atom1437]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1437Coded : CoefficientMerge.Poly := [(nat_lit 2735, Int.ofNat (nat_lit 1))]
theorem atom1437Coded_decode : atom1437 = SparsePolynomial.decodeCubic 24 atom1437Coded := by decide +kernel
theorem atom1437Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) := by
  have h := atom1437_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1437Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1438 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1438 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1438 = ((g 4) * (g 18) * (g 18)) := by
  norm_num [atom1438, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1438_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (249088416192000 : Int) atom1438) := by
  rw [SparsePolynomial.eval_scale, eval_atom1438]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1438Coded : CoefficientMerge.Poly := [(nat_lit 2754, Int.ofNat (nat_lit 1))]
theorem atom1438Coded_decode : atom1438 = SparsePolynomial.decodeCubic 24 atom1438Coded := by decide +kernel
theorem atom1438Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded) := by
  have h := atom1438_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1438Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1439 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1439 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1439 = ((g 4) * (g 18) * (g 19)) := by
  norm_num [atom1439, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1439_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (449248020026400 : Int) atom1439) := by
  rw [SparsePolynomial.eval_scale, eval_atom1439]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1439Coded : CoefficientMerge.Poly := [(nat_lit 2755, Int.ofNat (nat_lit 1))]
theorem atom1439Coded_decode : atom1439 = SparsePolynomial.decodeCubic 24 atom1439Coded := by decide +kernel
theorem atom1439Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) := by
  have h := atom1439_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1439Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1440 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1440 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1440 = ((g 4) * (g 18) * (g 20)) := by
  norm_num [atom1440, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1440_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (620668861394400 : Int) atom1440) := by
  rw [SparsePolynomial.eval_scale, eval_atom1440]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1440Coded : CoefficientMerge.Poly := [(nat_lit 2756, Int.ofNat (nat_lit 1))]
theorem atom1440Coded_decode : atom1440 = SparsePolynomial.decodeCubic 24 atom1440Coded := by decide +kernel
theorem atom1440Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded) := by
  have h := atom1440_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1440Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1441 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1441 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1441 = ((g 4) * (g 18) * (g 21)) := by
  norm_num [atom1441, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1441_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (582988918831200 : Int) atom1441) := by
  rw [SparsePolynomial.eval_scale, eval_atom1441]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1441Coded : CoefficientMerge.Poly := [(nat_lit 2757, Int.ofNat (nat_lit 1))]
theorem atom1441Coded_decode : atom1441 = SparsePolynomial.decodeCubic 24 atom1441Coded := by decide +kernel
theorem atom1441Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) := by
  have h := atom1441_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1441Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1442 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1442 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1442 = ((g 4) * (g 18) * (g 22)) := by
  norm_num [atom1442, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1442_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (416071587909600 : Int) atom1442) := by
  rw [SparsePolynomial.eval_scale, eval_atom1442]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1442Coded : CoefficientMerge.Poly := [(nat_lit 2758, Int.ofNat (nat_lit 1))]
theorem atom1442Coded_decode : atom1442 = SparsePolynomial.decodeCubic 24 atom1442Coded := by decide +kernel
theorem atom1442Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) := by
  have h := atom1442_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1442Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1443 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1443 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1443 = ((g 4) * (g 18) * (g 23)) := by
  norm_num [atom1443, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1443_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (578049932930400 : Int) atom1443) := by
  rw [SparsePolynomial.eval_scale, eval_atom1443]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1443Coded : CoefficientMerge.Poly := [(nat_lit 2759, Int.ofNat (nat_lit 1))]
theorem atom1443Coded_decode : atom1443 = SparsePolynomial.decodeCubic 24 atom1443Coded := by decide +kernel
theorem atom1443Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded) := by
  have h := atom1443_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1443Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1444 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1444 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1444 = ((g 4) * (g 19) * (g 19)) := by
  norm_num [atom1444, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1444_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163652046243840 : Int) atom1444) := by
  rw [SparsePolynomial.eval_scale, eval_atom1444]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1444Coded : CoefficientMerge.Poly := [(nat_lit 2779, Int.ofNat (nat_lit 1))]
theorem atom1444Coded_decode : atom1444 = SparsePolynomial.decodeCubic 24 atom1444Coded := by decide +kernel
theorem atom1444Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) := by
  have h := atom1444_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1444Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1445 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1445 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1445 = ((g 4) * (g 19) * (g 20)) := by
  norm_num [atom1445, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1445_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (483786370015200 : Int) atom1445) := by
  rw [SparsePolynomial.eval_scale, eval_atom1445]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1445Coded : CoefficientMerge.Poly := [(nat_lit 2780, Int.ofNat (nat_lit 1))]
theorem atom1445Coded_decode : atom1445 = SparsePolynomial.decodeCubic 24 atom1445Coded := by decide +kernel
theorem atom1445Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded) := by
  have h := atom1445_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1445Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1446 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1446 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1446 = ((g 4) * (g 19) * (g 21)) := by
  norm_num [atom1446, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1446_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (464046353038800 : Int) atom1446) := by
  rw [SparsePolynomial.eval_scale, eval_atom1446]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1446Coded : CoefficientMerge.Poly := [(nat_lit 2781, Int.ofNat (nat_lit 1))]
theorem atom1446Coded_decode : atom1446 = SparsePolynomial.decodeCubic 24 atom1446Coded := by decide +kernel
theorem atom1446Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) := by
  have h := atom1446_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1446Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1447 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1447 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1447 = ((g 4) * (g 19) * (g 22)) := by
  norm_num [atom1447, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1447_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (352564509192000 : Int) atom1447) := by
  rw [SparsePolynomial.eval_scale, eval_atom1447]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1447Coded : CoefficientMerge.Poly := [(nat_lit 2782, Int.ofNat (nat_lit 1))]
theorem atom1447Coded_decode : atom1447 = SparsePolynomial.decodeCubic 24 atom1447Coded := by decide +kernel
theorem atom1447Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) := by
  have h := atom1447_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1447Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1448 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1448 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1448 = ((g 4) * (g 19) * (g 23)) := by
  norm_num [atom1448, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1448_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (361867931119800 : Int) atom1448) := by
  rw [SparsePolynomial.eval_scale, eval_atom1448]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1448Coded : CoefficientMerge.Poly := [(nat_lit 2783, Int.ofNat (nat_lit 1))]
theorem atom1448Coded_decode : atom1448 = SparsePolynomial.decodeCubic 24 atom1448Coded := by decide +kernel
theorem atom1448Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded) := by
  have h := atom1448_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1448Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1449 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1449 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1449 = ((g 4) * (g 20) * (g 20)) := by
  norm_num [atom1449, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1449_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344960709357600 : Int) atom1449) := by
  rw [SparsePolynomial.eval_scale, eval_atom1449]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1449Coded : CoefficientMerge.Poly := [(nat_lit 2804, Int.ofNat (nat_lit 1))]
theorem atom1449Coded_decode : atom1449 = SparsePolynomial.decodeCubic 24 atom1449Coded := by decide +kernel
theorem atom1449Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) := by
  have h := atom1449_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1449Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1450 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1450 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1450 = ((g 4) * (g 20) * (g 21)) := by
  norm_num [atom1450, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1450_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (507525601237200 : Int) atom1450) := by
  rw [SparsePolynomial.eval_scale, eval_atom1450]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1450Coded : CoefficientMerge.Poly := [(nat_lit 2805, Int.ofNat (nat_lit 1))]
theorem atom1450Coded_decode : atom1450 = SparsePolynomial.decodeCubic 24 atom1450Coded := by decide +kernel
theorem atom1450Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded) := by
  have h := atom1450_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1450Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1451 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1451 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1451 = ((g 4) * (g 20) * (g 22)) := by
  norm_num [atom1451, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1451_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (377976761080800 : Int) atom1451) := by
  rw [SparsePolynomial.eval_scale, eval_atom1451]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1451Coded : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 1))]
theorem atom1451Coded_decode : atom1451 = SparsePolynomial.decodeCubic 24 atom1451Coded := by decide +kernel
theorem atom1451Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) := by
  have h := atom1451_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1451Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1452 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1452 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1452 = ((g 4) * (g 20) * (g 23)) := by
  norm_num [atom1452, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1452_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (424529099908200 : Int) atom1452) := by
  rw [SparsePolynomial.eval_scale, eval_atom1452]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1452Coded : CoefficientMerge.Poly := [(nat_lit 2807, Int.ofNat (nat_lit 1))]
theorem atom1452Coded_decode : atom1452 = SparsePolynomial.decodeCubic 24 atom1452Coded := by decide +kernel
theorem atom1452Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) := by
  have h := atom1452_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1452Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1453 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1453 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1453 = ((g 4) * (g 21) * (g 21)) := by
  norm_num [atom1453, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1453_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126080231583600 : Int) atom1453) := by
  rw [SparsePolynomial.eval_scale, eval_atom1453]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1453Coded : CoefficientMerge.Poly := [(nat_lit 2829, Int.ofNat (nat_lit 1))]
theorem atom1453Coded_decode : atom1453 = SparsePolynomial.decodeCubic 24 atom1453Coded := by decide +kernel
theorem atom1453Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded) := by
  have h := atom1453_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1453Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1454 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1454 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1454 = ((g 4) * (g 21) * (g 22)) := by
  norm_num [atom1454, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1454_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (174744351860400 : Int) atom1454) := by
  rw [SparsePolynomial.eval_scale, eval_atom1454]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1454Coded : CoefficientMerge.Poly := [(nat_lit 2830, Int.ofNat (nat_lit 1))]
theorem atom1454Coded_decode : atom1454 = SparsePolynomial.decodeCubic 24 atom1454Coded := by decide +kernel
theorem atom1454Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) := by
  have h := atom1454_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1454Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1455 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1455 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1455 = ((g 4) * (g 21) * (g 23)) := by
  norm_num [atom1455, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1455_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (211258137144600 : Int) atom1455) := by
  rw [SparsePolynomial.eval_scale, eval_atom1455]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1455Coded : CoefficientMerge.Poly := [(nat_lit 2831, Int.ofNat (nat_lit 1))]
theorem atom1455Coded_decode : atom1455 = SparsePolynomial.decodeCubic 24 atom1455Coded := by decide +kernel
theorem atom1455Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded) := by
  have h := atom1455_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1455Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1456 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1456 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1456 = ((g 4) * (g 22) * (g 23)) := by
  norm_num [atom1456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1456_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6690481950600 : Int) atom1456) := by
  rw [SparsePolynomial.eval_scale, eval_atom1456]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1456Coded : CoefficientMerge.Poly := [(nat_lit 2855, Int.ofNat (nat_lit 1))]
theorem atom1456Coded_decode : atom1456 = SparsePolynomial.decodeCubic 24 atom1456Coded := by decide +kernel
theorem atom1456Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) := by
  have h := atom1456_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1456Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1457 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 23, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1457 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1457 = ((g 4) * (g 23) * (g 23)) := by
  norm_num [atom1457, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1457_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49057765684200 : Int) atom1457) := by
  rw [SparsePolynomial.eval_scale, eval_atom1457]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1457Coded : CoefficientMerge.Poly := [(nat_lit 2879, Int.ofNat (nat_lit 1))]
theorem atom1457Coded_decode : atom1457 = SparsePolynomial.decodeCubic 24 atom1457Coded := by decide +kernel
theorem atom1457Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) := by
  have h := atom1457_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1457Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1458 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom1458 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1458 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom1458, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1458_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19631255212800 : Int) atom1458) := by
  rw [SparsePolynomial.eval_scale, eval_atom1458]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1458Coded : CoefficientMerge.Poly := [(nat_lit 3005, Int.ofNat (nat_lit 1))]
theorem atom1458Coded_decode : atom1458 = SparsePolynomial.decodeCubic 24 atom1458Coded := by decide +kernel
theorem atom1458Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded) := by
  have h := atom1458_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1458Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1459 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom1459 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1459 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom1459, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1459_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31325586960096 : Int) atom1459) := by
  rw [SparsePolynomial.eval_scale, eval_atom1459]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1459Coded : CoefficientMerge.Poly := [(nat_lit 3006, Int.ofNat (nat_lit 1))]
theorem atom1459Coded_decode : atom1459 = SparsePolynomial.decodeCubic 24 atom1459Coded := by decide +kernel
theorem atom1459Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) := by
  have h := atom1459_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1459Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1460 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1460 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1460 = ((g 5) * (g 5) * (g 7)) := by
  norm_num [atom1460, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1460_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6649449936096 : Int) atom1460) := by
  rw [SparsePolynomial.eval_scale, eval_atom1460]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1460Coded : CoefficientMerge.Poly := [(nat_lit 3007, Int.ofNat (nat_lit 1))]
theorem atom1460Coded_decode : atom1460 = SparsePolynomial.decodeCubic 24 atom1460Coded := by decide +kernel
theorem atom1460Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded) := by
  have h := atom1460_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1460Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1461 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1461 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1461 = ((g 5) * (g 5) * (g 8)) := by
  norm_num [atom1461, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1461_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6533608444704 : Int) atom1461) := by
  rw [SparsePolynomial.eval_scale, eval_atom1461]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1461Coded : CoefficientMerge.Poly := [(nat_lit 3008, Int.ofNat (nat_lit 1))]
theorem atom1461Coded_decode : atom1461 = SparsePolynomial.decodeCubic 24 atom1461Coded := by decide +kernel
theorem atom1461Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) := by
  have h := atom1461_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1461Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1462 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1462 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1462 = ((g 5) * (g 5) * (g 9)) := by
  norm_num [atom1462, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1462_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5725639190304 : Int) atom1462) := by
  rw [SparsePolynomial.eval_scale, eval_atom1462]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1462Coded : CoefficientMerge.Poly := [(nat_lit 3009, Int.ofNat (nat_lit 1))]
theorem atom1462Coded_decode : atom1462 = SparsePolynomial.decodeCubic 24 atom1462Coded := by decide +kernel
theorem atom1462Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) := by
  have h := atom1462_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1462Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1463 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1463 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1463 = ((g 5) * (g 5) * (g 11)) := by
  norm_num [atom1463, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1463_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2642598614304 : Int) atom1463) := by
  rw [SparsePolynomial.eval_scale, eval_atom1463]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1463Coded : CoefficientMerge.Poly := [(nat_lit 3011, Int.ofNat (nat_lit 1))]
theorem atom1463Coded_decode : atom1463 = SparsePolynomial.decodeCubic 24 atom1463Coded := by decide +kernel
theorem atom1463Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded) := by
  have h := atom1463_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1463Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1464 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1464 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1464 = ((g 5) * (g 5) * (g 12)) := by
  norm_num [atom1464, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1464_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27375228517824 : Int) atom1464) := by
  rw [SparsePolynomial.eval_scale, eval_atom1464]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1464Coded : CoefficientMerge.Poly := [(nat_lit 3012, Int.ofNat (nat_lit 1))]
theorem atom1464Coded_decode : atom1464 = SparsePolynomial.decodeCubic 24 atom1464Coded := by decide +kernel
theorem atom1464Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) := by
  have h := atom1464_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1464Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1465 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1465 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1465 = ((g 5) * (g 5) * (g 13)) := by
  norm_num [atom1465, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1465_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15524745667200 : Int) atom1465) := by
  rw [SparsePolynomial.eval_scale, eval_atom1465]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1465Coded : CoefficientMerge.Poly := [(nat_lit 3013, Int.ofNat (nat_lit 1))]
theorem atom1465Coded_decode : atom1465 = SparsePolynomial.decodeCubic 24 atom1465Coded := by decide +kernel
theorem atom1465Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded) := by
  have h := atom1465_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1465Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1466 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1466 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1466 = ((g 5) * (g 5) * (g 18)) := by
  norm_num [atom1466, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1466_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6709402022400 : Int) atom1466) := by
  rw [SparsePolynomial.eval_scale, eval_atom1466]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1466Coded : CoefficientMerge.Poly := [(nat_lit 3018, Int.ofNat (nat_lit 1))]
theorem atom1466Coded_decode : atom1466 = SparsePolynomial.decodeCubic 24 atom1466Coded := by decide +kernel
theorem atom1466Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) := by
  have h := atom1466_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1466Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1467 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom1467 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1467 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom1467, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1467_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34147372080096 : Int) atom1467) := by
  rw [SparsePolynomial.eval_scale, eval_atom1467]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1467Coded : CoefficientMerge.Poly := [(nat_lit 3030, Int.ofNat (nat_lit 1))]
theorem atom1467Coded_decode : atom1467 = SparsePolynomial.decodeCubic 24 atom1467Coded := by decide +kernel
theorem atom1467Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) := by
  have h := atom1467_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1467Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1468 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1468 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1468 = ((g 5) * (g 6) * (g 7)) := by
  norm_num [atom1468, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1468_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18942470112192 : Int) atom1468) := by
  rw [SparsePolynomial.eval_scale, eval_atom1468]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1468Coded : CoefficientMerge.Poly := [(nat_lit 3031, Int.ofNat (nat_lit 1))]
theorem atom1468Coded_decode : atom1468 = SparsePolynomial.decodeCubic 24 atom1468Coded := by decide +kernel
theorem atom1468Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded) := by
  have h := atom1468_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1468Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1469 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1469 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1469 = ((g 5) * (g 6) * (g 12)) := by
  norm_num [atom1469, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1469_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25753222645920 : Int) atom1469) := by
  rw [SparsePolynomial.eval_scale, eval_atom1469]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1469Coded : CoefficientMerge.Poly := [(nat_lit 3036, Int.ofNat (nat_lit 1))]
theorem atom1469Coded_decode : atom1469 = SparsePolynomial.decodeCubic 24 atom1469Coded := by decide +kernel
theorem atom1469Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) := by
  have h := atom1469_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1469Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1470 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1470 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1470 = ((g 5) * (g 6) * (g 13)) := by
  norm_num [atom1470, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1470_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16985780371296 : Int) atom1470) := by
  rw [SparsePolynomial.eval_scale, eval_atom1470]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1470Coded : CoefficientMerge.Poly := [(nat_lit 3037, Int.ofNat (nat_lit 1))]
theorem atom1470Coded_decode : atom1470 = SparsePolynomial.decodeCubic 24 atom1470Coded := by decide +kernel
theorem atom1470Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded) := by
  have h := atom1470_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1470Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1471 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1471 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1471 = ((g 5) * (g 6) * (g 14)) := by
  norm_num [atom1471, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1471_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4544075280096 : Int) atom1471) := by
  rw [SparsePolynomial.eval_scale, eval_atom1471]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1471Coded : CoefficientMerge.Poly := [(nat_lit 3038, Int.ofNat (nat_lit 1))]
theorem atom1471Coded_decode : atom1471 = SparsePolynomial.decodeCubic 24 atom1471Coded := by decide +kernel
theorem atom1471Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) := by
  have h := atom1471_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1471Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1472 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1472 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1472 = ((g 5) * (g 6) * (g 15)) := by
  norm_num [atom1472, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1472_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7627115856096 : Int) atom1472) := by
  rw [SparsePolynomial.eval_scale, eval_atom1472]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1472Coded : CoefficientMerge.Poly := [(nat_lit 3039, Int.ofNat (nat_lit 1))]
theorem atom1472Coded_decode : atom1472 = SparsePolynomial.decodeCubic 24 atom1472Coded := by decide +kernel
theorem atom1472Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) := by
  have h := atom1472_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1472Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1473 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1473 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1473 = ((g 5) * (g 6) * (g 16)) := by
  norm_num [atom1473, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1473_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10710156432096 : Int) atom1473) := by
  rw [SparsePolynomial.eval_scale, eval_atom1473]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1473Coded : CoefficientMerge.Poly := [(nat_lit 3040, Int.ofNat (nat_lit 1))]
theorem atom1473Coded_decode : atom1473 = SparsePolynomial.decodeCubic 24 atom1473Coded := by decide +kernel
theorem atom1473Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded) := by
  have h := atom1473_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1473Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1474 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1474 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1474 = ((g 5) * (g 6) * (g 17)) := by
  norm_num [atom1474, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1474_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13793197008096 : Int) atom1474) := by
  rw [SparsePolynomial.eval_scale, eval_atom1474]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1474Coded : CoefficientMerge.Poly := [(nat_lit 3041, Int.ofNat (nat_lit 1))]
theorem atom1474Coded_decode : atom1474 = SparsePolynomial.decodeCubic 24 atom1474Coded := by decide +kernel
theorem atom1474Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) := by
  have h := atom1474_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1474Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1475 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1475 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1475 = ((g 5) * (g 6) * (g 18)) := by
  norm_num [atom1475, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1475_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10047950030448 : Int) atom1475) := by
  rw [SparsePolynomial.eval_scale, eval_atom1475]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1475Coded : CoefficientMerge.Poly := [(nat_lit 3042, Int.ofNat (nat_lit 1))]
theorem atom1475Coded_decode : atom1475 = SparsePolynomial.decodeCubic 24 atom1475Coded := by decide +kernel
theorem atom1475Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded) := by
  have h := atom1475_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1475Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1476 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1476 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1476 = ((g 5) * (g 6) * (g 19)) := by
  norm_num [atom1476, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1476_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5544496742400 : Int) atom1476) := by
  rw [SparsePolynomial.eval_scale, eval_atom1476]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1476Coded : CoefficientMerge.Poly := [(nat_lit 3043, Int.ofNat (nat_lit 1))]
theorem atom1476Coded_decode : atom1476 = SparsePolynomial.decodeCubic 24 atom1476Coded := by decide +kernel
theorem atom1476Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) := by
  have h := atom1476_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1476Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1477 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1477 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1477 = ((g 5) * (g 6) * (g 20)) := by
  norm_num [atom1477, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1477_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7750445476752 : Int) atom1477) := by
  rw [SparsePolynomial.eval_scale, eval_atom1477]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1477Coded : CoefficientMerge.Poly := [(nat_lit 3044, Int.ofNat (nat_lit 1))]
theorem atom1477Coded_decode : atom1477 = SparsePolynomial.decodeCubic 24 atom1477Coded := by decide +kernel
theorem atom1477Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) := by
  have h := atom1477_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1477Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1478 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1478 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1478 = ((g 5) * (g 6) * (g 21)) := by
  norm_num [atom1478, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1478_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48376733335128 : Int) atom1478) := by
  rw [SparsePolynomial.eval_scale, eval_atom1478]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 5) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1478Coded : CoefficientMerge.Poly := [(nat_lit 3045, Int.ofNat (nat_lit 1))]
theorem atom1478Coded_decode : atom1478 = SparsePolynomial.decodeCubic 24 atom1478Coded := by decide +kernel
theorem atom1478Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded) := by
  have h := atom1478_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1478Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1479 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1479 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1479 = ((g 5) * (g 6) * (g 22)) := by
  norm_num [atom1479, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1479_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89003021193504 : Int) atom1479) := by
  rw [SparsePolynomial.eval_scale, eval_atom1479]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 5) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1479Coded : CoefficientMerge.Poly := [(nat_lit 3046, Int.ofNat (nat_lit 1))]
theorem atom1479Coded_decode : atom1479 = SparsePolynomial.decodeCubic 24 atom1479Coded := by decide +kernel
theorem atom1479Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) := by
  have h := atom1479_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1479Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1480 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1480 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1480 = ((g 5) * (g 6) * (g 23)) := by
  norm_num [atom1480, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1480_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136178880879492 : Int) atom1480) := by
  rw [SparsePolynomial.eval_scale, eval_atom1480]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 5) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1480Coded : CoefficientMerge.Poly := [(nat_lit 3047, Int.ofNat (nat_lit 1))]
theorem atom1480Coded_decode : atom1480 = SparsePolynomial.decodeCubic 24 atom1480Coded := by decide +kernel
theorem atom1480Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded) := by
  have h := atom1480_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1480Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1481 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1481 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1481 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom1481, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1481_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12542463216096 : Int) atom1481) := by
  rw [SparsePolynomial.eval_scale, eval_atom1481]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1481Coded : CoefficientMerge.Poly := [(nat_lit 3055, Int.ofNat (nat_lit 1))]
theorem atom1481Coded_decode : atom1481 = SparsePolynomial.decodeCubic 24 atom1481Coded := by decide +kernel
theorem atom1481Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) := by
  have h := atom1481_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1481Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1482 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1482 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1482 = ((g 5) * (g 7) * (g 8)) := by
  norm_num [atom1482, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1482_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14392247654400 : Int) atom1482) := by
  rw [SparsePolynomial.eval_scale, eval_atom1482]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1482Coded : CoefficientMerge.Poly := [(nat_lit 3056, Int.ofNat (nat_lit 1))]
theorem atom1482Coded_decode : atom1482 = SparsePolynomial.decodeCubic 24 atom1482Coded := by decide +kernel
theorem atom1482Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) := by
  have h := atom1482_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1482Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1483 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1483 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1483 = ((g 5) * (g 7) * (g 11)) := by
  norm_num [atom1483, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1483_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4124895667200 : Int) atom1483) := by
  rw [SparsePolynomial.eval_scale, eval_atom1483]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1483Coded : CoefficientMerge.Poly := [(nat_lit 3059, Int.ofNat (nat_lit 1))]
theorem atom1483Coded_decode : atom1483 = SparsePolynomial.decodeCubic 24 atom1483Coded := by decide +kernel
theorem atom1483Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded) := by
  have h := atom1483_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1483Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1484 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1484 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1484 = ((g 5) * (g 7) * (g 12)) := by
  norm_num [atom1484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1484_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34003013980320 : Int) atom1484) := by
  rw [SparsePolynomial.eval_scale, eval_atom1484]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1484Coded : CoefficientMerge.Poly := [(nat_lit 3060, Int.ofNat (nat_lit 1))]
theorem atom1484Coded_decode : atom1484 = SparsePolynomial.decodeCubic 24 atom1484Coded := by decide +kernel
theorem atom1484Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) := by
  have h := atom1484_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1484Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1485 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1485 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1485 = ((g 5) * (g 7) * (g 13)) := by
  norm_num [atom1485, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1485_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27298019539296 : Int) atom1485) := by
  rw [SparsePolynomial.eval_scale, eval_atom1485]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1485Coded : CoefficientMerge.Poly := [(nat_lit 3061, Int.ofNat (nat_lit 1))]
theorem atom1485Coded_decode : atom1485 = SparsePolynomial.decodeCubic 24 atom1485Coded := by decide +kernel
theorem atom1485Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded) := by
  have h := atom1485_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1485Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1486 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1486 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1486 = ((g 5) * (g 7) * (g 14)) := by
  norm_num [atom1486, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1486_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16918762281696 : Int) atom1486) := by
  rw [SparsePolynomial.eval_scale, eval_atom1486]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1486Coded : CoefficientMerge.Poly := [(nat_lit 3062, Int.ofNat (nat_lit 1))]
theorem atom1486Coded_decode : atom1486 = SparsePolynomial.decodeCubic 24 atom1486Coded := by decide +kernel
theorem atom1486Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) := by
  have h := atom1486_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1486Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1487 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1487 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1487 = ((g 5) * (g 7) * (g 15)) := by
  norm_num [atom1487, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1487_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22064250691296 : Int) atom1487) := by
  rw [SparsePolynomial.eval_scale, eval_atom1487]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1487Coded : CoefficientMerge.Poly := [(nat_lit 3063, Int.ofNat (nat_lit 1))]
theorem atom1487Coded_decode : atom1487 = SparsePolynomial.decodeCubic 24 atom1487Coded := by decide +kernel
theorem atom1487Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) := by
  have h := atom1487_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1487Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1488 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1488 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1488 = ((g 5) * (g 7) * (g 16)) := by
  norm_num [atom1488, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1488_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27209739100896 : Int) atom1488) := by
  rw [SparsePolynomial.eval_scale, eval_atom1488]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1488Coded : CoefficientMerge.Poly := [(nat_lit 3064, Int.ofNat (nat_lit 1))]
theorem atom1488Coded_decode : atom1488 = SparsePolynomial.decodeCubic 24 atom1488Coded := by decide +kernel
theorem atom1488Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded) := by
  have h := atom1488_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1488Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block020 : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 330838724412000)), (nat_lit 2660, Int.ofNat (nat_lit 432262826251200)), (nat_lit 2661, Int.ofNat (nat_lit 416309943672000)), (nat_lit 2662, Int.ofNat (nat_lit 457356545604000)), (nat_lit 2663, Int.ofNat (nat_lit 510982927610400)), (nat_lit 2679, Int.ofNat (nat_lit 208278237081600)), (nat_lit 2680, Int.ofNat (nat_lit 366404392166400)), (nat_lit 2681, Int.ofNat (nat_lit 344185237670400)), (nat_lit 2682, Int.ofNat (nat_lit 380141158118400)), (nat_lit 2683, Int.ofNat (nat_lit 346793499662400)), (nat_lit 2684, Int.ofNat (nat_lit 472461551755200)), (nat_lit 2685, Int.ofNat (nat_lit 461611632888000)), (nat_lit 2686, Int.ofNat (nat_lit 436957939454400)), (nat_lit 2687, Int.ofNat (nat_lit 482678754667200)), (nat_lit 2704, Int.ofNat (nat_lit 205392356467200)), (nat_lit 2705, Int.ofNat (nat_lit 377339038272000)), (nat_lit 2706, Int.ofNat (nat_lit 386488935705600)), (nat_lit 2707, Int.ofNat (nat_lit 358244240961600)), (nat_lit 2708, Int.ofNat (nat_lit 489015256766400)), (nat_lit 2709, Int.ofNat (nat_lit 483268301611200)), (nat_lit 2710, Int.ofNat (nat_lit 405924574910400)), (nat_lit 2711, Int.ofNat (nat_lit 533283144811200)), (nat_lit 2729, Int.ofNat (nat_lit 214421767257600)), (nat_lit 2730, Int.ofNat (nat_lit 415025907206400)), (nat_lit 2731, Int.ofNat (nat_lit 389560459176000)), (nat_lit 2732, Int.ofNat (nat_lit 523110721694400)), (nat_lit 2733, Int.ofNat (nat_lit 521304871752000)), (nat_lit 2734, Int.ofNat (nat_lit 446778567345600)), (nat_lit 2735, Int.ofNat (nat_lit 578659171708800)), (nat_lit 2754, Int.ofNat (nat_lit 249088416192000)), (nat_lit 2755, Int.ofNat (nat_lit 449248020026400)), (nat_lit 2756, Int.ofNat (nat_lit 620668861394400)), (nat_lit 2757, Int.ofNat (nat_lit 582988918831200)), (nat_lit 2758, Int.ofNat (nat_lit 416071587909600)), (nat_lit 2759, Int.ofNat (nat_lit 578049932930400)), (nat_lit 2779, Int.ofNat (nat_lit 163652046243840)), (nat_lit 2780, Int.ofNat (nat_lit 483786370015200)), (nat_lit 2781, Int.ofNat (nat_lit 464046353038800)), (nat_lit 2782, Int.ofNat (nat_lit 352564509192000)), (nat_lit 2783, Int.ofNat (nat_lit 361867931119800)), (nat_lit 2804, Int.ofNat (nat_lit 344960709357600)), (nat_lit 2805, Int.ofNat (nat_lit 507525601237200)), (nat_lit 2806, Int.ofNat (nat_lit 377976761080800)), (nat_lit 2807, Int.ofNat (nat_lit 424529099908200)), (nat_lit 2829, Int.ofNat (nat_lit 126080231583600)), (nat_lit 2830, Int.ofNat (nat_lit 174744351860400)), (nat_lit 2831, Int.ofNat (nat_lit 211258137144600)), (nat_lit 2855, Int.ofNat (nat_lit 6690481950600)), (nat_lit 2879, Int.ofNat (nat_lit 49057765684200)), (nat_lit 3005, Int.ofNat (nat_lit 19631255212800)), (nat_lit 3006, Int.ofNat (nat_lit 31325586960096)), (nat_lit 3007, Int.ofNat (nat_lit 6649449936096)), (nat_lit 3008, Int.ofNat (nat_lit 6533608444704)), (nat_lit 3009, Int.ofNat (nat_lit 5725639190304)), (nat_lit 3011, Int.ofNat (nat_lit 2642598614304)), (nat_lit 3012, Int.ofNat (nat_lit 27375228517824)), (nat_lit 3013, Int.ofNat (nat_lit 15524745667200)), (nat_lit 3018, Int.ofNat (nat_lit 6709402022400)), (nat_lit 3030, Int.ofNat (nat_lit 34147372080096)), (nat_lit 3031, Int.ofNat (nat_lit 18942470112192)), (nat_lit 3036, Int.ofNat (nat_lit 25753222645920)), (nat_lit 3037, Int.ofNat (nat_lit 16985780371296)), (nat_lit 3038, Int.ofNat (nat_lit 4544075280096)), (nat_lit 3039, Int.ofNat (nat_lit 7627115856096)), (nat_lit 3040, Int.ofNat (nat_lit 10710156432096)), (nat_lit 3041, Int.ofNat (nat_lit 13793197008096)), (nat_lit 3042, Int.ofNat (nat_lit 10047950030448)), (nat_lit 3043, Int.ofNat (nat_lit 5544496742400)), (nat_lit 3044, Int.ofNat (nat_lit 7750445476752)), (nat_lit 3045, Int.ofNat (nat_lit 48376733335128)), (nat_lit 3046, Int.ofNat (nat_lit 89003021193504)), (nat_lit 3047, Int.ofNat (nat_lit 136178880879492)), (nat_lit 3055, Int.ofNat (nat_lit 12542463216096)), (nat_lit 3056, Int.ofNat (nat_lit 14392247654400)), (nat_lit 3059, Int.ofNat (nat_lit 4124895667200)), (nat_lit 3060, Int.ofNat (nat_lit 34003013980320)), (nat_lit 3061, Int.ofNat (nat_lit 27298019539296)), (nat_lit 3062, Int.ofNat (nat_lit 16918762281696)), (nat_lit 3063, Int.ofNat (nat_lit 22064250691296)), (nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
def block020_data_flat000 : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 330838724412000))]
theorem block020_data_flat000_step : block020_data_flat000 = (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) := by decide +kernel
theorem block020_data_flat000_original : block020_data_flat000 = (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) := by
  rw [block020_data_flat000_step]
def block020_data_flat001 : CoefficientMerge.Poly := [(nat_lit 2660, Int.ofNat (nat_lit 432262826251200))]
theorem block020_data_flat001_step : block020_data_flat001 = (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded) := by decide +kernel
theorem block020_data_flat001_original : block020_data_flat001 = (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded) := by
  rw [block020_data_flat001_step]
def block020_data_flat002 : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 330838724412000)), (nat_lit 2660, Int.ofNat (nat_lit 432262826251200))]
theorem block020_data_flat002_step : block020_data_flat002 = (CoefficientMerge.fastMerge block020_data_flat000 block020_data_flat001) := by decide +kernel
theorem block020_data_flat002_original : block020_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded)) := by
  rw [block020_data_flat002_step, block020_data_flat000_original, block020_data_flat001_original]
def block020_data_flat003 : CoefficientMerge.Poly := [(nat_lit 2661, Int.ofNat (nat_lit 416309943672000))]
theorem block020_data_flat003_step : block020_data_flat003 = (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) := by decide +kernel
theorem block020_data_flat003_original : block020_data_flat003 = (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) := by
  rw [block020_data_flat003_step]
def block020_data_flat004 : CoefficientMerge.Poly := [(nat_lit 2662, Int.ofNat (nat_lit 457356545604000))]
theorem block020_data_flat004_step : block020_data_flat004 = (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) := by decide +kernel
theorem block020_data_flat004_original : block020_data_flat004 = (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) := by
  rw [block020_data_flat004_step]
def block020_data_flat005 : CoefficientMerge.Poly := [(nat_lit 2663, Int.ofNat (nat_lit 510982927610400))]
theorem block020_data_flat005_step : block020_data_flat005 = (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded) := by decide +kernel
theorem block020_data_flat005_original : block020_data_flat005 = (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded) := by
  rw [block020_data_flat005_step]
def block020_data_flat006 : CoefficientMerge.Poly := [(nat_lit 2662, Int.ofNat (nat_lit 457356545604000)), (nat_lit 2663, Int.ofNat (nat_lit 510982927610400))]
theorem block020_data_flat006_step : block020_data_flat006 = (CoefficientMerge.fastMerge block020_data_flat004 block020_data_flat005) := by decide +kernel
theorem block020_data_flat006_original : block020_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded)) := by
  rw [block020_data_flat006_step, block020_data_flat004_original, block020_data_flat005_original]
def block020_data_flat007 : CoefficientMerge.Poly := [(nat_lit 2661, Int.ofNat (nat_lit 416309943672000)), (nat_lit 2662, Int.ofNat (nat_lit 457356545604000)), (nat_lit 2663, Int.ofNat (nat_lit 510982927610400))]
theorem block020_data_flat007_step : block020_data_flat007 = (CoefficientMerge.fastMerge block020_data_flat003 block020_data_flat006) := by decide +kernel
theorem block020_data_flat007_original : block020_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded))) := by
  rw [block020_data_flat007_step, block020_data_flat003_original, block020_data_flat006_original]
def block020_data_flat008 : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 330838724412000)), (nat_lit 2660, Int.ofNat (nat_lit 432262826251200)), (nat_lit 2661, Int.ofNat (nat_lit 416309943672000)), (nat_lit 2662, Int.ofNat (nat_lit 457356545604000)), (nat_lit 2663, Int.ofNat (nat_lit 510982927610400))]
theorem block020_data_flat008_step : block020_data_flat008 = (CoefficientMerge.fastMerge block020_data_flat002 block020_data_flat007) := by decide +kernel
theorem block020_data_flat008_original : block020_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded)))) := by
  rw [block020_data_flat008_step, block020_data_flat002_original, block020_data_flat007_original]
def block020_data_flat009 : CoefficientMerge.Poly := [(nat_lit 2679, Int.ofNat (nat_lit 208278237081600))]
theorem block020_data_flat009_step : block020_data_flat009 = (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) := by decide +kernel
theorem block020_data_flat009_original : block020_data_flat009 = (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) := by
  rw [block020_data_flat009_step]
def block020_data_flat010 : CoefficientMerge.Poly := [(nat_lit 2680, Int.ofNat (nat_lit 366404392166400))]
theorem block020_data_flat010_step : block020_data_flat010 = (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded) := by decide +kernel
theorem block020_data_flat010_original : block020_data_flat010 = (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded) := by
  rw [block020_data_flat010_step]
def block020_data_flat011 : CoefficientMerge.Poly := [(nat_lit 2679, Int.ofNat (nat_lit 208278237081600)), (nat_lit 2680, Int.ofNat (nat_lit 366404392166400))]
theorem block020_data_flat011_step : block020_data_flat011 = (CoefficientMerge.fastMerge block020_data_flat009 block020_data_flat010) := by decide +kernel
theorem block020_data_flat011_original : block020_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded)) := by
  rw [block020_data_flat011_step, block020_data_flat009_original, block020_data_flat010_original]
def block020_data_flat012 : CoefficientMerge.Poly := [(nat_lit 2681, Int.ofNat (nat_lit 344185237670400))]
theorem block020_data_flat012_step : block020_data_flat012 = (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) := by decide +kernel
theorem block020_data_flat012_original : block020_data_flat012 = (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) := by
  rw [block020_data_flat012_step]
def block020_data_flat013 : CoefficientMerge.Poly := [(nat_lit 2682, Int.ofNat (nat_lit 380141158118400))]
theorem block020_data_flat013_step : block020_data_flat013 = (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) := by decide +kernel
theorem block020_data_flat013_original : block020_data_flat013 = (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) := by
  rw [block020_data_flat013_step]
def block020_data_flat014 : CoefficientMerge.Poly := [(nat_lit 2683, Int.ofNat (nat_lit 346793499662400))]
theorem block020_data_flat014_step : block020_data_flat014 = (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded) := by decide +kernel
theorem block020_data_flat014_original : block020_data_flat014 = (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded) := by
  rw [block020_data_flat014_step]
def block020_data_flat015 : CoefficientMerge.Poly := [(nat_lit 2682, Int.ofNat (nat_lit 380141158118400)), (nat_lit 2683, Int.ofNat (nat_lit 346793499662400))]
theorem block020_data_flat015_step : block020_data_flat015 = (CoefficientMerge.fastMerge block020_data_flat013 block020_data_flat014) := by decide +kernel
theorem block020_data_flat015_original : block020_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded)) := by
  rw [block020_data_flat015_step, block020_data_flat013_original, block020_data_flat014_original]
def block020_data_flat016 : CoefficientMerge.Poly := [(nat_lit 2681, Int.ofNat (nat_lit 344185237670400)), (nat_lit 2682, Int.ofNat (nat_lit 380141158118400)), (nat_lit 2683, Int.ofNat (nat_lit 346793499662400))]
theorem block020_data_flat016_step : block020_data_flat016 = (CoefficientMerge.fastMerge block020_data_flat012 block020_data_flat015) := by decide +kernel
theorem block020_data_flat016_original : block020_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded))) := by
  rw [block020_data_flat016_step, block020_data_flat012_original, block020_data_flat015_original]
def block020_data_flat017 : CoefficientMerge.Poly := [(nat_lit 2679, Int.ofNat (nat_lit 208278237081600)), (nat_lit 2680, Int.ofNat (nat_lit 366404392166400)), (nat_lit 2681, Int.ofNat (nat_lit 344185237670400)), (nat_lit 2682, Int.ofNat (nat_lit 380141158118400)), (nat_lit 2683, Int.ofNat (nat_lit 346793499662400))]
theorem block020_data_flat017_step : block020_data_flat017 = (CoefficientMerge.fastMerge block020_data_flat011 block020_data_flat016) := by decide +kernel
theorem block020_data_flat017_original : block020_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded)))) := by
  rw [block020_data_flat017_step, block020_data_flat011_original, block020_data_flat016_original]
def block020_data_flat018 : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 330838724412000)), (nat_lit 2660, Int.ofNat (nat_lit 432262826251200)), (nat_lit 2661, Int.ofNat (nat_lit 416309943672000)), (nat_lit 2662, Int.ofNat (nat_lit 457356545604000)), (nat_lit 2663, Int.ofNat (nat_lit 510982927610400)), (nat_lit 2679, Int.ofNat (nat_lit 208278237081600)), (nat_lit 2680, Int.ofNat (nat_lit 366404392166400)), (nat_lit 2681, Int.ofNat (nat_lit 344185237670400)), (nat_lit 2682, Int.ofNat (nat_lit 380141158118400)), (nat_lit 2683, Int.ofNat (nat_lit 346793499662400))]
theorem block020_data_flat018_step : block020_data_flat018 = (CoefficientMerge.fastMerge block020_data_flat008 block020_data_flat017) := by decide +kernel
theorem block020_data_flat018_original : block020_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded))))) := by
  rw [block020_data_flat018_step, block020_data_flat008_original, block020_data_flat017_original]
def block020_data_flat019 : CoefficientMerge.Poly := [(nat_lit 2684, Int.ofNat (nat_lit 472461551755200))]
theorem block020_data_flat019_step : block020_data_flat019 = (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) := by decide +kernel
theorem block020_data_flat019_original : block020_data_flat019 = (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) := by
  rw [block020_data_flat019_step]
def block020_data_flat020 : CoefficientMerge.Poly := [(nat_lit 2685, Int.ofNat (nat_lit 461611632888000))]
theorem block020_data_flat020_step : block020_data_flat020 = (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded) := by decide +kernel
theorem block020_data_flat020_original : block020_data_flat020 = (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded) := by
  rw [block020_data_flat020_step]
def block020_data_flat021 : CoefficientMerge.Poly := [(nat_lit 2684, Int.ofNat (nat_lit 472461551755200)), (nat_lit 2685, Int.ofNat (nat_lit 461611632888000))]
theorem block020_data_flat021_step : block020_data_flat021 = (CoefficientMerge.fastMerge block020_data_flat019 block020_data_flat020) := by decide +kernel
theorem block020_data_flat021_original : block020_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded)) := by
  rw [block020_data_flat021_step, block020_data_flat019_original, block020_data_flat020_original]
def block020_data_flat022 : CoefficientMerge.Poly := [(nat_lit 2686, Int.ofNat (nat_lit 436957939454400))]
theorem block020_data_flat022_step : block020_data_flat022 = (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) := by decide +kernel
theorem block020_data_flat022_original : block020_data_flat022 = (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) := by
  rw [block020_data_flat022_step]
def block020_data_flat023 : CoefficientMerge.Poly := [(nat_lit 2687, Int.ofNat (nat_lit 482678754667200))]
theorem block020_data_flat023_step : block020_data_flat023 = (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) := by decide +kernel
theorem block020_data_flat023_original : block020_data_flat023 = (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) := by
  rw [block020_data_flat023_step]
def block020_data_flat024 : CoefficientMerge.Poly := [(nat_lit 2704, Int.ofNat (nat_lit 205392356467200))]
theorem block020_data_flat024_step : block020_data_flat024 = (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded) := by decide +kernel
theorem block020_data_flat024_original : block020_data_flat024 = (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded) := by
  rw [block020_data_flat024_step]
def block020_data_flat025 : CoefficientMerge.Poly := [(nat_lit 2687, Int.ofNat (nat_lit 482678754667200)), (nat_lit 2704, Int.ofNat (nat_lit 205392356467200))]
theorem block020_data_flat025_step : block020_data_flat025 = (CoefficientMerge.fastMerge block020_data_flat023 block020_data_flat024) := by decide +kernel
theorem block020_data_flat025_original : block020_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded)) := by
  rw [block020_data_flat025_step, block020_data_flat023_original, block020_data_flat024_original]
def block020_data_flat026 : CoefficientMerge.Poly := [(nat_lit 2686, Int.ofNat (nat_lit 436957939454400)), (nat_lit 2687, Int.ofNat (nat_lit 482678754667200)), (nat_lit 2704, Int.ofNat (nat_lit 205392356467200))]
theorem block020_data_flat026_step : block020_data_flat026 = (CoefficientMerge.fastMerge block020_data_flat022 block020_data_flat025) := by decide +kernel
theorem block020_data_flat026_original : block020_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded))) := by
  rw [block020_data_flat026_step, block020_data_flat022_original, block020_data_flat025_original]
def block020_data_flat027 : CoefficientMerge.Poly := [(nat_lit 2684, Int.ofNat (nat_lit 472461551755200)), (nat_lit 2685, Int.ofNat (nat_lit 461611632888000)), (nat_lit 2686, Int.ofNat (nat_lit 436957939454400)), (nat_lit 2687, Int.ofNat (nat_lit 482678754667200)), (nat_lit 2704, Int.ofNat (nat_lit 205392356467200))]
theorem block020_data_flat027_step : block020_data_flat027 = (CoefficientMerge.fastMerge block020_data_flat021 block020_data_flat026) := by decide +kernel
theorem block020_data_flat027_original : block020_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded)))) := by
  rw [block020_data_flat027_step, block020_data_flat021_original, block020_data_flat026_original]
def block020_data_flat028 : CoefficientMerge.Poly := [(nat_lit 2705, Int.ofNat (nat_lit 377339038272000))]
theorem block020_data_flat028_step : block020_data_flat028 = (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) := by decide +kernel
theorem block020_data_flat028_original : block020_data_flat028 = (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) := by
  rw [block020_data_flat028_step]
def block020_data_flat029 : CoefficientMerge.Poly := [(nat_lit 2706, Int.ofNat (nat_lit 386488935705600))]
theorem block020_data_flat029_step : block020_data_flat029 = (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded) := by decide +kernel
theorem block020_data_flat029_original : block020_data_flat029 = (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded) := by
  rw [block020_data_flat029_step]
def block020_data_flat030 : CoefficientMerge.Poly := [(nat_lit 2705, Int.ofNat (nat_lit 377339038272000)), (nat_lit 2706, Int.ofNat (nat_lit 386488935705600))]
theorem block020_data_flat030_step : block020_data_flat030 = (CoefficientMerge.fastMerge block020_data_flat028 block020_data_flat029) := by decide +kernel
theorem block020_data_flat030_original : block020_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded)) := by
  rw [block020_data_flat030_step, block020_data_flat028_original, block020_data_flat029_original]
def block020_data_flat031 : CoefficientMerge.Poly := [(nat_lit 2707, Int.ofNat (nat_lit 358244240961600))]
theorem block020_data_flat031_step : block020_data_flat031 = (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) := by decide +kernel
theorem block020_data_flat031_original : block020_data_flat031 = (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) := by
  rw [block020_data_flat031_step]
def block020_data_flat032 : CoefficientMerge.Poly := [(nat_lit 2708, Int.ofNat (nat_lit 489015256766400))]
theorem block020_data_flat032_step : block020_data_flat032 = (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) := by decide +kernel
theorem block020_data_flat032_original : block020_data_flat032 = (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) := by
  rw [block020_data_flat032_step]
def block020_data_flat033 : CoefficientMerge.Poly := [(nat_lit 2709, Int.ofNat (nat_lit 483268301611200))]
theorem block020_data_flat033_step : block020_data_flat033 = (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded) := by decide +kernel
theorem block020_data_flat033_original : block020_data_flat033 = (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded) := by
  rw [block020_data_flat033_step]
def block020_data_flat034 : CoefficientMerge.Poly := [(nat_lit 2708, Int.ofNat (nat_lit 489015256766400)), (nat_lit 2709, Int.ofNat (nat_lit 483268301611200))]
theorem block020_data_flat034_step : block020_data_flat034 = (CoefficientMerge.fastMerge block020_data_flat032 block020_data_flat033) := by decide +kernel
theorem block020_data_flat034_original : block020_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded)) := by
  rw [block020_data_flat034_step, block020_data_flat032_original, block020_data_flat033_original]
def block020_data_flat035 : CoefficientMerge.Poly := [(nat_lit 2707, Int.ofNat (nat_lit 358244240961600)), (nat_lit 2708, Int.ofNat (nat_lit 489015256766400)), (nat_lit 2709, Int.ofNat (nat_lit 483268301611200))]
theorem block020_data_flat035_step : block020_data_flat035 = (CoefficientMerge.fastMerge block020_data_flat031 block020_data_flat034) := by decide +kernel
theorem block020_data_flat035_original : block020_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded))) := by
  rw [block020_data_flat035_step, block020_data_flat031_original, block020_data_flat034_original]
def block020_data_flat036 : CoefficientMerge.Poly := [(nat_lit 2705, Int.ofNat (nat_lit 377339038272000)), (nat_lit 2706, Int.ofNat (nat_lit 386488935705600)), (nat_lit 2707, Int.ofNat (nat_lit 358244240961600)), (nat_lit 2708, Int.ofNat (nat_lit 489015256766400)), (nat_lit 2709, Int.ofNat (nat_lit 483268301611200))]
theorem block020_data_flat036_step : block020_data_flat036 = (CoefficientMerge.fastMerge block020_data_flat030 block020_data_flat035) := by decide +kernel
theorem block020_data_flat036_original : block020_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded)))) := by
  rw [block020_data_flat036_step, block020_data_flat030_original, block020_data_flat035_original]
def block020_data_flat037 : CoefficientMerge.Poly := [(nat_lit 2684, Int.ofNat (nat_lit 472461551755200)), (nat_lit 2685, Int.ofNat (nat_lit 461611632888000)), (nat_lit 2686, Int.ofNat (nat_lit 436957939454400)), (nat_lit 2687, Int.ofNat (nat_lit 482678754667200)), (nat_lit 2704, Int.ofNat (nat_lit 205392356467200)), (nat_lit 2705, Int.ofNat (nat_lit 377339038272000)), (nat_lit 2706, Int.ofNat (nat_lit 386488935705600)), (nat_lit 2707, Int.ofNat (nat_lit 358244240961600)), (nat_lit 2708, Int.ofNat (nat_lit 489015256766400)), (nat_lit 2709, Int.ofNat (nat_lit 483268301611200))]
theorem block020_data_flat037_step : block020_data_flat037 = (CoefficientMerge.fastMerge block020_data_flat027 block020_data_flat036) := by decide +kernel
theorem block020_data_flat037_original : block020_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded))))) := by
  rw [block020_data_flat037_step, block020_data_flat027_original, block020_data_flat036_original]
def block020_data_flat038 : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 330838724412000)), (nat_lit 2660, Int.ofNat (nat_lit 432262826251200)), (nat_lit 2661, Int.ofNat (nat_lit 416309943672000)), (nat_lit 2662, Int.ofNat (nat_lit 457356545604000)), (nat_lit 2663, Int.ofNat (nat_lit 510982927610400)), (nat_lit 2679, Int.ofNat (nat_lit 208278237081600)), (nat_lit 2680, Int.ofNat (nat_lit 366404392166400)), (nat_lit 2681, Int.ofNat (nat_lit 344185237670400)), (nat_lit 2682, Int.ofNat (nat_lit 380141158118400)), (nat_lit 2683, Int.ofNat (nat_lit 346793499662400)), (nat_lit 2684, Int.ofNat (nat_lit 472461551755200)), (nat_lit 2685, Int.ofNat (nat_lit 461611632888000)), (nat_lit 2686, Int.ofNat (nat_lit 436957939454400)), (nat_lit 2687, Int.ofNat (nat_lit 482678754667200)), (nat_lit 2704, Int.ofNat (nat_lit 205392356467200)), (nat_lit 2705, Int.ofNat (nat_lit 377339038272000)), (nat_lit 2706, Int.ofNat (nat_lit 386488935705600)), (nat_lit 2707, Int.ofNat (nat_lit 358244240961600)), (nat_lit 2708, Int.ofNat (nat_lit 489015256766400)), (nat_lit 2709, Int.ofNat (nat_lit 483268301611200))]
theorem block020_data_flat038_step : block020_data_flat038 = (CoefficientMerge.fastMerge block020_data_flat018 block020_data_flat037) := by decide +kernel
theorem block020_data_flat038_original : block020_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded)))))) := by
  rw [block020_data_flat038_step, block020_data_flat018_original, block020_data_flat037_original]
def block020_data_flat039 : CoefficientMerge.Poly := [(nat_lit 2710, Int.ofNat (nat_lit 405924574910400))]
theorem block020_data_flat039_step : block020_data_flat039 = (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) := by decide +kernel
theorem block020_data_flat039_original : block020_data_flat039 = (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) := by
  rw [block020_data_flat039_step]
def block020_data_flat040 : CoefficientMerge.Poly := [(nat_lit 2711, Int.ofNat (nat_lit 533283144811200))]
theorem block020_data_flat040_step : block020_data_flat040 = (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded) := by decide +kernel
theorem block020_data_flat040_original : block020_data_flat040 = (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded) := by
  rw [block020_data_flat040_step]
def block020_data_flat041 : CoefficientMerge.Poly := [(nat_lit 2710, Int.ofNat (nat_lit 405924574910400)), (nat_lit 2711, Int.ofNat (nat_lit 533283144811200))]
theorem block020_data_flat041_step : block020_data_flat041 = (CoefficientMerge.fastMerge block020_data_flat039 block020_data_flat040) := by decide +kernel
theorem block020_data_flat041_original : block020_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded)) := by
  rw [block020_data_flat041_step, block020_data_flat039_original, block020_data_flat040_original]
def block020_data_flat042 : CoefficientMerge.Poly := [(nat_lit 2729, Int.ofNat (nat_lit 214421767257600))]
theorem block020_data_flat042_step : block020_data_flat042 = (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) := by decide +kernel
theorem block020_data_flat042_original : block020_data_flat042 = (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) := by
  rw [block020_data_flat042_step]
def block020_data_flat043 : CoefficientMerge.Poly := [(nat_lit 2730, Int.ofNat (nat_lit 415025907206400))]
theorem block020_data_flat043_step : block020_data_flat043 = (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) := by decide +kernel
theorem block020_data_flat043_original : block020_data_flat043 = (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) := by
  rw [block020_data_flat043_step]
def block020_data_flat044 : CoefficientMerge.Poly := [(nat_lit 2731, Int.ofNat (nat_lit 389560459176000))]
theorem block020_data_flat044_step : block020_data_flat044 = (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded) := by decide +kernel
theorem block020_data_flat044_original : block020_data_flat044 = (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded) := by
  rw [block020_data_flat044_step]
def block020_data_flat045 : CoefficientMerge.Poly := [(nat_lit 2730, Int.ofNat (nat_lit 415025907206400)), (nat_lit 2731, Int.ofNat (nat_lit 389560459176000))]
theorem block020_data_flat045_step : block020_data_flat045 = (CoefficientMerge.fastMerge block020_data_flat043 block020_data_flat044) := by decide +kernel
theorem block020_data_flat045_original : block020_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded)) := by
  rw [block020_data_flat045_step, block020_data_flat043_original, block020_data_flat044_original]
def block020_data_flat046 : CoefficientMerge.Poly := [(nat_lit 2729, Int.ofNat (nat_lit 214421767257600)), (nat_lit 2730, Int.ofNat (nat_lit 415025907206400)), (nat_lit 2731, Int.ofNat (nat_lit 389560459176000))]
theorem block020_data_flat046_step : block020_data_flat046 = (CoefficientMerge.fastMerge block020_data_flat042 block020_data_flat045) := by decide +kernel
theorem block020_data_flat046_original : block020_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded))) := by
  rw [block020_data_flat046_step, block020_data_flat042_original, block020_data_flat045_original]
def block020_data_flat047 : CoefficientMerge.Poly := [(nat_lit 2710, Int.ofNat (nat_lit 405924574910400)), (nat_lit 2711, Int.ofNat (nat_lit 533283144811200)), (nat_lit 2729, Int.ofNat (nat_lit 214421767257600)), (nat_lit 2730, Int.ofNat (nat_lit 415025907206400)), (nat_lit 2731, Int.ofNat (nat_lit 389560459176000))]
theorem block020_data_flat047_step : block020_data_flat047 = (CoefficientMerge.fastMerge block020_data_flat041 block020_data_flat046) := by decide +kernel
theorem block020_data_flat047_original : block020_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded)))) := by
  rw [block020_data_flat047_step, block020_data_flat041_original, block020_data_flat046_original]
def block020_data_flat048 : CoefficientMerge.Poly := [(nat_lit 2732, Int.ofNat (nat_lit 523110721694400))]
theorem block020_data_flat048_step : block020_data_flat048 = (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) := by decide +kernel
theorem block020_data_flat048_original : block020_data_flat048 = (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) := by
  rw [block020_data_flat048_step]
def block020_data_flat049 : CoefficientMerge.Poly := [(nat_lit 2733, Int.ofNat (nat_lit 521304871752000))]
theorem block020_data_flat049_step : block020_data_flat049 = (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded) := by decide +kernel
theorem block020_data_flat049_original : block020_data_flat049 = (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded) := by
  rw [block020_data_flat049_step]
def block020_data_flat050 : CoefficientMerge.Poly := [(nat_lit 2732, Int.ofNat (nat_lit 523110721694400)), (nat_lit 2733, Int.ofNat (nat_lit 521304871752000))]
theorem block020_data_flat050_step : block020_data_flat050 = (CoefficientMerge.fastMerge block020_data_flat048 block020_data_flat049) := by decide +kernel
theorem block020_data_flat050_original : block020_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded)) := by
  rw [block020_data_flat050_step, block020_data_flat048_original, block020_data_flat049_original]
def block020_data_flat051 : CoefficientMerge.Poly := [(nat_lit 2734, Int.ofNat (nat_lit 446778567345600))]
theorem block020_data_flat051_step : block020_data_flat051 = (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) := by decide +kernel
theorem block020_data_flat051_original : block020_data_flat051 = (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) := by
  rw [block020_data_flat051_step]
def block020_data_flat052 : CoefficientMerge.Poly := [(nat_lit 2735, Int.ofNat (nat_lit 578659171708800))]
theorem block020_data_flat052_step : block020_data_flat052 = (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) := by decide +kernel
theorem block020_data_flat052_original : block020_data_flat052 = (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) := by
  rw [block020_data_flat052_step]
def block020_data_flat053 : CoefficientMerge.Poly := [(nat_lit 2754, Int.ofNat (nat_lit 249088416192000))]
theorem block020_data_flat053_step : block020_data_flat053 = (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded) := by decide +kernel
theorem block020_data_flat053_original : block020_data_flat053 = (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded) := by
  rw [block020_data_flat053_step]
def block020_data_flat054 : CoefficientMerge.Poly := [(nat_lit 2735, Int.ofNat (nat_lit 578659171708800)), (nat_lit 2754, Int.ofNat (nat_lit 249088416192000))]
theorem block020_data_flat054_step : block020_data_flat054 = (CoefficientMerge.fastMerge block020_data_flat052 block020_data_flat053) := by decide +kernel
theorem block020_data_flat054_original : block020_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded)) := by
  rw [block020_data_flat054_step, block020_data_flat052_original, block020_data_flat053_original]
def block020_data_flat055 : CoefficientMerge.Poly := [(nat_lit 2734, Int.ofNat (nat_lit 446778567345600)), (nat_lit 2735, Int.ofNat (nat_lit 578659171708800)), (nat_lit 2754, Int.ofNat (nat_lit 249088416192000))]
theorem block020_data_flat055_step : block020_data_flat055 = (CoefficientMerge.fastMerge block020_data_flat051 block020_data_flat054) := by decide +kernel
theorem block020_data_flat055_original : block020_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded))) := by
  rw [block020_data_flat055_step, block020_data_flat051_original, block020_data_flat054_original]
def block020_data_flat056 : CoefficientMerge.Poly := [(nat_lit 2732, Int.ofNat (nat_lit 523110721694400)), (nat_lit 2733, Int.ofNat (nat_lit 521304871752000)), (nat_lit 2734, Int.ofNat (nat_lit 446778567345600)), (nat_lit 2735, Int.ofNat (nat_lit 578659171708800)), (nat_lit 2754, Int.ofNat (nat_lit 249088416192000))]
theorem block020_data_flat056_step : block020_data_flat056 = (CoefficientMerge.fastMerge block020_data_flat050 block020_data_flat055) := by decide +kernel
theorem block020_data_flat056_original : block020_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded)))) := by
  rw [block020_data_flat056_step, block020_data_flat050_original, block020_data_flat055_original]
def block020_data_flat057 : CoefficientMerge.Poly := [(nat_lit 2710, Int.ofNat (nat_lit 405924574910400)), (nat_lit 2711, Int.ofNat (nat_lit 533283144811200)), (nat_lit 2729, Int.ofNat (nat_lit 214421767257600)), (nat_lit 2730, Int.ofNat (nat_lit 415025907206400)), (nat_lit 2731, Int.ofNat (nat_lit 389560459176000)), (nat_lit 2732, Int.ofNat (nat_lit 523110721694400)), (nat_lit 2733, Int.ofNat (nat_lit 521304871752000)), (nat_lit 2734, Int.ofNat (nat_lit 446778567345600)), (nat_lit 2735, Int.ofNat (nat_lit 578659171708800)), (nat_lit 2754, Int.ofNat (nat_lit 249088416192000))]
theorem block020_data_flat057_step : block020_data_flat057 = (CoefficientMerge.fastMerge block020_data_flat047 block020_data_flat056) := by decide +kernel
theorem block020_data_flat057_original : block020_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded))))) := by
  rw [block020_data_flat057_step, block020_data_flat047_original, block020_data_flat056_original]
def block020_data_flat058 : CoefficientMerge.Poly := [(nat_lit 2755, Int.ofNat (nat_lit 449248020026400))]
theorem block020_data_flat058_step : block020_data_flat058 = (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) := by decide +kernel
theorem block020_data_flat058_original : block020_data_flat058 = (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) := by
  rw [block020_data_flat058_step]
def block020_data_flat059 : CoefficientMerge.Poly := [(nat_lit 2756, Int.ofNat (nat_lit 620668861394400))]
theorem block020_data_flat059_step : block020_data_flat059 = (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded) := by decide +kernel
theorem block020_data_flat059_original : block020_data_flat059 = (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded) := by
  rw [block020_data_flat059_step]
def block020_data_flat060 : CoefficientMerge.Poly := [(nat_lit 2755, Int.ofNat (nat_lit 449248020026400)), (nat_lit 2756, Int.ofNat (nat_lit 620668861394400))]
theorem block020_data_flat060_step : block020_data_flat060 = (CoefficientMerge.fastMerge block020_data_flat058 block020_data_flat059) := by decide +kernel
theorem block020_data_flat060_original : block020_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded)) := by
  rw [block020_data_flat060_step, block020_data_flat058_original, block020_data_flat059_original]
def block020_data_flat061 : CoefficientMerge.Poly := [(nat_lit 2757, Int.ofNat (nat_lit 582988918831200))]
theorem block020_data_flat061_step : block020_data_flat061 = (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) := by decide +kernel
theorem block020_data_flat061_original : block020_data_flat061 = (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) := by
  rw [block020_data_flat061_step]
def block020_data_flat062 : CoefficientMerge.Poly := [(nat_lit 2758, Int.ofNat (nat_lit 416071587909600))]
theorem block020_data_flat062_step : block020_data_flat062 = (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) := by decide +kernel
theorem block020_data_flat062_original : block020_data_flat062 = (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) := by
  rw [block020_data_flat062_step]
def block020_data_flat063 : CoefficientMerge.Poly := [(nat_lit 2759, Int.ofNat (nat_lit 578049932930400))]
theorem block020_data_flat063_step : block020_data_flat063 = (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded) := by decide +kernel
theorem block020_data_flat063_original : block020_data_flat063 = (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded) := by
  rw [block020_data_flat063_step]
def block020_data_flat064 : CoefficientMerge.Poly := [(nat_lit 2758, Int.ofNat (nat_lit 416071587909600)), (nat_lit 2759, Int.ofNat (nat_lit 578049932930400))]
theorem block020_data_flat064_step : block020_data_flat064 = (CoefficientMerge.fastMerge block020_data_flat062 block020_data_flat063) := by decide +kernel
theorem block020_data_flat064_original : block020_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded)) := by
  rw [block020_data_flat064_step, block020_data_flat062_original, block020_data_flat063_original]
def block020_data_flat065 : CoefficientMerge.Poly := [(nat_lit 2757, Int.ofNat (nat_lit 582988918831200)), (nat_lit 2758, Int.ofNat (nat_lit 416071587909600)), (nat_lit 2759, Int.ofNat (nat_lit 578049932930400))]
theorem block020_data_flat065_step : block020_data_flat065 = (CoefficientMerge.fastMerge block020_data_flat061 block020_data_flat064) := by decide +kernel
theorem block020_data_flat065_original : block020_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded))) := by
  rw [block020_data_flat065_step, block020_data_flat061_original, block020_data_flat064_original]
def block020_data_flat066 : CoefficientMerge.Poly := [(nat_lit 2755, Int.ofNat (nat_lit 449248020026400)), (nat_lit 2756, Int.ofNat (nat_lit 620668861394400)), (nat_lit 2757, Int.ofNat (nat_lit 582988918831200)), (nat_lit 2758, Int.ofNat (nat_lit 416071587909600)), (nat_lit 2759, Int.ofNat (nat_lit 578049932930400))]
theorem block020_data_flat066_step : block020_data_flat066 = (CoefficientMerge.fastMerge block020_data_flat060 block020_data_flat065) := by decide +kernel
theorem block020_data_flat066_original : block020_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded)))) := by
  rw [block020_data_flat066_step, block020_data_flat060_original, block020_data_flat065_original]
def block020_data_flat067 : CoefficientMerge.Poly := [(nat_lit 2779, Int.ofNat (nat_lit 163652046243840))]
theorem block020_data_flat067_step : block020_data_flat067 = (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) := by decide +kernel
theorem block020_data_flat067_original : block020_data_flat067 = (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) := by
  rw [block020_data_flat067_step]
def block020_data_flat068 : CoefficientMerge.Poly := [(nat_lit 2780, Int.ofNat (nat_lit 483786370015200))]
theorem block020_data_flat068_step : block020_data_flat068 = (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded) := by decide +kernel
theorem block020_data_flat068_original : block020_data_flat068 = (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded) := by
  rw [block020_data_flat068_step]
def block020_data_flat069 : CoefficientMerge.Poly := [(nat_lit 2779, Int.ofNat (nat_lit 163652046243840)), (nat_lit 2780, Int.ofNat (nat_lit 483786370015200))]
theorem block020_data_flat069_step : block020_data_flat069 = (CoefficientMerge.fastMerge block020_data_flat067 block020_data_flat068) := by decide +kernel
theorem block020_data_flat069_original : block020_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded)) := by
  rw [block020_data_flat069_step, block020_data_flat067_original, block020_data_flat068_original]
def block020_data_flat070 : CoefficientMerge.Poly := [(nat_lit 2781, Int.ofNat (nat_lit 464046353038800))]
theorem block020_data_flat070_step : block020_data_flat070 = (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) := by decide +kernel
theorem block020_data_flat070_original : block020_data_flat070 = (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) := by
  rw [block020_data_flat070_step]
def block020_data_flat071 : CoefficientMerge.Poly := [(nat_lit 2782, Int.ofNat (nat_lit 352564509192000))]
theorem block020_data_flat071_step : block020_data_flat071 = (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) := by decide +kernel
theorem block020_data_flat071_original : block020_data_flat071 = (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) := by
  rw [block020_data_flat071_step]
def block020_data_flat072 : CoefficientMerge.Poly := [(nat_lit 2783, Int.ofNat (nat_lit 361867931119800))]
theorem block020_data_flat072_step : block020_data_flat072 = (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded) := by decide +kernel
theorem block020_data_flat072_original : block020_data_flat072 = (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded) := by
  rw [block020_data_flat072_step]
def block020_data_flat073 : CoefficientMerge.Poly := [(nat_lit 2782, Int.ofNat (nat_lit 352564509192000)), (nat_lit 2783, Int.ofNat (nat_lit 361867931119800))]
theorem block020_data_flat073_step : block020_data_flat073 = (CoefficientMerge.fastMerge block020_data_flat071 block020_data_flat072) := by decide +kernel
theorem block020_data_flat073_original : block020_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded)) := by
  rw [block020_data_flat073_step, block020_data_flat071_original, block020_data_flat072_original]
def block020_data_flat074 : CoefficientMerge.Poly := [(nat_lit 2781, Int.ofNat (nat_lit 464046353038800)), (nat_lit 2782, Int.ofNat (nat_lit 352564509192000)), (nat_lit 2783, Int.ofNat (nat_lit 361867931119800))]
theorem block020_data_flat074_step : block020_data_flat074 = (CoefficientMerge.fastMerge block020_data_flat070 block020_data_flat073) := by decide +kernel
theorem block020_data_flat074_original : block020_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded))) := by
  rw [block020_data_flat074_step, block020_data_flat070_original, block020_data_flat073_original]
def block020_data_flat075 : CoefficientMerge.Poly := [(nat_lit 2779, Int.ofNat (nat_lit 163652046243840)), (nat_lit 2780, Int.ofNat (nat_lit 483786370015200)), (nat_lit 2781, Int.ofNat (nat_lit 464046353038800)), (nat_lit 2782, Int.ofNat (nat_lit 352564509192000)), (nat_lit 2783, Int.ofNat (nat_lit 361867931119800))]
theorem block020_data_flat075_step : block020_data_flat075 = (CoefficientMerge.fastMerge block020_data_flat069 block020_data_flat074) := by decide +kernel
theorem block020_data_flat075_original : block020_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded)))) := by
  rw [block020_data_flat075_step, block020_data_flat069_original, block020_data_flat074_original]
def block020_data_flat076 : CoefficientMerge.Poly := [(nat_lit 2755, Int.ofNat (nat_lit 449248020026400)), (nat_lit 2756, Int.ofNat (nat_lit 620668861394400)), (nat_lit 2757, Int.ofNat (nat_lit 582988918831200)), (nat_lit 2758, Int.ofNat (nat_lit 416071587909600)), (nat_lit 2759, Int.ofNat (nat_lit 578049932930400)), (nat_lit 2779, Int.ofNat (nat_lit 163652046243840)), (nat_lit 2780, Int.ofNat (nat_lit 483786370015200)), (nat_lit 2781, Int.ofNat (nat_lit 464046353038800)), (nat_lit 2782, Int.ofNat (nat_lit 352564509192000)), (nat_lit 2783, Int.ofNat (nat_lit 361867931119800))]
theorem block020_data_flat076_step : block020_data_flat076 = (CoefficientMerge.fastMerge block020_data_flat066 block020_data_flat075) := by decide +kernel
theorem block020_data_flat076_original : block020_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded))))) := by
  rw [block020_data_flat076_step, block020_data_flat066_original, block020_data_flat075_original]
def block020_data_flat077 : CoefficientMerge.Poly := [(nat_lit 2710, Int.ofNat (nat_lit 405924574910400)), (nat_lit 2711, Int.ofNat (nat_lit 533283144811200)), (nat_lit 2729, Int.ofNat (nat_lit 214421767257600)), (nat_lit 2730, Int.ofNat (nat_lit 415025907206400)), (nat_lit 2731, Int.ofNat (nat_lit 389560459176000)), (nat_lit 2732, Int.ofNat (nat_lit 523110721694400)), (nat_lit 2733, Int.ofNat (nat_lit 521304871752000)), (nat_lit 2734, Int.ofNat (nat_lit 446778567345600)), (nat_lit 2735, Int.ofNat (nat_lit 578659171708800)), (nat_lit 2754, Int.ofNat (nat_lit 249088416192000)), (nat_lit 2755, Int.ofNat (nat_lit 449248020026400)), (nat_lit 2756, Int.ofNat (nat_lit 620668861394400)), (nat_lit 2757, Int.ofNat (nat_lit 582988918831200)), (nat_lit 2758, Int.ofNat (nat_lit 416071587909600)), (nat_lit 2759, Int.ofNat (nat_lit 578049932930400)), (nat_lit 2779, Int.ofNat (nat_lit 163652046243840)), (nat_lit 2780, Int.ofNat (nat_lit 483786370015200)), (nat_lit 2781, Int.ofNat (nat_lit 464046353038800)), (nat_lit 2782, Int.ofNat (nat_lit 352564509192000)), (nat_lit 2783, Int.ofNat (nat_lit 361867931119800))]
theorem block020_data_flat077_step : block020_data_flat077 = (CoefficientMerge.fastMerge block020_data_flat057 block020_data_flat076) := by decide +kernel
theorem block020_data_flat077_original : block020_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded)))))) := by
  rw [block020_data_flat077_step, block020_data_flat057_original, block020_data_flat076_original]
def block020_data_flat078 : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 330838724412000)), (nat_lit 2660, Int.ofNat (nat_lit 432262826251200)), (nat_lit 2661, Int.ofNat (nat_lit 416309943672000)), (nat_lit 2662, Int.ofNat (nat_lit 457356545604000)), (nat_lit 2663, Int.ofNat (nat_lit 510982927610400)), (nat_lit 2679, Int.ofNat (nat_lit 208278237081600)), (nat_lit 2680, Int.ofNat (nat_lit 366404392166400)), (nat_lit 2681, Int.ofNat (nat_lit 344185237670400)), (nat_lit 2682, Int.ofNat (nat_lit 380141158118400)), (nat_lit 2683, Int.ofNat (nat_lit 346793499662400)), (nat_lit 2684, Int.ofNat (nat_lit 472461551755200)), (nat_lit 2685, Int.ofNat (nat_lit 461611632888000)), (nat_lit 2686, Int.ofNat (nat_lit 436957939454400)), (nat_lit 2687, Int.ofNat (nat_lit 482678754667200)), (nat_lit 2704, Int.ofNat (nat_lit 205392356467200)), (nat_lit 2705, Int.ofNat (nat_lit 377339038272000)), (nat_lit 2706, Int.ofNat (nat_lit 386488935705600)), (nat_lit 2707, Int.ofNat (nat_lit 358244240961600)), (nat_lit 2708, Int.ofNat (nat_lit 489015256766400)), (nat_lit 2709, Int.ofNat (nat_lit 483268301611200)), (nat_lit 2710, Int.ofNat (nat_lit 405924574910400)), (nat_lit 2711, Int.ofNat (nat_lit 533283144811200)), (nat_lit 2729, Int.ofNat (nat_lit 214421767257600)), (nat_lit 2730, Int.ofNat (nat_lit 415025907206400)), (nat_lit 2731, Int.ofNat (nat_lit 389560459176000)), (nat_lit 2732, Int.ofNat (nat_lit 523110721694400)), (nat_lit 2733, Int.ofNat (nat_lit 521304871752000)), (nat_lit 2734, Int.ofNat (nat_lit 446778567345600)), (nat_lit 2735, Int.ofNat (nat_lit 578659171708800)), (nat_lit 2754, Int.ofNat (nat_lit 249088416192000)), (nat_lit 2755, Int.ofNat (nat_lit 449248020026400)), (nat_lit 2756, Int.ofNat (nat_lit 620668861394400)), (nat_lit 2757, Int.ofNat (nat_lit 582988918831200)), (nat_lit 2758, Int.ofNat (nat_lit 416071587909600)), (nat_lit 2759, Int.ofNat (nat_lit 578049932930400)), (nat_lit 2779, Int.ofNat (nat_lit 163652046243840)), (nat_lit 2780, Int.ofNat (nat_lit 483786370015200)), (nat_lit 2781, Int.ofNat (nat_lit 464046353038800)), (nat_lit 2782, Int.ofNat (nat_lit 352564509192000)), (nat_lit 2783, Int.ofNat (nat_lit 361867931119800))]
theorem block020_data_flat078_step : block020_data_flat078 = (CoefficientMerge.fastMerge block020_data_flat038 block020_data_flat077) := by decide +kernel
theorem block020_data_flat078_original : block020_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded))))))) := by
  rw [block020_data_flat078_step, block020_data_flat038_original, block020_data_flat077_original]
def block020_data_flat079 : CoefficientMerge.Poly := [(nat_lit 2804, Int.ofNat (nat_lit 344960709357600))]
theorem block020_data_flat079_step : block020_data_flat079 = (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) := by decide +kernel
theorem block020_data_flat079_original : block020_data_flat079 = (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) := by
  rw [block020_data_flat079_step]
def block020_data_flat080 : CoefficientMerge.Poly := [(nat_lit 2805, Int.ofNat (nat_lit 507525601237200))]
theorem block020_data_flat080_step : block020_data_flat080 = (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded) := by decide +kernel
theorem block020_data_flat080_original : block020_data_flat080 = (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded) := by
  rw [block020_data_flat080_step]
def block020_data_flat081 : CoefficientMerge.Poly := [(nat_lit 2804, Int.ofNat (nat_lit 344960709357600)), (nat_lit 2805, Int.ofNat (nat_lit 507525601237200))]
theorem block020_data_flat081_step : block020_data_flat081 = (CoefficientMerge.fastMerge block020_data_flat079 block020_data_flat080) := by decide +kernel
theorem block020_data_flat081_original : block020_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded)) := by
  rw [block020_data_flat081_step, block020_data_flat079_original, block020_data_flat080_original]
def block020_data_flat082 : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 377976761080800))]
theorem block020_data_flat082_step : block020_data_flat082 = (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) := by decide +kernel
theorem block020_data_flat082_original : block020_data_flat082 = (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) := by
  rw [block020_data_flat082_step]
def block020_data_flat083 : CoefficientMerge.Poly := [(nat_lit 2807, Int.ofNat (nat_lit 424529099908200))]
theorem block020_data_flat083_step : block020_data_flat083 = (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) := by decide +kernel
theorem block020_data_flat083_original : block020_data_flat083 = (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) := by
  rw [block020_data_flat083_step]
def block020_data_flat084 : CoefficientMerge.Poly := [(nat_lit 2829, Int.ofNat (nat_lit 126080231583600))]
theorem block020_data_flat084_step : block020_data_flat084 = (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded) := by decide +kernel
theorem block020_data_flat084_original : block020_data_flat084 = (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded) := by
  rw [block020_data_flat084_step]
def block020_data_flat085 : CoefficientMerge.Poly := [(nat_lit 2807, Int.ofNat (nat_lit 424529099908200)), (nat_lit 2829, Int.ofNat (nat_lit 126080231583600))]
theorem block020_data_flat085_step : block020_data_flat085 = (CoefficientMerge.fastMerge block020_data_flat083 block020_data_flat084) := by decide +kernel
theorem block020_data_flat085_original : block020_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded)) := by
  rw [block020_data_flat085_step, block020_data_flat083_original, block020_data_flat084_original]
def block020_data_flat086 : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 377976761080800)), (nat_lit 2807, Int.ofNat (nat_lit 424529099908200)), (nat_lit 2829, Int.ofNat (nat_lit 126080231583600))]
theorem block020_data_flat086_step : block020_data_flat086 = (CoefficientMerge.fastMerge block020_data_flat082 block020_data_flat085) := by decide +kernel
theorem block020_data_flat086_original : block020_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded))) := by
  rw [block020_data_flat086_step, block020_data_flat082_original, block020_data_flat085_original]
def block020_data_flat087 : CoefficientMerge.Poly := [(nat_lit 2804, Int.ofNat (nat_lit 344960709357600)), (nat_lit 2805, Int.ofNat (nat_lit 507525601237200)), (nat_lit 2806, Int.ofNat (nat_lit 377976761080800)), (nat_lit 2807, Int.ofNat (nat_lit 424529099908200)), (nat_lit 2829, Int.ofNat (nat_lit 126080231583600))]
theorem block020_data_flat087_step : block020_data_flat087 = (CoefficientMerge.fastMerge block020_data_flat081 block020_data_flat086) := by decide +kernel
theorem block020_data_flat087_original : block020_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded)))) := by
  rw [block020_data_flat087_step, block020_data_flat081_original, block020_data_flat086_original]
def block020_data_flat088 : CoefficientMerge.Poly := [(nat_lit 2830, Int.ofNat (nat_lit 174744351860400))]
theorem block020_data_flat088_step : block020_data_flat088 = (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) := by decide +kernel
theorem block020_data_flat088_original : block020_data_flat088 = (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) := by
  rw [block020_data_flat088_step]
def block020_data_flat089 : CoefficientMerge.Poly := [(nat_lit 2831, Int.ofNat (nat_lit 211258137144600))]
theorem block020_data_flat089_step : block020_data_flat089 = (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded) := by decide +kernel
theorem block020_data_flat089_original : block020_data_flat089 = (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded) := by
  rw [block020_data_flat089_step]
def block020_data_flat090 : CoefficientMerge.Poly := [(nat_lit 2830, Int.ofNat (nat_lit 174744351860400)), (nat_lit 2831, Int.ofNat (nat_lit 211258137144600))]
theorem block020_data_flat090_step : block020_data_flat090 = (CoefficientMerge.fastMerge block020_data_flat088 block020_data_flat089) := by decide +kernel
theorem block020_data_flat090_original : block020_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded)) := by
  rw [block020_data_flat090_step, block020_data_flat088_original, block020_data_flat089_original]
def block020_data_flat091 : CoefficientMerge.Poly := [(nat_lit 2855, Int.ofNat (nat_lit 6690481950600))]
theorem block020_data_flat091_step : block020_data_flat091 = (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) := by decide +kernel
theorem block020_data_flat091_original : block020_data_flat091 = (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) := by
  rw [block020_data_flat091_step]
def block020_data_flat092 : CoefficientMerge.Poly := [(nat_lit 2879, Int.ofNat (nat_lit 49057765684200))]
theorem block020_data_flat092_step : block020_data_flat092 = (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) := by decide +kernel
theorem block020_data_flat092_original : block020_data_flat092 = (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) := by
  rw [block020_data_flat092_step]
def block020_data_flat093 : CoefficientMerge.Poly := [(nat_lit 3005, Int.ofNat (nat_lit 19631255212800))]
theorem block020_data_flat093_step : block020_data_flat093 = (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded) := by decide +kernel
theorem block020_data_flat093_original : block020_data_flat093 = (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded) := by
  rw [block020_data_flat093_step]
def block020_data_flat094 : CoefficientMerge.Poly := [(nat_lit 2879, Int.ofNat (nat_lit 49057765684200)), (nat_lit 3005, Int.ofNat (nat_lit 19631255212800))]
theorem block020_data_flat094_step : block020_data_flat094 = (CoefficientMerge.fastMerge block020_data_flat092 block020_data_flat093) := by decide +kernel
theorem block020_data_flat094_original : block020_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded)) := by
  rw [block020_data_flat094_step, block020_data_flat092_original, block020_data_flat093_original]
def block020_data_flat095 : CoefficientMerge.Poly := [(nat_lit 2855, Int.ofNat (nat_lit 6690481950600)), (nat_lit 2879, Int.ofNat (nat_lit 49057765684200)), (nat_lit 3005, Int.ofNat (nat_lit 19631255212800))]
theorem block020_data_flat095_step : block020_data_flat095 = (CoefficientMerge.fastMerge block020_data_flat091 block020_data_flat094) := by decide +kernel
theorem block020_data_flat095_original : block020_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded))) := by
  rw [block020_data_flat095_step, block020_data_flat091_original, block020_data_flat094_original]
def block020_data_flat096 : CoefficientMerge.Poly := [(nat_lit 2830, Int.ofNat (nat_lit 174744351860400)), (nat_lit 2831, Int.ofNat (nat_lit 211258137144600)), (nat_lit 2855, Int.ofNat (nat_lit 6690481950600)), (nat_lit 2879, Int.ofNat (nat_lit 49057765684200)), (nat_lit 3005, Int.ofNat (nat_lit 19631255212800))]
theorem block020_data_flat096_step : block020_data_flat096 = (CoefficientMerge.fastMerge block020_data_flat090 block020_data_flat095) := by decide +kernel
theorem block020_data_flat096_original : block020_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded)))) := by
  rw [block020_data_flat096_step, block020_data_flat090_original, block020_data_flat095_original]
def block020_data_flat097 : CoefficientMerge.Poly := [(nat_lit 2804, Int.ofNat (nat_lit 344960709357600)), (nat_lit 2805, Int.ofNat (nat_lit 507525601237200)), (nat_lit 2806, Int.ofNat (nat_lit 377976761080800)), (nat_lit 2807, Int.ofNat (nat_lit 424529099908200)), (nat_lit 2829, Int.ofNat (nat_lit 126080231583600)), (nat_lit 2830, Int.ofNat (nat_lit 174744351860400)), (nat_lit 2831, Int.ofNat (nat_lit 211258137144600)), (nat_lit 2855, Int.ofNat (nat_lit 6690481950600)), (nat_lit 2879, Int.ofNat (nat_lit 49057765684200)), (nat_lit 3005, Int.ofNat (nat_lit 19631255212800))]
theorem block020_data_flat097_step : block020_data_flat097 = (CoefficientMerge.fastMerge block020_data_flat087 block020_data_flat096) := by decide +kernel
theorem block020_data_flat097_original : block020_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded))))) := by
  rw [block020_data_flat097_step, block020_data_flat087_original, block020_data_flat096_original]
def block020_data_flat098 : CoefficientMerge.Poly := [(nat_lit 3006, Int.ofNat (nat_lit 31325586960096))]
theorem block020_data_flat098_step : block020_data_flat098 = (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) := by decide +kernel
theorem block020_data_flat098_original : block020_data_flat098 = (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) := by
  rw [block020_data_flat098_step]
def block020_data_flat099 : CoefficientMerge.Poly := [(nat_lit 3007, Int.ofNat (nat_lit 6649449936096))]
theorem block020_data_flat099_step : block020_data_flat099 = (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded) := by decide +kernel
theorem block020_data_flat099_original : block020_data_flat099 = (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded) := by
  rw [block020_data_flat099_step]
def block020_data_flat100 : CoefficientMerge.Poly := [(nat_lit 3006, Int.ofNat (nat_lit 31325586960096)), (nat_lit 3007, Int.ofNat (nat_lit 6649449936096))]
theorem block020_data_flat100_step : block020_data_flat100 = (CoefficientMerge.fastMerge block020_data_flat098 block020_data_flat099) := by decide +kernel
theorem block020_data_flat100_original : block020_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded)) := by
  rw [block020_data_flat100_step, block020_data_flat098_original, block020_data_flat099_original]
def block020_data_flat101 : CoefficientMerge.Poly := [(nat_lit 3008, Int.ofNat (nat_lit 6533608444704))]
theorem block020_data_flat101_step : block020_data_flat101 = (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) := by decide +kernel
theorem block020_data_flat101_original : block020_data_flat101 = (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) := by
  rw [block020_data_flat101_step]
def block020_data_flat102 : CoefficientMerge.Poly := [(nat_lit 3009, Int.ofNat (nat_lit 5725639190304))]
theorem block020_data_flat102_step : block020_data_flat102 = (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) := by decide +kernel
theorem block020_data_flat102_original : block020_data_flat102 = (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) := by
  rw [block020_data_flat102_step]
def block020_data_flat103 : CoefficientMerge.Poly := [(nat_lit 3011, Int.ofNat (nat_lit 2642598614304))]
theorem block020_data_flat103_step : block020_data_flat103 = (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded) := by decide +kernel
theorem block020_data_flat103_original : block020_data_flat103 = (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded) := by
  rw [block020_data_flat103_step]
def block020_data_flat104 : CoefficientMerge.Poly := [(nat_lit 3009, Int.ofNat (nat_lit 5725639190304)), (nat_lit 3011, Int.ofNat (nat_lit 2642598614304))]
theorem block020_data_flat104_step : block020_data_flat104 = (CoefficientMerge.fastMerge block020_data_flat102 block020_data_flat103) := by decide +kernel
theorem block020_data_flat104_original : block020_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded)) := by
  rw [block020_data_flat104_step, block020_data_flat102_original, block020_data_flat103_original]
def block020_data_flat105 : CoefficientMerge.Poly := [(nat_lit 3008, Int.ofNat (nat_lit 6533608444704)), (nat_lit 3009, Int.ofNat (nat_lit 5725639190304)), (nat_lit 3011, Int.ofNat (nat_lit 2642598614304))]
theorem block020_data_flat105_step : block020_data_flat105 = (CoefficientMerge.fastMerge block020_data_flat101 block020_data_flat104) := by decide +kernel
theorem block020_data_flat105_original : block020_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded))) := by
  rw [block020_data_flat105_step, block020_data_flat101_original, block020_data_flat104_original]
def block020_data_flat106 : CoefficientMerge.Poly := [(nat_lit 3006, Int.ofNat (nat_lit 31325586960096)), (nat_lit 3007, Int.ofNat (nat_lit 6649449936096)), (nat_lit 3008, Int.ofNat (nat_lit 6533608444704)), (nat_lit 3009, Int.ofNat (nat_lit 5725639190304)), (nat_lit 3011, Int.ofNat (nat_lit 2642598614304))]
theorem block020_data_flat106_step : block020_data_flat106 = (CoefficientMerge.fastMerge block020_data_flat100 block020_data_flat105) := by decide +kernel
theorem block020_data_flat106_original : block020_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded)))) := by
  rw [block020_data_flat106_step, block020_data_flat100_original, block020_data_flat105_original]
def block020_data_flat107 : CoefficientMerge.Poly := [(nat_lit 3012, Int.ofNat (nat_lit 27375228517824))]
theorem block020_data_flat107_step : block020_data_flat107 = (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) := by decide +kernel
theorem block020_data_flat107_original : block020_data_flat107 = (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) := by
  rw [block020_data_flat107_step]
def block020_data_flat108 : CoefficientMerge.Poly := [(nat_lit 3013, Int.ofNat (nat_lit 15524745667200))]
theorem block020_data_flat108_step : block020_data_flat108 = (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded) := by decide +kernel
theorem block020_data_flat108_original : block020_data_flat108 = (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded) := by
  rw [block020_data_flat108_step]
def block020_data_flat109 : CoefficientMerge.Poly := [(nat_lit 3012, Int.ofNat (nat_lit 27375228517824)), (nat_lit 3013, Int.ofNat (nat_lit 15524745667200))]
theorem block020_data_flat109_step : block020_data_flat109 = (CoefficientMerge.fastMerge block020_data_flat107 block020_data_flat108) := by decide +kernel
theorem block020_data_flat109_original : block020_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded)) := by
  rw [block020_data_flat109_step, block020_data_flat107_original, block020_data_flat108_original]
def block020_data_flat110 : CoefficientMerge.Poly := [(nat_lit 3018, Int.ofNat (nat_lit 6709402022400))]
theorem block020_data_flat110_step : block020_data_flat110 = (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) := by decide +kernel
theorem block020_data_flat110_original : block020_data_flat110 = (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) := by
  rw [block020_data_flat110_step]
def block020_data_flat111 : CoefficientMerge.Poly := [(nat_lit 3030, Int.ofNat (nat_lit 34147372080096))]
theorem block020_data_flat111_step : block020_data_flat111 = (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) := by decide +kernel
theorem block020_data_flat111_original : block020_data_flat111 = (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) := by
  rw [block020_data_flat111_step]
def block020_data_flat112 : CoefficientMerge.Poly := [(nat_lit 3031, Int.ofNat (nat_lit 18942470112192))]
theorem block020_data_flat112_step : block020_data_flat112 = (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded) := by decide +kernel
theorem block020_data_flat112_original : block020_data_flat112 = (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded) := by
  rw [block020_data_flat112_step]
def block020_data_flat113 : CoefficientMerge.Poly := [(nat_lit 3030, Int.ofNat (nat_lit 34147372080096)), (nat_lit 3031, Int.ofNat (nat_lit 18942470112192))]
theorem block020_data_flat113_step : block020_data_flat113 = (CoefficientMerge.fastMerge block020_data_flat111 block020_data_flat112) := by decide +kernel
theorem block020_data_flat113_original : block020_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded)) := by
  rw [block020_data_flat113_step, block020_data_flat111_original, block020_data_flat112_original]
def block020_data_flat114 : CoefficientMerge.Poly := [(nat_lit 3018, Int.ofNat (nat_lit 6709402022400)), (nat_lit 3030, Int.ofNat (nat_lit 34147372080096)), (nat_lit 3031, Int.ofNat (nat_lit 18942470112192))]
theorem block020_data_flat114_step : block020_data_flat114 = (CoefficientMerge.fastMerge block020_data_flat110 block020_data_flat113) := by decide +kernel
theorem block020_data_flat114_original : block020_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded))) := by
  rw [block020_data_flat114_step, block020_data_flat110_original, block020_data_flat113_original]
def block020_data_flat115 : CoefficientMerge.Poly := [(nat_lit 3012, Int.ofNat (nat_lit 27375228517824)), (nat_lit 3013, Int.ofNat (nat_lit 15524745667200)), (nat_lit 3018, Int.ofNat (nat_lit 6709402022400)), (nat_lit 3030, Int.ofNat (nat_lit 34147372080096)), (nat_lit 3031, Int.ofNat (nat_lit 18942470112192))]
theorem block020_data_flat115_step : block020_data_flat115 = (CoefficientMerge.fastMerge block020_data_flat109 block020_data_flat114) := by decide +kernel
theorem block020_data_flat115_original : block020_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded)))) := by
  rw [block020_data_flat115_step, block020_data_flat109_original, block020_data_flat114_original]
def block020_data_flat116 : CoefficientMerge.Poly := [(nat_lit 3006, Int.ofNat (nat_lit 31325586960096)), (nat_lit 3007, Int.ofNat (nat_lit 6649449936096)), (nat_lit 3008, Int.ofNat (nat_lit 6533608444704)), (nat_lit 3009, Int.ofNat (nat_lit 5725639190304)), (nat_lit 3011, Int.ofNat (nat_lit 2642598614304)), (nat_lit 3012, Int.ofNat (nat_lit 27375228517824)), (nat_lit 3013, Int.ofNat (nat_lit 15524745667200)), (nat_lit 3018, Int.ofNat (nat_lit 6709402022400)), (nat_lit 3030, Int.ofNat (nat_lit 34147372080096)), (nat_lit 3031, Int.ofNat (nat_lit 18942470112192))]
theorem block020_data_flat116_step : block020_data_flat116 = (CoefficientMerge.fastMerge block020_data_flat106 block020_data_flat115) := by decide +kernel
theorem block020_data_flat116_original : block020_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded))))) := by
  rw [block020_data_flat116_step, block020_data_flat106_original, block020_data_flat115_original]
def block020_data_flat117 : CoefficientMerge.Poly := [(nat_lit 2804, Int.ofNat (nat_lit 344960709357600)), (nat_lit 2805, Int.ofNat (nat_lit 507525601237200)), (nat_lit 2806, Int.ofNat (nat_lit 377976761080800)), (nat_lit 2807, Int.ofNat (nat_lit 424529099908200)), (nat_lit 2829, Int.ofNat (nat_lit 126080231583600)), (nat_lit 2830, Int.ofNat (nat_lit 174744351860400)), (nat_lit 2831, Int.ofNat (nat_lit 211258137144600)), (nat_lit 2855, Int.ofNat (nat_lit 6690481950600)), (nat_lit 2879, Int.ofNat (nat_lit 49057765684200)), (nat_lit 3005, Int.ofNat (nat_lit 19631255212800)), (nat_lit 3006, Int.ofNat (nat_lit 31325586960096)), (nat_lit 3007, Int.ofNat (nat_lit 6649449936096)), (nat_lit 3008, Int.ofNat (nat_lit 6533608444704)), (nat_lit 3009, Int.ofNat (nat_lit 5725639190304)), (nat_lit 3011, Int.ofNat (nat_lit 2642598614304)), (nat_lit 3012, Int.ofNat (nat_lit 27375228517824)), (nat_lit 3013, Int.ofNat (nat_lit 15524745667200)), (nat_lit 3018, Int.ofNat (nat_lit 6709402022400)), (nat_lit 3030, Int.ofNat (nat_lit 34147372080096)), (nat_lit 3031, Int.ofNat (nat_lit 18942470112192))]
theorem block020_data_flat117_step : block020_data_flat117 = (CoefficientMerge.fastMerge block020_data_flat097 block020_data_flat116) := by decide +kernel
theorem block020_data_flat117_original : block020_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded)))))) := by
  rw [block020_data_flat117_step, block020_data_flat097_original, block020_data_flat116_original]
def block020_data_flat118 : CoefficientMerge.Poly := [(nat_lit 3036, Int.ofNat (nat_lit 25753222645920))]
theorem block020_data_flat118_step : block020_data_flat118 = (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) := by decide +kernel
theorem block020_data_flat118_original : block020_data_flat118 = (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) := by
  rw [block020_data_flat118_step]
def block020_data_flat119 : CoefficientMerge.Poly := [(nat_lit 3037, Int.ofNat (nat_lit 16985780371296))]
theorem block020_data_flat119_step : block020_data_flat119 = (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded) := by decide +kernel
theorem block020_data_flat119_original : block020_data_flat119 = (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded) := by
  rw [block020_data_flat119_step]
def block020_data_flat120 : CoefficientMerge.Poly := [(nat_lit 3036, Int.ofNat (nat_lit 25753222645920)), (nat_lit 3037, Int.ofNat (nat_lit 16985780371296))]
theorem block020_data_flat120_step : block020_data_flat120 = (CoefficientMerge.fastMerge block020_data_flat118 block020_data_flat119) := by decide +kernel
theorem block020_data_flat120_original : block020_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded)) := by
  rw [block020_data_flat120_step, block020_data_flat118_original, block020_data_flat119_original]
def block020_data_flat121 : CoefficientMerge.Poly := [(nat_lit 3038, Int.ofNat (nat_lit 4544075280096))]
theorem block020_data_flat121_step : block020_data_flat121 = (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) := by decide +kernel
theorem block020_data_flat121_original : block020_data_flat121 = (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) := by
  rw [block020_data_flat121_step]
def block020_data_flat122 : CoefficientMerge.Poly := [(nat_lit 3039, Int.ofNat (nat_lit 7627115856096))]
theorem block020_data_flat122_step : block020_data_flat122 = (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) := by decide +kernel
theorem block020_data_flat122_original : block020_data_flat122 = (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) := by
  rw [block020_data_flat122_step]
def block020_data_flat123 : CoefficientMerge.Poly := [(nat_lit 3040, Int.ofNat (nat_lit 10710156432096))]
theorem block020_data_flat123_step : block020_data_flat123 = (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded) := by decide +kernel
theorem block020_data_flat123_original : block020_data_flat123 = (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded) := by
  rw [block020_data_flat123_step]
def block020_data_flat124 : CoefficientMerge.Poly := [(nat_lit 3039, Int.ofNat (nat_lit 7627115856096)), (nat_lit 3040, Int.ofNat (nat_lit 10710156432096))]
theorem block020_data_flat124_step : block020_data_flat124 = (CoefficientMerge.fastMerge block020_data_flat122 block020_data_flat123) := by decide +kernel
theorem block020_data_flat124_original : block020_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded)) := by
  rw [block020_data_flat124_step, block020_data_flat122_original, block020_data_flat123_original]
def block020_data_flat125 : CoefficientMerge.Poly := [(nat_lit 3038, Int.ofNat (nat_lit 4544075280096)), (nat_lit 3039, Int.ofNat (nat_lit 7627115856096)), (nat_lit 3040, Int.ofNat (nat_lit 10710156432096))]
theorem block020_data_flat125_step : block020_data_flat125 = (CoefficientMerge.fastMerge block020_data_flat121 block020_data_flat124) := by decide +kernel
theorem block020_data_flat125_original : block020_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded))) := by
  rw [block020_data_flat125_step, block020_data_flat121_original, block020_data_flat124_original]
def block020_data_flat126 : CoefficientMerge.Poly := [(nat_lit 3036, Int.ofNat (nat_lit 25753222645920)), (nat_lit 3037, Int.ofNat (nat_lit 16985780371296)), (nat_lit 3038, Int.ofNat (nat_lit 4544075280096)), (nat_lit 3039, Int.ofNat (nat_lit 7627115856096)), (nat_lit 3040, Int.ofNat (nat_lit 10710156432096))]
theorem block020_data_flat126_step : block020_data_flat126 = (CoefficientMerge.fastMerge block020_data_flat120 block020_data_flat125) := by decide +kernel
theorem block020_data_flat126_original : block020_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded)))) := by
  rw [block020_data_flat126_step, block020_data_flat120_original, block020_data_flat125_original]
def block020_data_flat127 : CoefficientMerge.Poly := [(nat_lit 3041, Int.ofNat (nat_lit 13793197008096))]
theorem block020_data_flat127_step : block020_data_flat127 = (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) := by decide +kernel
theorem block020_data_flat127_original : block020_data_flat127 = (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) := by
  rw [block020_data_flat127_step]
def block020_data_flat128 : CoefficientMerge.Poly := [(nat_lit 3042, Int.ofNat (nat_lit 10047950030448))]
theorem block020_data_flat128_step : block020_data_flat128 = (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded) := by decide +kernel
theorem block020_data_flat128_original : block020_data_flat128 = (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded) := by
  rw [block020_data_flat128_step]
def block020_data_flat129 : CoefficientMerge.Poly := [(nat_lit 3041, Int.ofNat (nat_lit 13793197008096)), (nat_lit 3042, Int.ofNat (nat_lit 10047950030448))]
theorem block020_data_flat129_step : block020_data_flat129 = (CoefficientMerge.fastMerge block020_data_flat127 block020_data_flat128) := by decide +kernel
theorem block020_data_flat129_original : block020_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded)) := by
  rw [block020_data_flat129_step, block020_data_flat127_original, block020_data_flat128_original]
def block020_data_flat130 : CoefficientMerge.Poly := [(nat_lit 3043, Int.ofNat (nat_lit 5544496742400))]
theorem block020_data_flat130_step : block020_data_flat130 = (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) := by decide +kernel
theorem block020_data_flat130_original : block020_data_flat130 = (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) := by
  rw [block020_data_flat130_step]
def block020_data_flat131 : CoefficientMerge.Poly := [(nat_lit 3044, Int.ofNat (nat_lit 7750445476752))]
theorem block020_data_flat131_step : block020_data_flat131 = (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) := by decide +kernel
theorem block020_data_flat131_original : block020_data_flat131 = (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) := by
  rw [block020_data_flat131_step]
def block020_data_flat132 : CoefficientMerge.Poly := [(nat_lit 3045, Int.ofNat (nat_lit 48376733335128))]
theorem block020_data_flat132_step : block020_data_flat132 = (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded) := by decide +kernel
theorem block020_data_flat132_original : block020_data_flat132 = (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded) := by
  rw [block020_data_flat132_step]
def block020_data_flat133 : CoefficientMerge.Poly := [(nat_lit 3044, Int.ofNat (nat_lit 7750445476752)), (nat_lit 3045, Int.ofNat (nat_lit 48376733335128))]
theorem block020_data_flat133_step : block020_data_flat133 = (CoefficientMerge.fastMerge block020_data_flat131 block020_data_flat132) := by decide +kernel
theorem block020_data_flat133_original : block020_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded)) := by
  rw [block020_data_flat133_step, block020_data_flat131_original, block020_data_flat132_original]
def block020_data_flat134 : CoefficientMerge.Poly := [(nat_lit 3043, Int.ofNat (nat_lit 5544496742400)), (nat_lit 3044, Int.ofNat (nat_lit 7750445476752)), (nat_lit 3045, Int.ofNat (nat_lit 48376733335128))]
theorem block020_data_flat134_step : block020_data_flat134 = (CoefficientMerge.fastMerge block020_data_flat130 block020_data_flat133) := by decide +kernel
theorem block020_data_flat134_original : block020_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded))) := by
  rw [block020_data_flat134_step, block020_data_flat130_original, block020_data_flat133_original]
def block020_data_flat135 : CoefficientMerge.Poly := [(nat_lit 3041, Int.ofNat (nat_lit 13793197008096)), (nat_lit 3042, Int.ofNat (nat_lit 10047950030448)), (nat_lit 3043, Int.ofNat (nat_lit 5544496742400)), (nat_lit 3044, Int.ofNat (nat_lit 7750445476752)), (nat_lit 3045, Int.ofNat (nat_lit 48376733335128))]
theorem block020_data_flat135_step : block020_data_flat135 = (CoefficientMerge.fastMerge block020_data_flat129 block020_data_flat134) := by decide +kernel
theorem block020_data_flat135_original : block020_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded)))) := by
  rw [block020_data_flat135_step, block020_data_flat129_original, block020_data_flat134_original]
def block020_data_flat136 : CoefficientMerge.Poly := [(nat_lit 3036, Int.ofNat (nat_lit 25753222645920)), (nat_lit 3037, Int.ofNat (nat_lit 16985780371296)), (nat_lit 3038, Int.ofNat (nat_lit 4544075280096)), (nat_lit 3039, Int.ofNat (nat_lit 7627115856096)), (nat_lit 3040, Int.ofNat (nat_lit 10710156432096)), (nat_lit 3041, Int.ofNat (nat_lit 13793197008096)), (nat_lit 3042, Int.ofNat (nat_lit 10047950030448)), (nat_lit 3043, Int.ofNat (nat_lit 5544496742400)), (nat_lit 3044, Int.ofNat (nat_lit 7750445476752)), (nat_lit 3045, Int.ofNat (nat_lit 48376733335128))]
theorem block020_data_flat136_step : block020_data_flat136 = (CoefficientMerge.fastMerge block020_data_flat126 block020_data_flat135) := by decide +kernel
theorem block020_data_flat136_original : block020_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded))))) := by
  rw [block020_data_flat136_step, block020_data_flat126_original, block020_data_flat135_original]
def block020_data_flat137 : CoefficientMerge.Poly := [(nat_lit 3046, Int.ofNat (nat_lit 89003021193504))]
theorem block020_data_flat137_step : block020_data_flat137 = (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) := by decide +kernel
theorem block020_data_flat137_original : block020_data_flat137 = (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) := by
  rw [block020_data_flat137_step]
def block020_data_flat138 : CoefficientMerge.Poly := [(nat_lit 3047, Int.ofNat (nat_lit 136178880879492))]
theorem block020_data_flat138_step : block020_data_flat138 = (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded) := by decide +kernel
theorem block020_data_flat138_original : block020_data_flat138 = (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded) := by
  rw [block020_data_flat138_step]
def block020_data_flat139 : CoefficientMerge.Poly := [(nat_lit 3046, Int.ofNat (nat_lit 89003021193504)), (nat_lit 3047, Int.ofNat (nat_lit 136178880879492))]
theorem block020_data_flat139_step : block020_data_flat139 = (CoefficientMerge.fastMerge block020_data_flat137 block020_data_flat138) := by decide +kernel
theorem block020_data_flat139_original : block020_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded)) := by
  rw [block020_data_flat139_step, block020_data_flat137_original, block020_data_flat138_original]
def block020_data_flat140 : CoefficientMerge.Poly := [(nat_lit 3055, Int.ofNat (nat_lit 12542463216096))]
theorem block020_data_flat140_step : block020_data_flat140 = (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) := by decide +kernel
theorem block020_data_flat140_original : block020_data_flat140 = (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) := by
  rw [block020_data_flat140_step]
def block020_data_flat141 : CoefficientMerge.Poly := [(nat_lit 3056, Int.ofNat (nat_lit 14392247654400))]
theorem block020_data_flat141_step : block020_data_flat141 = (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) := by decide +kernel
theorem block020_data_flat141_original : block020_data_flat141 = (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) := by
  rw [block020_data_flat141_step]
def block020_data_flat142 : CoefficientMerge.Poly := [(nat_lit 3059, Int.ofNat (nat_lit 4124895667200))]
theorem block020_data_flat142_step : block020_data_flat142 = (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded) := by decide +kernel
theorem block020_data_flat142_original : block020_data_flat142 = (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded) := by
  rw [block020_data_flat142_step]
def block020_data_flat143 : CoefficientMerge.Poly := [(nat_lit 3056, Int.ofNat (nat_lit 14392247654400)), (nat_lit 3059, Int.ofNat (nat_lit 4124895667200))]
theorem block020_data_flat143_step : block020_data_flat143 = (CoefficientMerge.fastMerge block020_data_flat141 block020_data_flat142) := by decide +kernel
theorem block020_data_flat143_original : block020_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded)) := by
  rw [block020_data_flat143_step, block020_data_flat141_original, block020_data_flat142_original]
def block020_data_flat144 : CoefficientMerge.Poly := [(nat_lit 3055, Int.ofNat (nat_lit 12542463216096)), (nat_lit 3056, Int.ofNat (nat_lit 14392247654400)), (nat_lit 3059, Int.ofNat (nat_lit 4124895667200))]
theorem block020_data_flat144_step : block020_data_flat144 = (CoefficientMerge.fastMerge block020_data_flat140 block020_data_flat143) := by decide +kernel
theorem block020_data_flat144_original : block020_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded))) := by
  rw [block020_data_flat144_step, block020_data_flat140_original, block020_data_flat143_original]
def block020_data_flat145 : CoefficientMerge.Poly := [(nat_lit 3046, Int.ofNat (nat_lit 89003021193504)), (nat_lit 3047, Int.ofNat (nat_lit 136178880879492)), (nat_lit 3055, Int.ofNat (nat_lit 12542463216096)), (nat_lit 3056, Int.ofNat (nat_lit 14392247654400)), (nat_lit 3059, Int.ofNat (nat_lit 4124895667200))]
theorem block020_data_flat145_step : block020_data_flat145 = (CoefficientMerge.fastMerge block020_data_flat139 block020_data_flat144) := by decide +kernel
theorem block020_data_flat145_original : block020_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded)))) := by
  rw [block020_data_flat145_step, block020_data_flat139_original, block020_data_flat144_original]
def block020_data_flat146 : CoefficientMerge.Poly := [(nat_lit 3060, Int.ofNat (nat_lit 34003013980320))]
theorem block020_data_flat146_step : block020_data_flat146 = (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) := by decide +kernel
theorem block020_data_flat146_original : block020_data_flat146 = (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) := by
  rw [block020_data_flat146_step]
def block020_data_flat147 : CoefficientMerge.Poly := [(nat_lit 3061, Int.ofNat (nat_lit 27298019539296))]
theorem block020_data_flat147_step : block020_data_flat147 = (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded) := by decide +kernel
theorem block020_data_flat147_original : block020_data_flat147 = (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded) := by
  rw [block020_data_flat147_step]
def block020_data_flat148 : CoefficientMerge.Poly := [(nat_lit 3060, Int.ofNat (nat_lit 34003013980320)), (nat_lit 3061, Int.ofNat (nat_lit 27298019539296))]
theorem block020_data_flat148_step : block020_data_flat148 = (CoefficientMerge.fastMerge block020_data_flat146 block020_data_flat147) := by decide +kernel
theorem block020_data_flat148_original : block020_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded)) := by
  rw [block020_data_flat148_step, block020_data_flat146_original, block020_data_flat147_original]
def block020_data_flat149 : CoefficientMerge.Poly := [(nat_lit 3062, Int.ofNat (nat_lit 16918762281696))]
theorem block020_data_flat149_step : block020_data_flat149 = (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) := by decide +kernel
theorem block020_data_flat149_original : block020_data_flat149 = (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) := by
  rw [block020_data_flat149_step]
def block020_data_flat150 : CoefficientMerge.Poly := [(nat_lit 3063, Int.ofNat (nat_lit 22064250691296))]
theorem block020_data_flat150_step : block020_data_flat150 = (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) := by decide +kernel
theorem block020_data_flat150_original : block020_data_flat150 = (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) := by
  rw [block020_data_flat150_step]
def block020_data_flat151 : CoefficientMerge.Poly := [(nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
theorem block020_data_flat151_step : block020_data_flat151 = (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded) := by decide +kernel
theorem block020_data_flat151_original : block020_data_flat151 = (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded) := by
  rw [block020_data_flat151_step]
def block020_data_flat152 : CoefficientMerge.Poly := [(nat_lit 3063, Int.ofNat (nat_lit 22064250691296)), (nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
theorem block020_data_flat152_step : block020_data_flat152 = (CoefficientMerge.fastMerge block020_data_flat150 block020_data_flat151) := by decide +kernel
theorem block020_data_flat152_original : block020_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded)) := by
  rw [block020_data_flat152_step, block020_data_flat150_original, block020_data_flat151_original]
def block020_data_flat153 : CoefficientMerge.Poly := [(nat_lit 3062, Int.ofNat (nat_lit 16918762281696)), (nat_lit 3063, Int.ofNat (nat_lit 22064250691296)), (nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
theorem block020_data_flat153_step : block020_data_flat153 = (CoefficientMerge.fastMerge block020_data_flat149 block020_data_flat152) := by decide +kernel
theorem block020_data_flat153_original : block020_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded))) := by
  rw [block020_data_flat153_step, block020_data_flat149_original, block020_data_flat152_original]
def block020_data_flat154 : CoefficientMerge.Poly := [(nat_lit 3060, Int.ofNat (nat_lit 34003013980320)), (nat_lit 3061, Int.ofNat (nat_lit 27298019539296)), (nat_lit 3062, Int.ofNat (nat_lit 16918762281696)), (nat_lit 3063, Int.ofNat (nat_lit 22064250691296)), (nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
theorem block020_data_flat154_step : block020_data_flat154 = (CoefficientMerge.fastMerge block020_data_flat148 block020_data_flat153) := by decide +kernel
theorem block020_data_flat154_original : block020_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded)))) := by
  rw [block020_data_flat154_step, block020_data_flat148_original, block020_data_flat153_original]
def block020_data_flat155 : CoefficientMerge.Poly := [(nat_lit 3046, Int.ofNat (nat_lit 89003021193504)), (nat_lit 3047, Int.ofNat (nat_lit 136178880879492)), (nat_lit 3055, Int.ofNat (nat_lit 12542463216096)), (nat_lit 3056, Int.ofNat (nat_lit 14392247654400)), (nat_lit 3059, Int.ofNat (nat_lit 4124895667200)), (nat_lit 3060, Int.ofNat (nat_lit 34003013980320)), (nat_lit 3061, Int.ofNat (nat_lit 27298019539296)), (nat_lit 3062, Int.ofNat (nat_lit 16918762281696)), (nat_lit 3063, Int.ofNat (nat_lit 22064250691296)), (nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
theorem block020_data_flat155_step : block020_data_flat155 = (CoefficientMerge.fastMerge block020_data_flat145 block020_data_flat154) := by decide +kernel
theorem block020_data_flat155_original : block020_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded))))) := by
  rw [block020_data_flat155_step, block020_data_flat145_original, block020_data_flat154_original]
def block020_data_flat156 : CoefficientMerge.Poly := [(nat_lit 3036, Int.ofNat (nat_lit 25753222645920)), (nat_lit 3037, Int.ofNat (nat_lit 16985780371296)), (nat_lit 3038, Int.ofNat (nat_lit 4544075280096)), (nat_lit 3039, Int.ofNat (nat_lit 7627115856096)), (nat_lit 3040, Int.ofNat (nat_lit 10710156432096)), (nat_lit 3041, Int.ofNat (nat_lit 13793197008096)), (nat_lit 3042, Int.ofNat (nat_lit 10047950030448)), (nat_lit 3043, Int.ofNat (nat_lit 5544496742400)), (nat_lit 3044, Int.ofNat (nat_lit 7750445476752)), (nat_lit 3045, Int.ofNat (nat_lit 48376733335128)), (nat_lit 3046, Int.ofNat (nat_lit 89003021193504)), (nat_lit 3047, Int.ofNat (nat_lit 136178880879492)), (nat_lit 3055, Int.ofNat (nat_lit 12542463216096)), (nat_lit 3056, Int.ofNat (nat_lit 14392247654400)), (nat_lit 3059, Int.ofNat (nat_lit 4124895667200)), (nat_lit 3060, Int.ofNat (nat_lit 34003013980320)), (nat_lit 3061, Int.ofNat (nat_lit 27298019539296)), (nat_lit 3062, Int.ofNat (nat_lit 16918762281696)), (nat_lit 3063, Int.ofNat (nat_lit 22064250691296)), (nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
theorem block020_data_flat156_step : block020_data_flat156 = (CoefficientMerge.fastMerge block020_data_flat136 block020_data_flat155) := by decide +kernel
theorem block020_data_flat156_original : block020_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded)))))) := by
  rw [block020_data_flat156_step, block020_data_flat136_original, block020_data_flat155_original]
def block020_data_flat157 : CoefficientMerge.Poly := [(nat_lit 2804, Int.ofNat (nat_lit 344960709357600)), (nat_lit 2805, Int.ofNat (nat_lit 507525601237200)), (nat_lit 2806, Int.ofNat (nat_lit 377976761080800)), (nat_lit 2807, Int.ofNat (nat_lit 424529099908200)), (nat_lit 2829, Int.ofNat (nat_lit 126080231583600)), (nat_lit 2830, Int.ofNat (nat_lit 174744351860400)), (nat_lit 2831, Int.ofNat (nat_lit 211258137144600)), (nat_lit 2855, Int.ofNat (nat_lit 6690481950600)), (nat_lit 2879, Int.ofNat (nat_lit 49057765684200)), (nat_lit 3005, Int.ofNat (nat_lit 19631255212800)), (nat_lit 3006, Int.ofNat (nat_lit 31325586960096)), (nat_lit 3007, Int.ofNat (nat_lit 6649449936096)), (nat_lit 3008, Int.ofNat (nat_lit 6533608444704)), (nat_lit 3009, Int.ofNat (nat_lit 5725639190304)), (nat_lit 3011, Int.ofNat (nat_lit 2642598614304)), (nat_lit 3012, Int.ofNat (nat_lit 27375228517824)), (nat_lit 3013, Int.ofNat (nat_lit 15524745667200)), (nat_lit 3018, Int.ofNat (nat_lit 6709402022400)), (nat_lit 3030, Int.ofNat (nat_lit 34147372080096)), (nat_lit 3031, Int.ofNat (nat_lit 18942470112192)), (nat_lit 3036, Int.ofNat (nat_lit 25753222645920)), (nat_lit 3037, Int.ofNat (nat_lit 16985780371296)), (nat_lit 3038, Int.ofNat (nat_lit 4544075280096)), (nat_lit 3039, Int.ofNat (nat_lit 7627115856096)), (nat_lit 3040, Int.ofNat (nat_lit 10710156432096)), (nat_lit 3041, Int.ofNat (nat_lit 13793197008096)), (nat_lit 3042, Int.ofNat (nat_lit 10047950030448)), (nat_lit 3043, Int.ofNat (nat_lit 5544496742400)), (nat_lit 3044, Int.ofNat (nat_lit 7750445476752)), (nat_lit 3045, Int.ofNat (nat_lit 48376733335128)), (nat_lit 3046, Int.ofNat (nat_lit 89003021193504)), (nat_lit 3047, Int.ofNat (nat_lit 136178880879492)), (nat_lit 3055, Int.ofNat (nat_lit 12542463216096)), (nat_lit 3056, Int.ofNat (nat_lit 14392247654400)), (nat_lit 3059, Int.ofNat (nat_lit 4124895667200)), (nat_lit 3060, Int.ofNat (nat_lit 34003013980320)), (nat_lit 3061, Int.ofNat (nat_lit 27298019539296)), (nat_lit 3062, Int.ofNat (nat_lit 16918762281696)), (nat_lit 3063, Int.ofNat (nat_lit 22064250691296)), (nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
theorem block020_data_flat157_step : block020_data_flat157 = (CoefficientMerge.fastMerge block020_data_flat117 block020_data_flat156) := by decide +kernel
theorem block020_data_flat157_original : block020_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded))))))) := by
  rw [block020_data_flat157_step, block020_data_flat117_original, block020_data_flat156_original]
def block020_data_flat158 : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 330838724412000)), (nat_lit 2660, Int.ofNat (nat_lit 432262826251200)), (nat_lit 2661, Int.ofNat (nat_lit 416309943672000)), (nat_lit 2662, Int.ofNat (nat_lit 457356545604000)), (nat_lit 2663, Int.ofNat (nat_lit 510982927610400)), (nat_lit 2679, Int.ofNat (nat_lit 208278237081600)), (nat_lit 2680, Int.ofNat (nat_lit 366404392166400)), (nat_lit 2681, Int.ofNat (nat_lit 344185237670400)), (nat_lit 2682, Int.ofNat (nat_lit 380141158118400)), (nat_lit 2683, Int.ofNat (nat_lit 346793499662400)), (nat_lit 2684, Int.ofNat (nat_lit 472461551755200)), (nat_lit 2685, Int.ofNat (nat_lit 461611632888000)), (nat_lit 2686, Int.ofNat (nat_lit 436957939454400)), (nat_lit 2687, Int.ofNat (nat_lit 482678754667200)), (nat_lit 2704, Int.ofNat (nat_lit 205392356467200)), (nat_lit 2705, Int.ofNat (nat_lit 377339038272000)), (nat_lit 2706, Int.ofNat (nat_lit 386488935705600)), (nat_lit 2707, Int.ofNat (nat_lit 358244240961600)), (nat_lit 2708, Int.ofNat (nat_lit 489015256766400)), (nat_lit 2709, Int.ofNat (nat_lit 483268301611200)), (nat_lit 2710, Int.ofNat (nat_lit 405924574910400)), (nat_lit 2711, Int.ofNat (nat_lit 533283144811200)), (nat_lit 2729, Int.ofNat (nat_lit 214421767257600)), (nat_lit 2730, Int.ofNat (nat_lit 415025907206400)), (nat_lit 2731, Int.ofNat (nat_lit 389560459176000)), (nat_lit 2732, Int.ofNat (nat_lit 523110721694400)), (nat_lit 2733, Int.ofNat (nat_lit 521304871752000)), (nat_lit 2734, Int.ofNat (nat_lit 446778567345600)), (nat_lit 2735, Int.ofNat (nat_lit 578659171708800)), (nat_lit 2754, Int.ofNat (nat_lit 249088416192000)), (nat_lit 2755, Int.ofNat (nat_lit 449248020026400)), (nat_lit 2756, Int.ofNat (nat_lit 620668861394400)), (nat_lit 2757, Int.ofNat (nat_lit 582988918831200)), (nat_lit 2758, Int.ofNat (nat_lit 416071587909600)), (nat_lit 2759, Int.ofNat (nat_lit 578049932930400)), (nat_lit 2779, Int.ofNat (nat_lit 163652046243840)), (nat_lit 2780, Int.ofNat (nat_lit 483786370015200)), (nat_lit 2781, Int.ofNat (nat_lit 464046353038800)), (nat_lit 2782, Int.ofNat (nat_lit 352564509192000)), (nat_lit 2783, Int.ofNat (nat_lit 361867931119800)), (nat_lit 2804, Int.ofNat (nat_lit 344960709357600)), (nat_lit 2805, Int.ofNat (nat_lit 507525601237200)), (nat_lit 2806, Int.ofNat (nat_lit 377976761080800)), (nat_lit 2807, Int.ofNat (nat_lit 424529099908200)), (nat_lit 2829, Int.ofNat (nat_lit 126080231583600)), (nat_lit 2830, Int.ofNat (nat_lit 174744351860400)), (nat_lit 2831, Int.ofNat (nat_lit 211258137144600)), (nat_lit 2855, Int.ofNat (nat_lit 6690481950600)), (nat_lit 2879, Int.ofNat (nat_lit 49057765684200)), (nat_lit 3005, Int.ofNat (nat_lit 19631255212800)), (nat_lit 3006, Int.ofNat (nat_lit 31325586960096)), (nat_lit 3007, Int.ofNat (nat_lit 6649449936096)), (nat_lit 3008, Int.ofNat (nat_lit 6533608444704)), (nat_lit 3009, Int.ofNat (nat_lit 5725639190304)), (nat_lit 3011, Int.ofNat (nat_lit 2642598614304)), (nat_lit 3012, Int.ofNat (nat_lit 27375228517824)), (nat_lit 3013, Int.ofNat (nat_lit 15524745667200)), (nat_lit 3018, Int.ofNat (nat_lit 6709402022400)), (nat_lit 3030, Int.ofNat (nat_lit 34147372080096)), (nat_lit 3031, Int.ofNat (nat_lit 18942470112192)), (nat_lit 3036, Int.ofNat (nat_lit 25753222645920)), (nat_lit 3037, Int.ofNat (nat_lit 16985780371296)), (nat_lit 3038, Int.ofNat (nat_lit 4544075280096)), (nat_lit 3039, Int.ofNat (nat_lit 7627115856096)), (nat_lit 3040, Int.ofNat (nat_lit 10710156432096)), (nat_lit 3041, Int.ofNat (nat_lit 13793197008096)), (nat_lit 3042, Int.ofNat (nat_lit 10047950030448)), (nat_lit 3043, Int.ofNat (nat_lit 5544496742400)), (nat_lit 3044, Int.ofNat (nat_lit 7750445476752)), (nat_lit 3045, Int.ofNat (nat_lit 48376733335128)), (nat_lit 3046, Int.ofNat (nat_lit 89003021193504)), (nat_lit 3047, Int.ofNat (nat_lit 136178880879492)), (nat_lit 3055, Int.ofNat (nat_lit 12542463216096)), (nat_lit 3056, Int.ofNat (nat_lit 14392247654400)), (nat_lit 3059, Int.ofNat (nat_lit 4124895667200)), (nat_lit 3060, Int.ofNat (nat_lit 34003013980320)), (nat_lit 3061, Int.ofNat (nat_lit 27298019539296)), (nat_lit 3062, Int.ofNat (nat_lit 16918762281696)), (nat_lit 3063, Int.ofNat (nat_lit 22064250691296)), (nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
theorem block020_data_flat158_step : block020_data_flat158 = (CoefficientMerge.fastMerge block020_data_flat078 block020_data_flat157) := by decide +kernel
theorem block020_data_flat158_original : block020_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded)))))))) := by
  rw [block020_data_flat158_step, block020_data_flat078_original, block020_data_flat157_original]
def block020_data_flat159 : CoefficientMerge.Poly := [(nat_lit 2659, Int.ofNat (nat_lit 330838724412000)), (nat_lit 2660, Int.ofNat (nat_lit 432262826251200)), (nat_lit 2661, Int.ofNat (nat_lit 416309943672000)), (nat_lit 2662, Int.ofNat (nat_lit 457356545604000)), (nat_lit 2663, Int.ofNat (nat_lit 510982927610400)), (nat_lit 2679, Int.ofNat (nat_lit 208278237081600)), (nat_lit 2680, Int.ofNat (nat_lit 366404392166400)), (nat_lit 2681, Int.ofNat (nat_lit 344185237670400)), (nat_lit 2682, Int.ofNat (nat_lit 380141158118400)), (nat_lit 2683, Int.ofNat (nat_lit 346793499662400)), (nat_lit 2684, Int.ofNat (nat_lit 472461551755200)), (nat_lit 2685, Int.ofNat (nat_lit 461611632888000)), (nat_lit 2686, Int.ofNat (nat_lit 436957939454400)), (nat_lit 2687, Int.ofNat (nat_lit 482678754667200)), (nat_lit 2704, Int.ofNat (nat_lit 205392356467200)), (nat_lit 2705, Int.ofNat (nat_lit 377339038272000)), (nat_lit 2706, Int.ofNat (nat_lit 386488935705600)), (nat_lit 2707, Int.ofNat (nat_lit 358244240961600)), (nat_lit 2708, Int.ofNat (nat_lit 489015256766400)), (nat_lit 2709, Int.ofNat (nat_lit 483268301611200)), (nat_lit 2710, Int.ofNat (nat_lit 405924574910400)), (nat_lit 2711, Int.ofNat (nat_lit 533283144811200)), (nat_lit 2729, Int.ofNat (nat_lit 214421767257600)), (nat_lit 2730, Int.ofNat (nat_lit 415025907206400)), (nat_lit 2731, Int.ofNat (nat_lit 389560459176000)), (nat_lit 2732, Int.ofNat (nat_lit 523110721694400)), (nat_lit 2733, Int.ofNat (nat_lit 521304871752000)), (nat_lit 2734, Int.ofNat (nat_lit 446778567345600)), (nat_lit 2735, Int.ofNat (nat_lit 578659171708800)), (nat_lit 2754, Int.ofNat (nat_lit 249088416192000)), (nat_lit 2755, Int.ofNat (nat_lit 449248020026400)), (nat_lit 2756, Int.ofNat (nat_lit 620668861394400)), (nat_lit 2757, Int.ofNat (nat_lit 582988918831200)), (nat_lit 2758, Int.ofNat (nat_lit 416071587909600)), (nat_lit 2759, Int.ofNat (nat_lit 578049932930400)), (nat_lit 2779, Int.ofNat (nat_lit 163652046243840)), (nat_lit 2780, Int.ofNat (nat_lit 483786370015200)), (nat_lit 2781, Int.ofNat (nat_lit 464046353038800)), (nat_lit 2782, Int.ofNat (nat_lit 352564509192000)), (nat_lit 2783, Int.ofNat (nat_lit 361867931119800)), (nat_lit 2804, Int.ofNat (nat_lit 344960709357600)), (nat_lit 2805, Int.ofNat (nat_lit 507525601237200)), (nat_lit 2806, Int.ofNat (nat_lit 377976761080800)), (nat_lit 2807, Int.ofNat (nat_lit 424529099908200)), (nat_lit 2829, Int.ofNat (nat_lit 126080231583600)), (nat_lit 2830, Int.ofNat (nat_lit 174744351860400)), (nat_lit 2831, Int.ofNat (nat_lit 211258137144600)), (nat_lit 2855, Int.ofNat (nat_lit 6690481950600)), (nat_lit 2879, Int.ofNat (nat_lit 49057765684200)), (nat_lit 3005, Int.ofNat (nat_lit 19631255212800)), (nat_lit 3006, Int.ofNat (nat_lit 31325586960096)), (nat_lit 3007, Int.ofNat (nat_lit 6649449936096)), (nat_lit 3008, Int.ofNat (nat_lit 6533608444704)), (nat_lit 3009, Int.ofNat (nat_lit 5725639190304)), (nat_lit 3011, Int.ofNat (nat_lit 2642598614304)), (nat_lit 3012, Int.ofNat (nat_lit 27375228517824)), (nat_lit 3013, Int.ofNat (nat_lit 15524745667200)), (nat_lit 3018, Int.ofNat (nat_lit 6709402022400)), (nat_lit 3030, Int.ofNat (nat_lit 34147372080096)), (nat_lit 3031, Int.ofNat (nat_lit 18942470112192)), (nat_lit 3036, Int.ofNat (nat_lit 25753222645920)), (nat_lit 3037, Int.ofNat (nat_lit 16985780371296)), (nat_lit 3038, Int.ofNat (nat_lit 4544075280096)), (nat_lit 3039, Int.ofNat (nat_lit 7627115856096)), (nat_lit 3040, Int.ofNat (nat_lit 10710156432096)), (nat_lit 3041, Int.ofNat (nat_lit 13793197008096)), (nat_lit 3042, Int.ofNat (nat_lit 10047950030448)), (nat_lit 3043, Int.ofNat (nat_lit 5544496742400)), (nat_lit 3044, Int.ofNat (nat_lit 7750445476752)), (nat_lit 3045, Int.ofNat (nat_lit 48376733335128)), (nat_lit 3046, Int.ofNat (nat_lit 89003021193504)), (nat_lit 3047, Int.ofNat (nat_lit 136178880879492)), (nat_lit 3055, Int.ofNat (nat_lit 12542463216096)), (nat_lit 3056, Int.ofNat (nat_lit 14392247654400)), (nat_lit 3059, Int.ofNat (nat_lit 4124895667200)), (nat_lit 3060, Int.ofNat (nat_lit 34003013980320)), (nat_lit 3061, Int.ofNat (nat_lit 27298019539296)), (nat_lit 3062, Int.ofNat (nat_lit 16918762281696)), (nat_lit 3063, Int.ofNat (nat_lit 22064250691296)), (nat_lit 3064, Int.ofNat (nat_lit 27209739100896))]
theorem block020_data_flat159_step : block020_data_flat159 = (CoefficientMerge.trim block020_data_flat158) := by decide +kernel
theorem block020_data_flat159_original : block020_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded))))))))) := by
  rw [block020_data_flat159_step, block020_data_flat158_original]
theorem block020_data : block020 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330838724412000 : Int) atom1409Coded) (CoefficientMerge.scale (432262826251200 : Int) atom1410Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416309943672000 : Int) atom1411Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457356545604000 : Int) atom1412Coded) (CoefficientMerge.scale (510982927610400 : Int) atom1413Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208278237081600 : Int) atom1414Coded) (CoefficientMerge.scale (366404392166400 : Int) atom1415Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (344185237670400 : Int) atom1416Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (380141158118400 : Int) atom1417Coded) (CoefficientMerge.scale (346793499662400 : Int) atom1418Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472461551755200 : Int) atom1419Coded) (CoefficientMerge.scale (461611632888000 : Int) atom1420Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436957939454400 : Int) atom1421Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (482678754667200 : Int) atom1422Coded) (CoefficientMerge.scale (205392356467200 : Int) atom1423Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (377339038272000 : Int) atom1424Coded) (CoefficientMerge.scale (386488935705600 : Int) atom1425Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358244240961600 : Int) atom1426Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (489015256766400 : Int) atom1427Coded) (CoefficientMerge.scale (483268301611200 : Int) atom1428Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405924574910400 : Int) atom1429Coded) (CoefficientMerge.scale (533283144811200 : Int) atom1430Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (214421767257600 : Int) atom1431Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (415025907206400 : Int) atom1432Coded) (CoefficientMerge.scale (389560459176000 : Int) atom1433Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523110721694400 : Int) atom1434Coded) (CoefficientMerge.scale (521304871752000 : Int) atom1435Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (446778567345600 : Int) atom1436Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (578659171708800 : Int) atom1437Coded) (CoefficientMerge.scale (249088416192000 : Int) atom1438Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (449248020026400 : Int) atom1439Coded) (CoefficientMerge.scale (620668861394400 : Int) atom1440Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (582988918831200 : Int) atom1441Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416071587909600 : Int) atom1442Coded) (CoefficientMerge.scale (578049932930400 : Int) atom1443Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163652046243840 : Int) atom1444Coded) (CoefficientMerge.scale (483786370015200 : Int) atom1445Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464046353038800 : Int) atom1446Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (352564509192000 : Int) atom1447Coded) (CoefficientMerge.scale (361867931119800 : Int) atom1448Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (344960709357600 : Int) atom1449Coded) (CoefficientMerge.scale (507525601237200 : Int) atom1450Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377976761080800 : Int) atom1451Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424529099908200 : Int) atom1452Coded) (CoefficientMerge.scale (126080231583600 : Int) atom1453Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (174744351860400 : Int) atom1454Coded) (CoefficientMerge.scale (211258137144600 : Int) atom1455Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6690481950600 : Int) atom1456Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49057765684200 : Int) atom1457Coded) (CoefficientMerge.scale (19631255212800 : Int) atom1458Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31325586960096 : Int) atom1459Coded) (CoefficientMerge.scale (6649449936096 : Int) atom1460Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6533608444704 : Int) atom1461Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5725639190304 : Int) atom1462Coded) (CoefficientMerge.scale (2642598614304 : Int) atom1463Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27375228517824 : Int) atom1464Coded) (CoefficientMerge.scale (15524745667200 : Int) atom1465Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6709402022400 : Int) atom1466Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34147372080096 : Int) atom1467Coded) (CoefficientMerge.scale (18942470112192 : Int) atom1468Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25753222645920 : Int) atom1469Coded) (CoefficientMerge.scale (16985780371296 : Int) atom1470Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4544075280096 : Int) atom1471Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7627115856096 : Int) atom1472Coded) (CoefficientMerge.scale (10710156432096 : Int) atom1473Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13793197008096 : Int) atom1474Coded) (CoefficientMerge.scale (10047950030448 : Int) atom1475Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5544496742400 : Int) atom1476Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7750445476752 : Int) atom1477Coded) (CoefficientMerge.scale (48376733335128 : Int) atom1478Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (89003021193504 : Int) atom1479Coded) (CoefficientMerge.scale (136178880879492 : Int) atom1480Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12542463216096 : Int) atom1481Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14392247654400 : Int) atom1482Coded) (CoefficientMerge.scale (4124895667200 : Int) atom1483Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34003013980320 : Int) atom1484Coded) (CoefficientMerge.scale (27298019539296 : Int) atom1485Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16918762281696 : Int) atom1486Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22064250691296 : Int) atom1487Coded) (CoefficientMerge.scale (27209739100896 : Int) atom1488Coded)))))))) := by
  have h : block020 = block020_data_flat159 := by decide +kernel
  exact h.trans block020_data_flat159_original
theorem block020_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block020 := by
  rw [block020_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1409Coded_nonneg g hg hA hB) (atom1410Coded_nonneg g hg hA hB)) (add_nonneg (atom1411Coded_nonneg g hg hA hB) (add_nonneg (atom1412Coded_nonneg g hg hA hB) (atom1413Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1414Coded_nonneg g hg hA hB) (atom1415Coded_nonneg g hg hA hB)) (add_nonneg (atom1416Coded_nonneg g hg hA hB) (add_nonneg (atom1417Coded_nonneg g hg hA hB) (atom1418Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1419Coded_nonneg g hg hA hB) (atom1420Coded_nonneg g hg hA hB)) (add_nonneg (atom1421Coded_nonneg g hg hA hB) (add_nonneg (atom1422Coded_nonneg g hg hA hB) (atom1423Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1424Coded_nonneg g hg hA hB) (atom1425Coded_nonneg g hg hA hB)) (add_nonneg (atom1426Coded_nonneg g hg hA hB) (add_nonneg (atom1427Coded_nonneg g hg hA hB) (atom1428Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1429Coded_nonneg g hg hA hB) (atom1430Coded_nonneg g hg hA hB)) (add_nonneg (atom1431Coded_nonneg g hg hA hB) (add_nonneg (atom1432Coded_nonneg g hg hA hB) (atom1433Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1434Coded_nonneg g hg hA hB) (atom1435Coded_nonneg g hg hA hB)) (add_nonneg (atom1436Coded_nonneg g hg hA hB) (add_nonneg (atom1437Coded_nonneg g hg hA hB) (atom1438Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1439Coded_nonneg g hg hA hB) (atom1440Coded_nonneg g hg hA hB)) (add_nonneg (atom1441Coded_nonneg g hg hA hB) (add_nonneg (atom1442Coded_nonneg g hg hA hB) (atom1443Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1444Coded_nonneg g hg hA hB) (atom1445Coded_nonneg g hg hA hB)) (add_nonneg (atom1446Coded_nonneg g hg hA hB) (add_nonneg (atom1447Coded_nonneg g hg hA hB) (atom1448Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1449Coded_nonneg g hg hA hB) (atom1450Coded_nonneg g hg hA hB)) (add_nonneg (atom1451Coded_nonneg g hg hA hB) (add_nonneg (atom1452Coded_nonneg g hg hA hB) (atom1453Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1454Coded_nonneg g hg hA hB) (atom1455Coded_nonneg g hg hA hB)) (add_nonneg (atom1456Coded_nonneg g hg hA hB) (add_nonneg (atom1457Coded_nonneg g hg hA hB) (atom1458Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1459Coded_nonneg g hg hA hB) (atom1460Coded_nonneg g hg hA hB)) (add_nonneg (atom1461Coded_nonneg g hg hA hB) (add_nonneg (atom1462Coded_nonneg g hg hA hB) (atom1463Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1464Coded_nonneg g hg hA hB) (atom1465Coded_nonneg g hg hA hB)) (add_nonneg (atom1466Coded_nonneg g hg hA hB) (add_nonneg (atom1467Coded_nonneg g hg hA hB) (atom1468Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1469Coded_nonneg g hg hA hB) (atom1470Coded_nonneg g hg hA hB)) (add_nonneg (atom1471Coded_nonneg g hg hA hB) (add_nonneg (atom1472Coded_nonneg g hg hA hB) (atom1473Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1474Coded_nonneg g hg hA hB) (atom1475Coded_nonneg g hg hA hB)) (add_nonneg (atom1476Coded_nonneg g hg hA hB) (add_nonneg (atom1477Coded_nonneg g hg hA hB) (atom1478Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1479Coded_nonneg g hg hA hB) (atom1480Coded_nonneg g hg hA hB)) (add_nonneg (atom1481Coded_nonneg g hg hA hB) (add_nonneg (atom1482Coded_nonneg g hg hA hB) (atom1483Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1484Coded_nonneg g hg hA hB) (atom1485Coded_nonneg g hg hA hB)) (add_nonneg (atom1486Coded_nonneg g hg hA hB) (add_nonneg (atom1487Coded_nonneg g hg hA hB) (atom1488Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
