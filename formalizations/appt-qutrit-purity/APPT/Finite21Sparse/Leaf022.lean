import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1616 : SparsePolynomial.Poly := [([11,18,19], 1)]
theorem eval_atom1616 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1616 = ((g 11) * (g 18) * (g 19)) := by
  norm_num [atom1616, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1616_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58329956563200 : Int) atom1616) := by
  rw [SparsePolynomial.eval_scale, eval_atom1616]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1616Coded : CoefficientMerge.Poly := [(5248, 1)]
theorem atom1616Coded_decode : atom1616 = SparsePolynomial.decodeCubic 21 atom1616Coded := by decide +kernel
theorem atom1616Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) := by
  have h := atom1616_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1616Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1617 : SparsePolynomial.Poly := [([11,18,20], 1)]
theorem eval_atom1617 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1617 = ((g 11) * (g 18) * (g 20)) := by
  norm_num [atom1617, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1617_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71135158752000 : Int) atom1617) := by
  rw [SparsePolynomial.eval_scale, eval_atom1617]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1617Coded : CoefficientMerge.Poly := [(5249, 1)]
theorem atom1617Coded_decode : atom1617 = SparsePolynomial.decodeCubic 21 atom1617Coded := by decide +kernel
theorem atom1617Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded) := by
  have h := atom1617_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1617Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1618 : SparsePolynomial.Poly := [([11,19,19], 1)]
theorem eval_atom1618 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1618 = ((g 11) * (g 19) * (g 19)) := by
  norm_num [atom1618, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1618_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16986153139200 : Int) atom1618) := by
  rw [SparsePolynomial.eval_scale, eval_atom1618]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1618Coded : CoefficientMerge.Poly := [(5269, 1)]
theorem atom1618Coded_decode : atom1618 = SparsePolynomial.decodeCubic 21 atom1618Coded := by decide +kernel
theorem atom1618Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) := by
  have h := atom1618_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1618Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1619 : SparsePolynomial.Poly := [([11,19,20], 1)]
theorem eval_atom1619 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1619 = ((g 11) * (g 19) * (g 20)) := by
  norm_num [atom1619, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1619_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48554288496000 : Int) atom1619) := by
  rw [SparsePolynomial.eval_scale, eval_atom1619]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1619Coded : CoefficientMerge.Poly := [(5270, 1)]
theorem atom1619Coded_decode : atom1619 = SparsePolynomial.decodeCubic 21 atom1619Coded := by decide +kernel
theorem atom1619Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) := by
  have h := atom1619_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1619Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1620 : SparsePolynomial.Poly := [([11,20,20], 1)]
theorem eval_atom1620 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1620 = ((g 11) * (g 20) * (g 20)) := by
  norm_num [atom1620, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1620_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27477786268800 : Int) atom1620) := by
  rw [SparsePolynomial.eval_scale, eval_atom1620]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1620Coded : CoefficientMerge.Poly := [(5291, 1)]
theorem atom1620Coded_decode : atom1620 = SparsePolynomial.decodeCubic 21 atom1620Coded := by decide +kernel
theorem atom1620Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded) := by
  have h := atom1620_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1620Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1621 : SparsePolynomial.Poly := [([12,12,12], 1)]
theorem eval_atom1621 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1621 = ((g 12) * (g 12) * (g 12)) := by
  norm_num [atom1621, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1621_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142393305600 : Int) atom1621) := by
  rw [SparsePolynomial.eval_scale, eval_atom1621]
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 12) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1621Coded : CoefficientMerge.Poly := [(5556, 1)]
theorem atom1621Coded_decode : atom1621 = SparsePolynomial.decodeCubic 21 atom1621Coded := by decide +kernel
theorem atom1621Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) := by
  have h := atom1621_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1621Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1622 : SparsePolynomial.Poly := [([12,12,17], 1)]
theorem eval_atom1622 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1622 = ((g 12) * (g 12) * (g 17)) := by
  norm_num [atom1622, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1622_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3961249152000 : Int) atom1622) := by
  rw [SparsePolynomial.eval_scale, eval_atom1622]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1622Coded : CoefficientMerge.Poly := [(5561, 1)]
theorem atom1622Coded_decode : atom1622 = SparsePolynomial.decodeCubic 21 atom1622Coded := by decide +kernel
theorem atom1622Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded) := by
  have h := atom1622_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1622Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1623 : SparsePolynomial.Poly := [([12,12,18], 1)]
theorem eval_atom1623 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1623 = ((g 12) * (g 12) * (g 18)) := by
  norm_num [atom1623, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1623_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (657701004800 : Int) atom1623) := by
  rw [SparsePolynomial.eval_scale, eval_atom1623]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1623Coded : CoefficientMerge.Poly := [(5562, 1)]
theorem atom1623Coded_decode : atom1623 = SparsePolynomial.decodeCubic 21 atom1623Coded := by decide +kernel
theorem atom1623Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) := by
  have h := atom1623_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1623Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1624 : SparsePolynomial.Poly := [([12,13,13], 1)]
theorem eval_atom1624 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1624 = ((g 12) * (g 13) * (g 13)) := by
  norm_num [atom1624, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1624_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (731019801600 : Int) atom1624) := by
  rw [SparsePolynomial.eval_scale, eval_atom1624]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1624Coded : CoefficientMerge.Poly := [(5578, 1)]
theorem atom1624Coded_decode : atom1624 = SparsePolynomial.decodeCubic 21 atom1624Coded := by decide +kernel
theorem atom1624Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) := by
  have h := atom1624_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1624Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1625 : SparsePolynomial.Poly := [([12,13,14], 1)]
theorem eval_atom1625 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1625 = ((g 12) * (g 13) * (g 14)) := by
  norm_num [atom1625, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1625_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (718685798400 : Int) atom1625) := by
  rw [SparsePolynomial.eval_scale, eval_atom1625]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1625Coded : CoefficientMerge.Poly := [(5579, 1)]
theorem atom1625Coded_decode : atom1625 = SparsePolynomial.decodeCubic 21 atom1625Coded := by decide +kernel
theorem atom1625Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded) := by
  have h := atom1625_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1625Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1626 : SparsePolynomial.Poly := [([12,13,16], 1)]
theorem eval_atom1626 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1626 = ((g 12) * (g 13) * (g 16)) := by
  norm_num [atom1626, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1626_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (781859212800 : Int) atom1626) := by
  rw [SparsePolynomial.eval_scale, eval_atom1626]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1626Coded : CoefficientMerge.Poly := [(5581, 1)]
theorem atom1626Coded_decode : atom1626 = SparsePolynomial.decodeCubic 21 atom1626Coded := by decide +kernel
theorem atom1626Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) := by
  have h := atom1626_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1626Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1627 : SparsePolynomial.Poly := [([12,13,17], 1)]
theorem eval_atom1627 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1627 = ((g 12) * (g 13) * (g 17)) := by
  norm_num [atom1627, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1627_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16022245108800 : Int) atom1627) := by
  rw [SparsePolynomial.eval_scale, eval_atom1627]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1627Coded : CoefficientMerge.Poly := [(5582, 1)]
theorem atom1627Coded_decode : atom1627 = SparsePolynomial.decodeCubic 21 atom1627Coded := by decide +kernel
theorem atom1627Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded) := by
  have h := atom1627_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1627Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1628 : SparsePolynomial.Poly := [([12,13,18], 1)]
theorem eval_atom1628 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1628 = ((g 12) * (g 13) * (g 18)) := by
  norm_num [atom1628, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1628_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13551194686400 : Int) atom1628) := by
  rw [SparsePolynomial.eval_scale, eval_atom1628]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1628Coded : CoefficientMerge.Poly := [(5583, 1)]
theorem atom1628Coded_decode : atom1628 = SparsePolynomial.decodeCubic 21 atom1628Coded := by decide +kernel
theorem atom1628Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) := by
  have h := atom1628_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1628Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1629 : SparsePolynomial.Poly := [([12,13,19], 1)]
theorem eval_atom1629 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1629 = ((g 12) * (g 13) * (g 19)) := by
  norm_num [atom1629, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1629_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11776027622400 : Int) atom1629) := by
  rw [SparsePolynomial.eval_scale, eval_atom1629]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1629Coded : CoefficientMerge.Poly := [(5584, 1)]
theorem atom1629Coded_decode : atom1629 = SparsePolynomial.decodeCubic 21 atom1629Coded := by decide +kernel
theorem atom1629Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) := by
  have h := atom1629_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1629Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1630 : SparsePolynomial.Poly := [([12,13,20], 1)]
theorem eval_atom1630 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1630 = ((g 12) * (g 13) * (g 20)) := by
  norm_num [atom1630, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1630_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24502199198400 : Int) atom1630) := by
  rw [SparsePolynomial.eval_scale, eval_atom1630]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1630Coded : CoefficientMerge.Poly := [(5585, 1)]
theorem atom1630Coded_decode : atom1630 = SparsePolynomial.decodeCubic 21 atom1630Coded := by decide +kernel
theorem atom1630Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded) := by
  have h := atom1630_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1630Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1631 : SparsePolynomial.Poly := [([12,14,14], 1)]
theorem eval_atom1631 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1631 = ((g 12) * (g 14) * (g 14)) := by
  norm_num [atom1631, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1631_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3414217766400 : Int) atom1631) := by
  rw [SparsePolynomial.eval_scale, eval_atom1631]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1631Coded : CoefficientMerge.Poly := [(5600, 1)]
theorem atom1631Coded_decode : atom1631 = SparsePolynomial.decodeCubic 21 atom1631Coded := by decide +kernel
theorem atom1631Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) := by
  have h := atom1631_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1631Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1632 : SparsePolynomial.Poly := [([12,14,16], 1)]
theorem eval_atom1632 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1632 = ((g 12) * (g 14) * (g 16)) := by
  norm_num [atom1632, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1632_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1274989228800 : Int) atom1632) := by
  rw [SparsePolynomial.eval_scale, eval_atom1632]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1632Coded : CoefficientMerge.Poly := [(5602, 1)]
theorem atom1632Coded_decode : atom1632 = SparsePolynomial.decodeCubic 21 atom1632Coded := by decide +kernel
theorem atom1632Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded) := by
  have h := atom1632_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1632Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1633 : SparsePolynomial.Poly := [([12,14,17], 1)]
theorem eval_atom1633 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1633 = ((g 12) * (g 14) * (g 17)) := by
  norm_num [atom1633, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1633_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25932352051200 : Int) atom1633) := by
  rw [SparsePolynomial.eval_scale, eval_atom1633]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1633Coded : CoefficientMerge.Poly := [(5603, 1)]
theorem atom1633Coded_decode : atom1633 = SparsePolynomial.decodeCubic 21 atom1633Coded := by decide +kernel
theorem atom1633Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) := by
  have h := atom1633_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1633Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1634 : SparsePolynomial.Poly := [([12,14,18], 1)]
theorem eval_atom1634 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1634 = ((g 12) * (g 14) * (g 18)) := by
  norm_num [atom1634, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1634_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27709905507200 : Int) atom1634) := by
  rw [SparsePolynomial.eval_scale, eval_atom1634]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1634Coded : CoefficientMerge.Poly := [(5604, 1)]
theorem atom1634Coded_decode : atom1634 = SparsePolynomial.decodeCubic 21 atom1634Coded := by decide +kernel
theorem atom1634Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) := by
  have h := atom1634_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1634Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1635 : SparsePolynomial.Poly := [([12,14,19], 1)]
theorem eval_atom1635 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1635 = ((g 12) * (g 14) * (g 19)) := by
  norm_num [atom1635, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1635_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27473854060800 : Int) atom1635) := by
  rw [SparsePolynomial.eval_scale, eval_atom1635]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1635Coded : CoefficientMerge.Poly := [(5605, 1)]
theorem atom1635Coded_decode : atom1635 = SparsePolynomial.decodeCubic 21 atom1635Coded := by decide +kernel
theorem atom1635Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded) := by
  have h := atom1635_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1635Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1636 : SparsePolynomial.Poly := [([12,14,20], 1)]
theorem eval_atom1636 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1636 = ((g 12) * (g 14) * (g 20)) := by
  norm_num [atom1636, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1636_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53106823627200 : Int) atom1636) := by
  rw [SparsePolynomial.eval_scale, eval_atom1636]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1636Coded : CoefficientMerge.Poly := [(5606, 1)]
theorem atom1636Coded_decode : atom1636 = SparsePolynomial.decodeCubic 21 atom1636Coded := by decide +kernel
theorem atom1636Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) := by
  have h := atom1636_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1636Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1637 : SparsePolynomial.Poly := [([12,15,15], 1)]
theorem eval_atom1637 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1637 = ((g 12) * (g 15) * (g 15)) := by
  norm_num [atom1637, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1637_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6357299110400 : Int) atom1637) := by
  rw [SparsePolynomial.eval_scale, eval_atom1637]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1637Coded : CoefficientMerge.Poly := [(5622, 1)]
theorem atom1637Coded_decode : atom1637 = SparsePolynomial.decodeCubic 21 atom1637Coded := by decide +kernel
theorem atom1637Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded) := by
  have h := atom1637_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1637Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1638 : SparsePolynomial.Poly := [([12,15,16], 1)]
theorem eval_atom1638 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1638 = ((g 12) * (g 15) * (g 16)) := by
  norm_num [atom1638, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1638_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19520661753600 : Int) atom1638) := by
  rw [SparsePolynomial.eval_scale, eval_atom1638]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1638Coded : CoefficientMerge.Poly := [(5623, 1)]
theorem atom1638Coded_decode : atom1638 = SparsePolynomial.decodeCubic 21 atom1638Coded := by decide +kernel
theorem atom1638Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) := by
  have h := atom1638_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1638Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1639 : SparsePolynomial.Poly := [([12,15,17], 1)]
theorem eval_atom1639 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1639 = ((g 12) * (g 15) * (g 17)) := by
  norm_num [atom1639, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1639_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54017265971200 : Int) atom1639) := by
  rw [SparsePolynomial.eval_scale, eval_atom1639]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1639Coded : CoefficientMerge.Poly := [(5624, 1)]
theorem atom1639Coded_decode : atom1639 = SparsePolynomial.decodeCubic 21 atom1639Coded := by decide +kernel
theorem atom1639Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) := by
  have h := atom1639_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1639Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1640 : SparsePolynomial.Poly := [([12,15,18], 1)]
theorem eval_atom1640 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1640 = ((g 12) * (g 15) * (g 18)) := by
  norm_num [atom1640, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1640_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60723048870400 : Int) atom1640) := by
  rw [SparsePolynomial.eval_scale, eval_atom1640]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1640Coded : CoefficientMerge.Poly := [(5625, 1)]
theorem atom1640Coded_decode : atom1640 = SparsePolynomial.decodeCubic 21 atom1640Coded := by decide +kernel
theorem atom1640Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded) := by
  have h := atom1640_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1640Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1641 : SparsePolynomial.Poly := [([12,15,19], 1)]
theorem eval_atom1641 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1641 = ((g 12) * (g 15) * (g 19)) := by
  norm_num [atom1641, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1641_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48904332915200 : Int) atom1641) := by
  rw [SparsePolynomial.eval_scale, eval_atom1641]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1641Coded : CoefficientMerge.Poly := [(5626, 1)]
theorem atom1641Coded_decode : atom1641 = SparsePolynomial.decodeCubic 21 atom1641Coded := by decide +kernel
theorem atom1641Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) := by
  have h := atom1641_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1641Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1642 : SparsePolynomial.Poly := [([12,15,20], 1)]
theorem eval_atom1642 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1642 = ((g 12) * (g 15) * (g 20)) := by
  norm_num [atom1642, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1642_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82971805996800 : Int) atom1642) := by
  rw [SparsePolynomial.eval_scale, eval_atom1642]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1642Coded : CoefficientMerge.Poly := [(5627, 1)]
theorem atom1642Coded_decode : atom1642 = SparsePolynomial.decodeCubic 21 atom1642Coded := by decide +kernel
theorem atom1642Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded) := by
  have h := atom1642_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1642Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1643 : SparsePolynomial.Poly := [([12,16,16], 1)]
theorem eval_atom1643 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1643 = ((g 12) * (g 16) * (g 16)) := by
  norm_num [atom1643, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1643_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7890507752960 : Int) atom1643) := by
  rw [SparsePolynomial.eval_scale, eval_atom1643]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1643Coded : CoefficientMerge.Poly := [(5644, 1)]
theorem atom1643Coded_decode : atom1643 = SparsePolynomial.decodeCubic 21 atom1643Coded := by decide +kernel
theorem atom1643Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) := by
  have h := atom1643_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1643Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1644 : SparsePolynomial.Poly := [([12,16,17], 1)]
theorem eval_atom1644 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1644 = ((g 12) * (g 16) * (g 17)) := by
  norm_num [atom1644, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1644_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48082095084800 : Int) atom1644) := by
  rw [SparsePolynomial.eval_scale, eval_atom1644]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1644Coded : CoefficientMerge.Poly := [(5645, 1)]
theorem atom1644Coded_decode : atom1644 = SparsePolynomial.decodeCubic 21 atom1644Coded := by decide +kernel
theorem atom1644Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) := by
  have h := atom1644_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1644Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1645 : SparsePolynomial.Poly := [([12,16,18], 1)]
theorem eval_atom1645 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1645 = ((g 12) * (g 16) * (g 18)) := by
  norm_num [atom1645, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1645_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63896669200000 : Int) atom1645) := by
  rw [SparsePolynomial.eval_scale, eval_atom1645]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1645Coded : CoefficientMerge.Poly := [(5646, 1)]
theorem atom1645Coded_decode : atom1645 = SparsePolynomial.decodeCubic 21 atom1645Coded := by decide +kernel
theorem atom1645Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded) := by
  have h := atom1645_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1645Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1646 : SparsePolynomial.Poly := [([12,16,19], 1)]
theorem eval_atom1646 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1646 = ((g 12) * (g 16) * (g 19)) := by
  norm_num [atom1646, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1646_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55239224230400 : Int) atom1646) := by
  rw [SparsePolynomial.eval_scale, eval_atom1646]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1646Coded : CoefficientMerge.Poly := [(5647, 1)]
theorem atom1646Coded_decode : atom1646 = SparsePolynomial.decodeCubic 21 atom1646Coded := by decide +kernel
theorem atom1646Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) := by
  have h := atom1646_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1646Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1647 : SparsePolynomial.Poly := [([12,16,20], 1)]
theorem eval_atom1647 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1647 = ((g 12) * (g 16) * (g 20)) := by
  norm_num [atom1647, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1647_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78568808472000 : Int) atom1647) := by
  rw [SparsePolynomial.eval_scale, eval_atom1647]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1647Coded : CoefficientMerge.Poly := [(5648, 1)]
theorem atom1647Coded_decode : atom1647 = SparsePolynomial.decodeCubic 21 atom1647Coded := by decide +kernel
theorem atom1647Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded) := by
  have h := atom1647_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1647Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1648 : SparsePolynomial.Poly := [([12,17,17], 1)]
theorem eval_atom1648 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1648 = ((g 12) * (g 17) * (g 17)) := by
  norm_num [atom1648, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1648_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39256609548800 : Int) atom1648) := by
  rw [SparsePolynomial.eval_scale, eval_atom1648]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1648Coded : CoefficientMerge.Poly := [(5666, 1)]
theorem atom1648Coded_decode : atom1648 = SparsePolynomial.decodeCubic 21 atom1648Coded := by decide +kernel
theorem atom1648Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) := by
  have h := atom1648_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1648Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1649 : SparsePolynomial.Poly := [([12,17,18], 1)]
theorem eval_atom1649 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1649 = ((g 12) * (g 17) * (g 18)) := by
  norm_num [atom1649, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1649_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80549880678400 : Int) atom1649) := by
  rw [SparsePolynomial.eval_scale, eval_atom1649]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1649Coded : CoefficientMerge.Poly := [(5667, 1)]
theorem atom1649Coded_decode : atom1649 = SparsePolynomial.decodeCubic 21 atom1649Coded := by decide +kernel
theorem atom1649Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) := by
  have h := atom1649_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1649Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1650 : SparsePolynomial.Poly := [([12,17,19], 1)]
theorem eval_atom1650 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1650 = ((g 12) * (g 17) * (g 19)) := by
  norm_num [atom1650, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1650_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69215540800000 : Int) atom1650) := by
  rw [SparsePolynomial.eval_scale, eval_atom1650]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1650Coded : CoefficientMerge.Poly := [(5668, 1)]
theorem atom1650Coded_decode : atom1650 = SparsePolynomial.decodeCubic 21 atom1650Coded := by decide +kernel
theorem atom1650Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded) := by
  have h := atom1650_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1650Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1651 : SparsePolynomial.Poly := [([12,17,20], 1)]
theorem eval_atom1651 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1651 = ((g 12) * (g 17) * (g 20)) := by
  norm_num [atom1651, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1651_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88196267756800 : Int) atom1651) := by
  rw [SparsePolynomial.eval_scale, eval_atom1651]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1651Coded : CoefficientMerge.Poly := [(5669, 1)]
theorem atom1651Coded_decode : atom1651 = SparsePolynomial.decodeCubic 21 atom1651Coded := by decide +kernel
theorem atom1651Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) := by
  have h := atom1651_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1651Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1652 : SparsePolynomial.Poly := [([12,18,18], 1)]
theorem eval_atom1652 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1652 = ((g 12) * (g 18) * (g 18)) := by
  norm_num [atom1652, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1652_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35739932211200 : Int) atom1652) := by
  rw [SparsePolynomial.eval_scale, eval_atom1652]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1652Coded : CoefficientMerge.Poly := [(5688, 1)]
theorem atom1652Coded_decode : atom1652 = SparsePolynomial.decodeCubic 21 atom1652Coded := by decide +kernel
theorem atom1652Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded) := by
  have h := atom1652_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1652Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1653 : SparsePolynomial.Poly := [([12,18,19], 1)]
theorem eval_atom1653 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1653 = ((g 12) * (g 18) * (g 19)) := by
  norm_num [atom1653, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1653_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67106442681600 : Int) atom1653) := by
  rw [SparsePolynomial.eval_scale, eval_atom1653]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1653Coded : CoefficientMerge.Poly := [(5689, 1)]
theorem atom1653Coded_decode : atom1653 = SparsePolynomial.decodeCubic 21 atom1653Coded := by decide +kernel
theorem atom1653Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) := by
  have h := atom1653_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1653Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1654 : SparsePolynomial.Poly := [([12,18,20], 1)]
theorem eval_atom1654 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1654 = ((g 12) * (g 18) * (g 20)) := by
  norm_num [atom1654, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1654_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90606689488000 : Int) atom1654) := by
  rw [SparsePolynomial.eval_scale, eval_atom1654]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1654Coded : CoefficientMerge.Poly := [(5690, 1)]
theorem atom1654Coded_decode : atom1654 = SparsePolynomial.decodeCubic 21 atom1654Coded := by decide +kernel
theorem atom1654Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) := by
  have h := atom1654_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1654Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1655 : SparsePolynomial.Poly := [([12,19,19], 1)]
theorem eval_atom1655 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1655 = ((g 12) * (g 19) * (g 19)) := by
  norm_num [atom1655, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1655_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25516823091200 : Int) atom1655) := by
  rw [SparsePolynomial.eval_scale, eval_atom1655]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1655Coded : CoefficientMerge.Poly := [(5710, 1)]
theorem atom1655Coded_decode : atom1655 = SparsePolynomial.decodeCubic 21 atom1655Coded := by decide +kernel
theorem atom1655Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded) := by
  have h := atom1655_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1655Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1656 : SparsePolynomial.Poly := [([12,19,20], 1)]
theorem eval_atom1656 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1656 = ((g 12) * (g 19) * (g 20)) := by
  norm_num [atom1656, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1656_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77437241660800 : Int) atom1656) := by
  rw [SparsePolynomial.eval_scale, eval_atom1656]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1656Coded : CoefficientMerge.Poly := [(5711, 1)]
theorem atom1656Coded_decode : atom1656 = SparsePolynomial.decodeCubic 21 atom1656Coded := by decide +kernel
theorem atom1656Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) := by
  have h := atom1656_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1656Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1657 : SparsePolynomial.Poly := [([12,20,20], 1)]
theorem eval_atom1657 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1657 = ((g 12) * (g 20) * (g 20)) := by
  norm_num [atom1657, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1657_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47533761553600 : Int) atom1657) := by
  rw [SparsePolynomial.eval_scale, eval_atom1657]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1657Coded : CoefficientMerge.Poly := [(5732, 1)]
theorem atom1657Coded_decode : atom1657 = SparsePolynomial.decodeCubic 21 atom1657Coded := by decide +kernel
theorem atom1657Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded) := by
  have h := atom1657_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1657Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1658 : SparsePolynomial.Poly := [([13,13,13], 1)]
theorem eval_atom1658 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1658 = ((g 13) * (g 13) * (g 13)) := by
  norm_num [atom1658, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1658_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (390177907200 : Int) atom1658) := by
  rw [SparsePolynomial.eval_scale, eval_atom1658]
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 13) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1658Coded : CoefficientMerge.Poly := [(6019, 1)]
theorem atom1658Coded_decode : atom1658 = SparsePolynomial.decodeCubic 21 atom1658Coded := by decide +kernel
theorem atom1658Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) := by
  have h := atom1658_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1658Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1659 : SparsePolynomial.Poly := [([13,13,17], 1)]
theorem eval_atom1659 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1659 = ((g 13) * (g 13) * (g 17)) := by
  norm_num [atom1659, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1659_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7496187508800 : Int) atom1659) := by
  rw [SparsePolynomial.eval_scale, eval_atom1659]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1659Coded : CoefficientMerge.Poly := [(6023, 1)]
theorem atom1659Coded_decode : atom1659 = SparsePolynomial.decodeCubic 21 atom1659Coded := by decide +kernel
theorem atom1659Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) := by
  have h := atom1659_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1659Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1660 : SparsePolynomial.Poly := [([13,13,18], 1)]
theorem eval_atom1660 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1660 = ((g 13) * (g 13) * (g 18)) := by
  norm_num [atom1660, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1660_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6223620657600 : Int) atom1660) := by
  rw [SparsePolynomial.eval_scale, eval_atom1660]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1660Coded : CoefficientMerge.Poly := [(6024, 1)]
theorem atom1660Coded_decode : atom1660 = SparsePolynomial.decodeCubic 21 atom1660Coded := by decide +kernel
theorem atom1660Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded) := by
  have h := atom1660_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1660Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1661 : SparsePolynomial.Poly := [([13,13,20], 1)]
theorem eval_atom1661 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1661 = ((g 13) * (g 13) * (g 20)) := by
  norm_num [atom1661, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1661_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6958414296000 : Int) atom1661) := by
  rw [SparsePolynomial.eval_scale, eval_atom1661]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1661Coded : CoefficientMerge.Poly := [(6026, 1)]
theorem atom1661Coded_decode : atom1661 = SparsePolynomial.decodeCubic 21 atom1661Coded := by decide +kernel
theorem atom1661Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) := by
  have h := atom1661_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1661Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1662 : SparsePolynomial.Poly := [([13,14,14], 1)]
theorem eval_atom1662 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1662 = ((g 13) * (g 14) * (g 14)) := by
  norm_num [atom1662, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1662_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1828838131200 : Int) atom1662) := by
  rw [SparsePolynomial.eval_scale, eval_atom1662]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1662Coded : CoefficientMerge.Poly := [(6041, 1)]
theorem atom1662Coded_decode : atom1662 = SparsePolynomial.decodeCubic 21 atom1662Coded := by decide +kernel
theorem atom1662Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded) := by
  have h := atom1662_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1662Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1663 : SparsePolynomial.Poly := [([13,14,16], 1)]
theorem eval_atom1663 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1663 = ((g 13) * (g 14) * (g 16)) := by
  norm_num [atom1663, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1663_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2672152588800 : Int) atom1663) := by
  rw [SparsePolynomial.eval_scale, eval_atom1663]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1663Coded : CoefficientMerge.Poly := [(6043, 1)]
theorem atom1663Coded_decode : atom1663 = SparsePolynomial.decodeCubic 21 atom1663Coded := by decide +kernel
theorem atom1663Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) := by
  have h := atom1663_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1663Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1664 : SparsePolynomial.Poly := [([13,14,17], 1)]
theorem eval_atom1664 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1664 = ((g 13) * (g 14) * (g 17)) := by
  norm_num [atom1664, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1664_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28714425307200 : Int) atom1664) := by
  rw [SparsePolynomial.eval_scale, eval_atom1664]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1664Coded : CoefficientMerge.Poly := [(6044, 1)]
theorem atom1664Coded_decode : atom1664 = SparsePolynomial.decodeCubic 21 atom1664Coded := by decide +kernel
theorem atom1664Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) := by
  have h := atom1664_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1664Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1665 : SparsePolynomial.Poly := [([13,14,18], 1)]
theorem eval_atom1665 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1665 = ((g 13) * (g 14) * (g 18)) := by
  norm_num [atom1665, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1665_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31318438795200 : Int) atom1665) := by
  rw [SparsePolynomial.eval_scale, eval_atom1665]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1665Coded : CoefficientMerge.Poly := [(6045, 1)]
theorem atom1665Coded_decode : atom1665 = SparsePolynomial.decodeCubic 21 atom1665Coded := by decide +kernel
theorem atom1665Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded) := by
  have h := atom1665_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1665Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1666 : SparsePolynomial.Poly := [([13,14,19], 1)]
theorem eval_atom1666 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1666 = ((g 13) * (g 14) * (g 19)) := by
  norm_num [atom1666, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1666_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20764754611200 : Int) atom1666) := by
  rw [SparsePolynomial.eval_scale, eval_atom1666]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1666Coded : CoefficientMerge.Poly := [(6046, 1)]
theorem atom1666Coded_decode : atom1666 = SparsePolynomial.decodeCubic 21 atom1666Coded := by decide +kernel
theorem atom1666Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) := by
  have h := atom1666_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1666Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1667 : SparsePolynomial.Poly := [([13,14,20], 1)]
theorem eval_atom1667 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1667 = ((g 13) * (g 14) * (g 20)) := by
  norm_num [atom1667, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1667_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47303583076800 : Int) atom1667) := by
  rw [SparsePolynomial.eval_scale, eval_atom1667]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1667Coded : CoefficientMerge.Poly := [(6047, 1)]
theorem atom1667Coded_decode : atom1667 = SparsePolynomial.decodeCubic 21 atom1667Coded := by decide +kernel
theorem atom1667Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded) := by
  have h := atom1667_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1667Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1668 : SparsePolynomial.Poly := [([13,15,15], 1)]
theorem eval_atom1668 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1668 = ((g 13) * (g 15) * (g 15)) := by
  norm_num [atom1668, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1668_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3550208205600 : Int) atom1668) := by
  rw [SparsePolynomial.eval_scale, eval_atom1668]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1668Coded : CoefficientMerge.Poly := [(6063, 1)]
theorem atom1668Coded_decode : atom1668 = SparsePolynomial.decodeCubic 21 atom1668Coded := by decide +kernel
theorem atom1668Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) := by
  have h := atom1668_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1668Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1669 : SparsePolynomial.Poly := [([13,15,16], 1)]
theorem eval_atom1669 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1669 = ((g 13) * (g 15) * (g 16)) := by
  norm_num [atom1669, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1669_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14159602504800 : Int) atom1669) := by
  rw [SparsePolynomial.eval_scale, eval_atom1669]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1669Coded : CoefficientMerge.Poly := [(6064, 1)]
theorem atom1669Coded_decode : atom1669 = SparsePolynomial.decodeCubic 21 atom1669Coded := by decide +kernel
theorem atom1669Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) := by
  have h := atom1669_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1669Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1670 : SparsePolynomial.Poly := [([13,15,17], 1)]
theorem eval_atom1670 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1670 = ((g 13) * (g 15) * (g 17)) := by
  norm_num [atom1670, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1670_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50540795877600 : Int) atom1670) := by
  rw [SparsePolynomial.eval_scale, eval_atom1670]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1670Coded : CoefficientMerge.Poly := [(6065, 1)]
theorem atom1670Coded_decode : atom1670 = SparsePolynomial.decodeCubic 21 atom1670Coded := by decide +kernel
theorem atom1670Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded) := by
  have h := atom1670_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1670Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1671 : SparsePolynomial.Poly := [([13,15,18], 1)]
theorem eval_atom1671 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1671 = ((g 13) * (g 15) * (g 18)) := by
  norm_num [atom1671, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1671_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58714949336400 : Int) atom1671) := by
  rw [SparsePolynomial.eval_scale, eval_atom1671]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1671Coded : CoefficientMerge.Poly := [(6066, 1)]
theorem atom1671Coded_decode : atom1671 = SparsePolynomial.decodeCubic 21 atom1671Coded := by decide +kernel
theorem atom1671Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) := by
  have h := atom1671_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1671Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1672 : SparsePolynomial.Poly := [([13,15,19], 1)]
theorem eval_atom1672 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1672 = ((g 13) * (g 15) * (g 19)) := by
  norm_num [atom1672, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1672_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44621368840800 : Int) atom1672) := by
  rw [SparsePolynomial.eval_scale, eval_atom1672]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1672Coded : CoefficientMerge.Poly := [(6067, 1)]
theorem atom1672Coded_decode : atom1672 = SparsePolynomial.decodeCubic 21 atom1672Coded := by decide +kernel
theorem atom1672Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded) := by
  have h := atom1672_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1672Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1673 : SparsePolynomial.Poly := [([13,15,20], 1)]
theorem eval_atom1673 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1673 = ((g 13) * (g 15) * (g 20)) := by
  norm_num [atom1673, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1673_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82584805073400 : Int) atom1673) := by
  rw [SparsePolynomial.eval_scale, eval_atom1673]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1673Coded : CoefficientMerge.Poly := [(6068, 1)]
theorem atom1673Coded_decode : atom1673 = SparsePolynomial.decodeCubic 21 atom1673Coded := by decide +kernel
theorem atom1673Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) := by
  have h := atom1673_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1673Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1674 : SparsePolynomial.Poly := [([13,16,16], 1)]
theorem eval_atom1674 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1674 = ((g 13) * (g 16) * (g 16)) := by
  norm_num [atom1674, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1674_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5924850140160 : Int) atom1674) := by
  rw [SparsePolynomial.eval_scale, eval_atom1674]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1674Coded : CoefficientMerge.Poly := [(6085, 1)]
theorem atom1674Coded_decode : atom1674 = SparsePolynomial.decodeCubic 21 atom1674Coded := by decide +kernel
theorem atom1674Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) := by
  have h := atom1674_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1674Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1675 : SparsePolynomial.Poly := [([13,16,17], 1)]
theorem eval_atom1675 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1675 = ((g 13) * (g 16) * (g 17)) := by
  norm_num [atom1675, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1675_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46603049565600 : Int) atom1675) := by
  rw [SparsePolynomial.eval_scale, eval_atom1675]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1675Coded : CoefficientMerge.Poly := [(6086, 1)]
theorem atom1675Coded_decode : atom1675 = SparsePolynomial.decodeCubic 21 atom1675Coded := by decide +kernel
theorem atom1675Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded) := by
  have h := atom1675_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1675Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1676 : SparsePolynomial.Poly := [([13,16,18], 1)]
theorem eval_atom1676 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1676 = ((g 13) * (g 16) * (g 18)) := by
  norm_num [atom1676, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1676_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64561905414000 : Int) atom1676) := by
  rw [SparsePolynomial.eval_scale, eval_atom1676]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1676Coded : CoefficientMerge.Poly := [(6087, 1)]
theorem atom1676Coded_decode : atom1676 = SparsePolynomial.decodeCubic 21 atom1676Coded := by decide +kernel
theorem atom1676Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) := by
  have h := atom1676_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1676Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1677 : SparsePolynomial.Poly := [([13,16,19], 1)]
theorem eval_atom1677 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1677 = ((g 13) * (g 16) * (g 19)) := by
  norm_num [atom1677, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1677_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58431178094400 : Int) atom1677) := by
  rw [SparsePolynomial.eval_scale, eval_atom1677]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1677Coded : CoefficientMerge.Poly := [(6088, 1)]
theorem atom1677Coded_decode : atom1677 = SparsePolynomial.decodeCubic 21 atom1677Coded := by decide +kernel
theorem atom1677Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded) := by
  have h := atom1677_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1677Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1678 : SparsePolynomial.Poly := [([13,16,20], 1)]
theorem eval_atom1678 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1678 = ((g 13) * (g 16) * (g 20)) := by
  norm_num [atom1678, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1678_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83751050082600 : Int) atom1678) := by
  rw [SparsePolynomial.eval_scale, eval_atom1678]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1678Coded : CoefficientMerge.Poly := [(6089, 1)]
theorem atom1678Coded_decode : atom1678 = SparsePolynomial.decodeCubic 21 atom1678Coded := by decide +kernel
theorem atom1678Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) := by
  have h := atom1678_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1678Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1679 : SparsePolynomial.Poly := [([13,17,17], 1)]
theorem eval_atom1679 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1679 = ((g 13) * (g 17) * (g 17)) := by
  norm_num [atom1679, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1679_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38700065779200 : Int) atom1679) := by
  rw [SparsePolynomial.eval_scale, eval_atom1679]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1679Coded : CoefficientMerge.Poly := [(6107, 1)]
theorem atom1679Coded_decode : atom1679 = SparsePolynomial.decodeCubic 21 atom1679Coded := by decide +kernel
theorem atom1679Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) := by
  have h := atom1679_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1679Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1680 : SparsePolynomial.Poly := [([13,17,18], 1)]
theorem eval_atom1680 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1680 = ((g 13) * (g 17) * (g 18)) := by
  norm_num [atom1680, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1680_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81441252748800 : Int) atom1680) := by
  rw [SparsePolynomial.eval_scale, eval_atom1680]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1680Coded : CoefficientMerge.Poly := [(6108, 1)]
theorem atom1680Coded_decode : atom1680 = SparsePolynomial.decodeCubic 21 atom1680Coded := by decide +kernel
theorem atom1680Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded) := by
  have h := atom1680_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1680Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1681 : SparsePolynomial.Poly := [([13,17,19], 1)]
theorem eval_atom1681 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1681 = ((g 13) * (g 17) * (g 19)) := by
  norm_num [atom1681, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1681_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76619479413600 : Int) atom1681) := by
  rw [SparsePolynomial.eval_scale, eval_atom1681]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1681Coded : CoefficientMerge.Poly := [(6109, 1)]
theorem atom1681Coded_decode : atom1681 = SparsePolynomial.decodeCubic 21 atom1681Coded := by decide +kernel
theorem atom1681Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) := by
  have h := atom1681_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1681Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1682 : SparsePolynomial.Poly := [([13,17,20], 1)]
theorem eval_atom1682 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1682 = ((g 13) * (g 17) * (g 20)) := by
  norm_num [atom1682, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1682_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96041823897600 : Int) atom1682) := by
  rw [SparsePolynomial.eval_scale, eval_atom1682]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1682Coded : CoefficientMerge.Poly := [(6110, 1)]
theorem atom1682Coded_decode : atom1682 = SparsePolynomial.decodeCubic 21 atom1682Coded := by decide +kernel
theorem atom1682Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded) := by
  have h := atom1682_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1682Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1683 : SparsePolynomial.Poly := [([13,18,18], 1)]
theorem eval_atom1683 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1683 = ((g 13) * (g 18) * (g 18)) := by
  norm_num [atom1683, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1683_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36760668134400 : Int) atom1683) := by
  rw [SparsePolynomial.eval_scale, eval_atom1683]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1683Coded : CoefficientMerge.Poly := [(6129, 1)]
theorem atom1683Coded_decode : atom1683 = SparsePolynomial.decodeCubic 21 atom1683Coded := by decide +kernel
theorem atom1683Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) := by
  have h := atom1683_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1683Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1684 : SparsePolynomial.Poly := [([13,18,19], 1)]
theorem eval_atom1684 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1684 = ((g 13) * (g 18) * (g 19)) := by
  norm_num [atom1684, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1684_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77891482429200 : Int) atom1684) := by
  rw [SparsePolynomial.eval_scale, eval_atom1684]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1684Coded : CoefficientMerge.Poly := [(6130, 1)]
theorem atom1684Coded_decode : atom1684 = SparsePolynomial.decodeCubic 21 atom1684Coded := by decide +kernel
theorem atom1684Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) := by
  have h := atom1684_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1684Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1685 : SparsePolynomial.Poly := [([13,18,20], 1)]
theorem eval_atom1685 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1685 = ((g 13) * (g 18) * (g 20)) := by
  norm_num [atom1685, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1685_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100837655654400 : Int) atom1685) := by
  rw [SparsePolynomial.eval_scale, eval_atom1685]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1685Coded : CoefficientMerge.Poly := [(6131, 1)]
theorem atom1685Coded_decode : atom1685 = SparsePolynomial.decodeCubic 21 atom1685Coded := by decide +kernel
theorem atom1685Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded) := by
  have h := atom1685_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1685Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1686 : SparsePolynomial.Poly := [([13,19,19], 1)]
theorem eval_atom1686 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1686 = ((g 13) * (g 19) * (g 19)) := by
  norm_num [atom1686, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1686_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36725564548800 : Int) atom1686) := by
  rw [SparsePolynomial.eval_scale, eval_atom1686]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1686Coded : CoefficientMerge.Poly := [(6151, 1)]
theorem atom1686Coded_decode : atom1686 = SparsePolynomial.decodeCubic 21 atom1686Coded := by decide +kernel
theorem atom1686Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) := by
  have h := atom1686_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1686Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1687 : SparsePolynomial.Poly := [([13,19,20], 1)]
theorem eval_atom1687 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1687 = ((g 13) * (g 19) * (g 20)) := by
  norm_num [atom1687, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1687_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99336377640600 : Int) atom1687) := by
  rw [SparsePolynomial.eval_scale, eval_atom1687]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1687Coded : CoefficientMerge.Poly := [(6152, 1)]
theorem atom1687Coded_decode : atom1687 = SparsePolynomial.decodeCubic 21 atom1687Coded := by decide +kernel
theorem atom1687Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded) := by
  have h := atom1687_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1687Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1688 : SparsePolynomial.Poly := [([13,20,20], 1)]
theorem eval_atom1688 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1688 = ((g 13) * (g 20) * (g 20)) := by
  norm_num [atom1688, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1688_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57215047680000 : Int) atom1688) := by
  rw [SparsePolynomial.eval_scale, eval_atom1688]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1688Coded : CoefficientMerge.Poly := [(6173, 1)]
theorem atom1688Coded_decode : atom1688 = SparsePolynomial.decodeCubic 21 atom1688Coded := by decide +kernel
theorem atom1688Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) := by
  have h := atom1688_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1688Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1689 : SparsePolynomial.Poly := [([14,14,14], 1)]
theorem eval_atom1689 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1689 = ((g 14) * (g 14) * (g 14)) := by
  norm_num [atom1689, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1689_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1735780838400 : Int) atom1689) := by
  rw [SparsePolynomial.eval_scale, eval_atom1689]
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 14) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1689Coded : CoefficientMerge.Poly := [(6482, 1)]
theorem atom1689Coded_decode : atom1689 = SparsePolynomial.decodeCubic 21 atom1689Coded := by decide +kernel
theorem atom1689Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) := by
  have h := atom1689_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1689Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1690 : SparsePolynomial.Poly := [([14,14,17], 1)]
theorem eval_atom1690 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1690 = ((g 14) * (g 14) * (g 17)) := by
  norm_num [atom1690, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1690_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13628959948800 : Int) atom1690) := by
  rw [SparsePolynomial.eval_scale, eval_atom1690]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1690Coded : CoefficientMerge.Poly := [(6485, 1)]
theorem atom1690Coded_decode : atom1690 = SparsePolynomial.decodeCubic 21 atom1690Coded := by decide +kernel
theorem atom1690Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded) := by
  have h := atom1690_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1690Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1691 : SparsePolynomial.Poly := [([14,14,18], 1)]
theorem eval_atom1691 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1691 = ((g 14) * (g 14) * (g 18)) := by
  norm_num [atom1691, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1691_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14833387699200 : Int) atom1691) := by
  rw [SparsePolynomial.eval_scale, eval_atom1691]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1691Coded : CoefficientMerge.Poly := [(6486, 1)]
theorem atom1691Coded_decode : atom1691 = SparsePolynomial.decodeCubic 21 atom1691Coded := by decide +kernel
theorem atom1691Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) := by
  have h := atom1691_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1691Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1692 : SparsePolynomial.Poly := [([14,14,19], 1)]
theorem eval_atom1692 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1692 = ((g 14) * (g 14) * (g 19)) := by
  norm_num [atom1692, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1692_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5586198912000 : Int) atom1692) := by
  rw [SparsePolynomial.eval_scale, eval_atom1692]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1692Coded : CoefficientMerge.Poly := [(6487, 1)]
theorem atom1692Coded_decode : atom1692 = SparsePolynomial.decodeCubic 21 atom1692Coded := by decide +kernel
theorem atom1692Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded) := by
  have h := atom1692_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1692Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1693 : SparsePolynomial.Poly := [([14,14,20], 1)]
theorem eval_atom1693 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1693 = ((g 14) * (g 14) * (g 20)) := by
  norm_num [atom1693, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1693_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20249487820800 : Int) atom1693) := by
  rw [SparsePolynomial.eval_scale, eval_atom1693]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1693Coded : CoefficientMerge.Poly := [(6488, 1)]
theorem atom1693Coded_decode : atom1693 = SparsePolynomial.decodeCubic 21 atom1693Coded := by decide +kernel
theorem atom1693Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) := by
  have h := atom1693_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1693Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1694 : SparsePolynomial.Poly := [([14,15,15], 1)]
theorem eval_atom1694 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1694 = ((g 14) * (g 15) * (g 15)) := by
  norm_num [atom1694, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1694_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (906549235200 : Int) atom1694) := by
  rw [SparsePolynomial.eval_scale, eval_atom1694]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 14) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1694Coded : CoefficientMerge.Poly := [(6504, 1)]
theorem atom1694Coded_decode : atom1694 = SparsePolynomial.decodeCubic 21 atom1694Coded := by decide +kernel
theorem atom1694Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) := by
  have h := atom1694_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1694Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1695 : SparsePolynomial.Poly := [([14,15,16], 1)]
theorem eval_atom1695 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1695 = ((g 14) * (g 15) * (g 16)) := by
  norm_num [atom1695, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1695_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9616380480000 : Int) atom1695) := by
  rw [SparsePolynomial.eval_scale, eval_atom1695]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1695Coded : CoefficientMerge.Poly := [(6505, 1)]
theorem atom1695Coded_decode : atom1695 = SparsePolynomial.decodeCubic 21 atom1695Coded := by decide +kernel
theorem atom1695Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded) := by
  have h := atom1695_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1695Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block022 : CoefficientMerge.Poly := [(5248, 58329956563200), (5249, 71135158752000), (5269, 16986153139200), (5270, 48554288496000), (5291, 27477786268800), (5556, 142393305600), (5561, 3961249152000), (5562, 657701004800), (5578, 731019801600), (5579, 718685798400), (5581, 781859212800), (5582, 16022245108800), (5583, 13551194686400), (5584, 11776027622400), (5585, 24502199198400), (5600, 3414217766400), (5602, 1274989228800), (5603, 25932352051200), (5604, 27709905507200), (5605, 27473854060800), (5606, 53106823627200), (5622, 6357299110400), (5623, 19520661753600), (5624, 54017265971200), (5625, 60723048870400), (5626, 48904332915200), (5627, 82971805996800), (5644, 7890507752960), (5645, 48082095084800), (5646, 63896669200000), (5647, 55239224230400), (5648, 78568808472000), (5666, 39256609548800), (5667, 80549880678400), (5668, 69215540800000), (5669, 88196267756800), (5688, 35739932211200), (5689, 67106442681600), (5690, 90606689488000), (5710, 25516823091200), (5711, 77437241660800), (5732, 47533761553600), (6019, 390177907200), (6023, 7496187508800), (6024, 6223620657600), (6026, 6958414296000), (6041, 1828838131200), (6043, 2672152588800), (6044, 28714425307200), (6045, 31318438795200), (6046, 20764754611200), (6047, 47303583076800), (6063, 3550208205600), (6064, 14159602504800), (6065, 50540795877600), (6066, 58714949336400), (6067, 44621368840800), (6068, 82584805073400), (6085, 5924850140160), (6086, 46603049565600), (6087, 64561905414000), (6088, 58431178094400), (6089, 83751050082600), (6107, 38700065779200), (6108, 81441252748800), (6109, 76619479413600), (6110, 96041823897600), (6129, 36760668134400), (6130, 77891482429200), (6131, 100837655654400), (6151, 36725564548800), (6152, 99336377640600), (6173, 57215047680000), (6482, 1735780838400), (6485, 13628959948800), (6486, 14833387699200), (6487, 5586198912000), (6488, 20249487820800), (6504, 906549235200), (6505, 9616380480000)]
theorem block022_data : block022 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded)))))))) := by decide +kernel
theorem block022_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block022 := by
  rw [block022_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1616Coded_nonneg g hg hA hB) (atom1617Coded_nonneg g hg hA hB)) (add_nonneg (atom1618Coded_nonneg g hg hA hB) (add_nonneg (atom1619Coded_nonneg g hg hA hB) (atom1620Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1621Coded_nonneg g hg hA hB) (atom1622Coded_nonneg g hg hA hB)) (add_nonneg (atom1623Coded_nonneg g hg hA hB) (add_nonneg (atom1624Coded_nonneg g hg hA hB) (atom1625Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1626Coded_nonneg g hg hA hB) (atom1627Coded_nonneg g hg hA hB)) (add_nonneg (atom1628Coded_nonneg g hg hA hB) (add_nonneg (atom1629Coded_nonneg g hg hA hB) (atom1630Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1631Coded_nonneg g hg hA hB) (atom1632Coded_nonneg g hg hA hB)) (add_nonneg (atom1633Coded_nonneg g hg hA hB) (add_nonneg (atom1634Coded_nonneg g hg hA hB) (atom1635Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1636Coded_nonneg g hg hA hB) (atom1637Coded_nonneg g hg hA hB)) (add_nonneg (atom1638Coded_nonneg g hg hA hB) (add_nonneg (atom1639Coded_nonneg g hg hA hB) (atom1640Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1641Coded_nonneg g hg hA hB) (atom1642Coded_nonneg g hg hA hB)) (add_nonneg (atom1643Coded_nonneg g hg hA hB) (add_nonneg (atom1644Coded_nonneg g hg hA hB) (atom1645Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1646Coded_nonneg g hg hA hB) (atom1647Coded_nonneg g hg hA hB)) (add_nonneg (atom1648Coded_nonneg g hg hA hB) (add_nonneg (atom1649Coded_nonneg g hg hA hB) (atom1650Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1651Coded_nonneg g hg hA hB) (atom1652Coded_nonneg g hg hA hB)) (add_nonneg (atom1653Coded_nonneg g hg hA hB) (add_nonneg (atom1654Coded_nonneg g hg hA hB) (atom1655Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1656Coded_nonneg g hg hA hB) (atom1657Coded_nonneg g hg hA hB)) (add_nonneg (atom1658Coded_nonneg g hg hA hB) (add_nonneg (atom1659Coded_nonneg g hg hA hB) (atom1660Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1661Coded_nonneg g hg hA hB) (atom1662Coded_nonneg g hg hA hB)) (add_nonneg (atom1663Coded_nonneg g hg hA hB) (add_nonneg (atom1664Coded_nonneg g hg hA hB) (atom1665Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1666Coded_nonneg g hg hA hB) (atom1667Coded_nonneg g hg hA hB)) (add_nonneg (atom1668Coded_nonneg g hg hA hB) (add_nonneg (atom1669Coded_nonneg g hg hA hB) (atom1670Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1671Coded_nonneg g hg hA hB) (atom1672Coded_nonneg g hg hA hB)) (add_nonneg (atom1673Coded_nonneg g hg hA hB) (add_nonneg (atom1674Coded_nonneg g hg hA hB) (atom1675Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1676Coded_nonneg g hg hA hB) (atom1677Coded_nonneg g hg hA hB)) (add_nonneg (atom1678Coded_nonneg g hg hA hB) (add_nonneg (atom1679Coded_nonneg g hg hA hB) (atom1680Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1681Coded_nonneg g hg hA hB) (atom1682Coded_nonneg g hg hA hB)) (add_nonneg (atom1683Coded_nonneg g hg hA hB) (add_nonneg (atom1684Coded_nonneg g hg hA hB) (atom1685Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1686Coded_nonneg g hg hA hB) (atom1687Coded_nonneg g hg hA hB)) (add_nonneg (atom1688Coded_nonneg g hg hA hB) (add_nonneg (atom1689Coded_nonneg g hg hA hB) (atom1690Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1691Coded_nonneg g hg hA hB) (atom1692Coded_nonneg g hg hA hB)) (add_nonneg (atom1693Coded_nonneg g hg hA hB) (add_nonneg (atom1694Coded_nonneg g hg hA hB) (atom1695Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
