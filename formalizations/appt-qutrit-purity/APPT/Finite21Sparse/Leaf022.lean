-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1616 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1616Coded : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 1))]
theorem atom1616Coded_decode : atom1616 = SparsePolynomial.decodeCubic 21 atom1616Coded := by decide +kernel
theorem atom1616Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) := by
  have h := atom1616_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1616Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1617 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1617Coded : CoefficientMerge.Poly := [(nat_lit 5249, Int.ofNat (nat_lit 1))]
theorem atom1617Coded_decode : atom1617 = SparsePolynomial.decodeCubic 21 atom1617Coded := by decide +kernel
theorem atom1617Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded) := by
  have h := atom1617_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1617Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1618 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1618 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1618 = ((g 11) * (g 19) * (g 19)) := by
  norm_num [atom1618, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1618_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16986153139200 : Int) atom1618) := by
  rw [SparsePolynomial.eval_scale, eval_atom1618]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 11) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1618Coded : CoefficientMerge.Poly := [(nat_lit 5269, Int.ofNat (nat_lit 1))]
theorem atom1618Coded_decode : atom1618 = SparsePolynomial.decodeCubic 21 atom1618Coded := by decide +kernel
theorem atom1618Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) := by
  have h := atom1618_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1618Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1619 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1619Coded : CoefficientMerge.Poly := [(nat_lit 5270, Int.ofNat (nat_lit 1))]
theorem atom1619Coded_decode : atom1619 = SparsePolynomial.decodeCubic 21 atom1619Coded := by decide +kernel
theorem atom1619Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) := by
  have h := atom1619_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1619Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1620 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1620 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1620 = ((g 11) * (g 20) * (g 20)) := by
  norm_num [atom1620, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1620_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27477786268800 : Int) atom1620) := by
  rw [SparsePolynomial.eval_scale, eval_atom1620]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 11) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1620Coded : CoefficientMerge.Poly := [(nat_lit 5291, Int.ofNat (nat_lit 1))]
theorem atom1620Coded_decode : atom1620 = SparsePolynomial.decodeCubic 21 atom1620Coded := by decide +kernel
theorem atom1620Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded) := by
  have h := atom1620_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1620Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1621 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1621 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1621 = ((g 12) * (g 12) * (g 12)) := by
  norm_num [atom1621, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1621_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142393305600 : Int) atom1621) := by
  rw [SparsePolynomial.eval_scale, eval_atom1621]
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 12) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1621Coded : CoefficientMerge.Poly := [(nat_lit 5556, Int.ofNat (nat_lit 1))]
theorem atom1621Coded_decode : atom1621 = SparsePolynomial.decodeCubic 21 atom1621Coded := by decide +kernel
theorem atom1621Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) := by
  have h := atom1621_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1621Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1622 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1622 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1622 = ((g 12) * (g 12) * (g 17)) := by
  norm_num [atom1622, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1622_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3961249152000 : Int) atom1622) := by
  rw [SparsePolynomial.eval_scale, eval_atom1622]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1622Coded : CoefficientMerge.Poly := [(nat_lit 5561, Int.ofNat (nat_lit 1))]
theorem atom1622Coded_decode : atom1622 = SparsePolynomial.decodeCubic 21 atom1622Coded := by decide +kernel
theorem atom1622Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded) := by
  have h := atom1622_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1622Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1623 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1623 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1623 = ((g 12) * (g 12) * (g 18)) := by
  norm_num [atom1623, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1623_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (657701004800 : Int) atom1623) := by
  rw [SparsePolynomial.eval_scale, eval_atom1623]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1623Coded : CoefficientMerge.Poly := [(nat_lit 5562, Int.ofNat (nat_lit 1))]
theorem atom1623Coded_decode : atom1623 = SparsePolynomial.decodeCubic 21 atom1623Coded := by decide +kernel
theorem atom1623Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) := by
  have h := atom1623_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1623Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1624 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1624 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1624 = ((g 12) * (g 13) * (g 13)) := by
  norm_num [atom1624, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1624_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (731019801600 : Int) atom1624) := by
  rw [SparsePolynomial.eval_scale, eval_atom1624]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1624Coded : CoefficientMerge.Poly := [(nat_lit 5578, Int.ofNat (nat_lit 1))]
theorem atom1624Coded_decode : atom1624 = SparsePolynomial.decodeCubic 21 atom1624Coded := by decide +kernel
theorem atom1624Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) := by
  have h := atom1624_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1624Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1625 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1625Coded : CoefficientMerge.Poly := [(nat_lit 5579, Int.ofNat (nat_lit 1))]
theorem atom1625Coded_decode : atom1625 = SparsePolynomial.decodeCubic 21 atom1625Coded := by decide +kernel
theorem atom1625Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded) := by
  have h := atom1625_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1625Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1626 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1626Coded : CoefficientMerge.Poly := [(nat_lit 5581, Int.ofNat (nat_lit 1))]
theorem atom1626Coded_decode : atom1626 = SparsePolynomial.decodeCubic 21 atom1626Coded := by decide +kernel
theorem atom1626Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) := by
  have h := atom1626_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1626Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1627 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1627Coded : CoefficientMerge.Poly := [(nat_lit 5582, Int.ofNat (nat_lit 1))]
theorem atom1627Coded_decode : atom1627 = SparsePolynomial.decodeCubic 21 atom1627Coded := by decide +kernel
theorem atom1627Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded) := by
  have h := atom1627_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1627Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1628 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1628Coded : CoefficientMerge.Poly := [(nat_lit 5583, Int.ofNat (nat_lit 1))]
theorem atom1628Coded_decode : atom1628 = SparsePolynomial.decodeCubic 21 atom1628Coded := by decide +kernel
theorem atom1628Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) := by
  have h := atom1628_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1628Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1629 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1629Coded : CoefficientMerge.Poly := [(nat_lit 5584, Int.ofNat (nat_lit 1))]
theorem atom1629Coded_decode : atom1629 = SparsePolynomial.decodeCubic 21 atom1629Coded := by decide +kernel
theorem atom1629Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) := by
  have h := atom1629_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1629Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1630 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1630Coded : CoefficientMerge.Poly := [(nat_lit 5585, Int.ofNat (nat_lit 1))]
theorem atom1630Coded_decode : atom1630 = SparsePolynomial.decodeCubic 21 atom1630Coded := by decide +kernel
theorem atom1630Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded) := by
  have h := atom1630_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1630Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1631 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1631 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1631 = ((g 12) * (g 14) * (g 14)) := by
  norm_num [atom1631, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1631_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3414217766400 : Int) atom1631) := by
  rw [SparsePolynomial.eval_scale, eval_atom1631]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1631Coded : CoefficientMerge.Poly := [(nat_lit 5600, Int.ofNat (nat_lit 1))]
theorem atom1631Coded_decode : atom1631 = SparsePolynomial.decodeCubic 21 atom1631Coded := by decide +kernel
theorem atom1631Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) := by
  have h := atom1631_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1631Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1632 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1632Coded : CoefficientMerge.Poly := [(nat_lit 5602, Int.ofNat (nat_lit 1))]
theorem atom1632Coded_decode : atom1632 = SparsePolynomial.decodeCubic 21 atom1632Coded := by decide +kernel
theorem atom1632Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded) := by
  have h := atom1632_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1632Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1633 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1633Coded : CoefficientMerge.Poly := [(nat_lit 5603, Int.ofNat (nat_lit 1))]
theorem atom1633Coded_decode : atom1633 = SparsePolynomial.decodeCubic 21 atom1633Coded := by decide +kernel
theorem atom1633Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) := by
  have h := atom1633_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1633Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1634 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1634Coded : CoefficientMerge.Poly := [(nat_lit 5604, Int.ofNat (nat_lit 1))]
theorem atom1634Coded_decode : atom1634 = SparsePolynomial.decodeCubic 21 atom1634Coded := by decide +kernel
theorem atom1634Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) := by
  have h := atom1634_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1634Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1635 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1635Coded : CoefficientMerge.Poly := [(nat_lit 5605, Int.ofNat (nat_lit 1))]
theorem atom1635Coded_decode : atom1635 = SparsePolynomial.decodeCubic 21 atom1635Coded := by decide +kernel
theorem atom1635Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded) := by
  have h := atom1635_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1635Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1636 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1636Coded : CoefficientMerge.Poly := [(nat_lit 5606, Int.ofNat (nat_lit 1))]
theorem atom1636Coded_decode : atom1636 = SparsePolynomial.decodeCubic 21 atom1636Coded := by decide +kernel
theorem atom1636Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) := by
  have h := atom1636_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1636Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1637 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1637 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1637 = ((g 12) * (g 15) * (g 15)) := by
  norm_num [atom1637, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1637_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6357299110400 : Int) atom1637) := by
  rw [SparsePolynomial.eval_scale, eval_atom1637]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1637Coded : CoefficientMerge.Poly := [(nat_lit 5622, Int.ofNat (nat_lit 1))]
theorem atom1637Coded_decode : atom1637 = SparsePolynomial.decodeCubic 21 atom1637Coded := by decide +kernel
theorem atom1637Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded) := by
  have h := atom1637_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1637Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1638 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1638Coded : CoefficientMerge.Poly := [(nat_lit 5623, Int.ofNat (nat_lit 1))]
theorem atom1638Coded_decode : atom1638 = SparsePolynomial.decodeCubic 21 atom1638Coded := by decide +kernel
theorem atom1638Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) := by
  have h := atom1638_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1638Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1639 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1639Coded : CoefficientMerge.Poly := [(nat_lit 5624, Int.ofNat (nat_lit 1))]
theorem atom1639Coded_decode : atom1639 = SparsePolynomial.decodeCubic 21 atom1639Coded := by decide +kernel
theorem atom1639Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) := by
  have h := atom1639_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1639Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1640 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1640Coded : CoefficientMerge.Poly := [(nat_lit 5625, Int.ofNat (nat_lit 1))]
theorem atom1640Coded_decode : atom1640 = SparsePolynomial.decodeCubic 21 atom1640Coded := by decide +kernel
theorem atom1640Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded) := by
  have h := atom1640_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1640Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1641 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1641Coded : CoefficientMerge.Poly := [(nat_lit 5626, Int.ofNat (nat_lit 1))]
theorem atom1641Coded_decode : atom1641 = SparsePolynomial.decodeCubic 21 atom1641Coded := by decide +kernel
theorem atom1641Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) := by
  have h := atom1641_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1641Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1642 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1642Coded : CoefficientMerge.Poly := [(nat_lit 5627, Int.ofNat (nat_lit 1))]
theorem atom1642Coded_decode : atom1642 = SparsePolynomial.decodeCubic 21 atom1642Coded := by decide +kernel
theorem atom1642Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded) := by
  have h := atom1642_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1642Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1643 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1643 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1643 = ((g 12) * (g 16) * (g 16)) := by
  norm_num [atom1643, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1643_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7890507752960 : Int) atom1643) := by
  rw [SparsePolynomial.eval_scale, eval_atom1643]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1643Coded : CoefficientMerge.Poly := [(nat_lit 5644, Int.ofNat (nat_lit 1))]
theorem atom1643Coded_decode : atom1643 = SparsePolynomial.decodeCubic 21 atom1643Coded := by decide +kernel
theorem atom1643Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) := by
  have h := atom1643_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1643Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1644 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1644Coded : CoefficientMerge.Poly := [(nat_lit 5645, Int.ofNat (nat_lit 1))]
theorem atom1644Coded_decode : atom1644 = SparsePolynomial.decodeCubic 21 atom1644Coded := by decide +kernel
theorem atom1644Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) := by
  have h := atom1644_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1644Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1645 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1645Coded : CoefficientMerge.Poly := [(nat_lit 5646, Int.ofNat (nat_lit 1))]
theorem atom1645Coded_decode : atom1645 = SparsePolynomial.decodeCubic 21 atom1645Coded := by decide +kernel
theorem atom1645Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded) := by
  have h := atom1645_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1645Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1646 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1646Coded : CoefficientMerge.Poly := [(nat_lit 5647, Int.ofNat (nat_lit 1))]
theorem atom1646Coded_decode : atom1646 = SparsePolynomial.decodeCubic 21 atom1646Coded := by decide +kernel
theorem atom1646Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) := by
  have h := atom1646_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1646Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1647 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1647Coded : CoefficientMerge.Poly := [(nat_lit 5648, Int.ofNat (nat_lit 1))]
theorem atom1647Coded_decode : atom1647 = SparsePolynomial.decodeCubic 21 atom1647Coded := by decide +kernel
theorem atom1647Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded) := by
  have h := atom1647_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1647Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1648 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1648 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1648 = ((g 12) * (g 17) * (g 17)) := by
  norm_num [atom1648, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1648_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39256609548800 : Int) atom1648) := by
  rw [SparsePolynomial.eval_scale, eval_atom1648]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1648Coded : CoefficientMerge.Poly := [(nat_lit 5666, Int.ofNat (nat_lit 1))]
theorem atom1648Coded_decode : atom1648 = SparsePolynomial.decodeCubic 21 atom1648Coded := by decide +kernel
theorem atom1648Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) := by
  have h := atom1648_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1648Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1649 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1649Coded : CoefficientMerge.Poly := [(nat_lit 5667, Int.ofNat (nat_lit 1))]
theorem atom1649Coded_decode : atom1649 = SparsePolynomial.decodeCubic 21 atom1649Coded := by decide +kernel
theorem atom1649Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) := by
  have h := atom1649_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1649Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1650 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1650Coded : CoefficientMerge.Poly := [(nat_lit 5668, Int.ofNat (nat_lit 1))]
theorem atom1650Coded_decode : atom1650 = SparsePolynomial.decodeCubic 21 atom1650Coded := by decide +kernel
theorem atom1650Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded) := by
  have h := atom1650_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1650Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1651 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1651Coded : CoefficientMerge.Poly := [(nat_lit 5669, Int.ofNat (nat_lit 1))]
theorem atom1651Coded_decode : atom1651 = SparsePolynomial.decodeCubic 21 atom1651Coded := by decide +kernel
theorem atom1651Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) := by
  have h := atom1651_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1651Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1652 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1652 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1652 = ((g 12) * (g 18) * (g 18)) := by
  norm_num [atom1652, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1652_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35739932211200 : Int) atom1652) := by
  rw [SparsePolynomial.eval_scale, eval_atom1652]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 12) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1652Coded : CoefficientMerge.Poly := [(nat_lit 5688, Int.ofNat (nat_lit 1))]
theorem atom1652Coded_decode : atom1652 = SparsePolynomial.decodeCubic 21 atom1652Coded := by decide +kernel
theorem atom1652Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded) := by
  have h := atom1652_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1652Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1653 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1653Coded : CoefficientMerge.Poly := [(nat_lit 5689, Int.ofNat (nat_lit 1))]
theorem atom1653Coded_decode : atom1653 = SparsePolynomial.decodeCubic 21 atom1653Coded := by decide +kernel
theorem atom1653Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) := by
  have h := atom1653_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1653Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1654 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1654Coded : CoefficientMerge.Poly := [(nat_lit 5690, Int.ofNat (nat_lit 1))]
theorem atom1654Coded_decode : atom1654 = SparsePolynomial.decodeCubic 21 atom1654Coded := by decide +kernel
theorem atom1654Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) := by
  have h := atom1654_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1654Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1655 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1655 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1655 = ((g 12) * (g 19) * (g 19)) := by
  norm_num [atom1655, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1655_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25516823091200 : Int) atom1655) := by
  rw [SparsePolynomial.eval_scale, eval_atom1655]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 12) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1655Coded : CoefficientMerge.Poly := [(nat_lit 5710, Int.ofNat (nat_lit 1))]
theorem atom1655Coded_decode : atom1655 = SparsePolynomial.decodeCubic 21 atom1655Coded := by decide +kernel
theorem atom1655Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded) := by
  have h := atom1655_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1655Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1656 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1656Coded : CoefficientMerge.Poly := [(nat_lit 5711, Int.ofNat (nat_lit 1))]
theorem atom1656Coded_decode : atom1656 = SparsePolynomial.decodeCubic 21 atom1656Coded := by decide +kernel
theorem atom1656Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) := by
  have h := atom1656_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1656Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1657 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1657 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1657 = ((g 12) * (g 20) * (g 20)) := by
  norm_num [atom1657, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1657_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47533761553600 : Int) atom1657) := by
  rw [SparsePolynomial.eval_scale, eval_atom1657]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 12) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1657Coded : CoefficientMerge.Poly := [(nat_lit 5732, Int.ofNat (nat_lit 1))]
theorem atom1657Coded_decode : atom1657 = SparsePolynomial.decodeCubic 21 atom1657Coded := by decide +kernel
theorem atom1657Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded) := by
  have h := atom1657_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1657Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1658 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1658 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1658 = ((g 13) * (g 13) * (g 13)) := by
  norm_num [atom1658, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1658_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (390177907200 : Int) atom1658) := by
  rw [SparsePolynomial.eval_scale, eval_atom1658]
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 13) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1658Coded : CoefficientMerge.Poly := [(nat_lit 6019, Int.ofNat (nat_lit 1))]
theorem atom1658Coded_decode : atom1658 = SparsePolynomial.decodeCubic 21 atom1658Coded := by decide +kernel
theorem atom1658Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) := by
  have h := atom1658_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1658Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1659 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1659 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1659 = ((g 13) * (g 13) * (g 17)) := by
  norm_num [atom1659, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1659_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7496187508800 : Int) atom1659) := by
  rw [SparsePolynomial.eval_scale, eval_atom1659]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1659Coded : CoefficientMerge.Poly := [(nat_lit 6023, Int.ofNat (nat_lit 1))]
theorem atom1659Coded_decode : atom1659 = SparsePolynomial.decodeCubic 21 atom1659Coded := by decide +kernel
theorem atom1659Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) := by
  have h := atom1659_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1659Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1660 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1660 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1660 = ((g 13) * (g 13) * (g 18)) := by
  norm_num [atom1660, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1660_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6223620657600 : Int) atom1660) := by
  rw [SparsePolynomial.eval_scale, eval_atom1660]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1660Coded : CoefficientMerge.Poly := [(nat_lit 6024, Int.ofNat (nat_lit 1))]
theorem atom1660Coded_decode : atom1660 = SparsePolynomial.decodeCubic 21 atom1660Coded := by decide +kernel
theorem atom1660Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded) := by
  have h := atom1660_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1660Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1661 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1661 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1661 = ((g 13) * (g 13) * (g 20)) := by
  norm_num [atom1661, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1661_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6958414296000 : Int) atom1661) := by
  rw [SparsePolynomial.eval_scale, eval_atom1661]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1661Coded : CoefficientMerge.Poly := [(nat_lit 6026, Int.ofNat (nat_lit 1))]
theorem atom1661Coded_decode : atom1661 = SparsePolynomial.decodeCubic 21 atom1661Coded := by decide +kernel
theorem atom1661Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) := by
  have h := atom1661_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1661Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1662 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1662 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1662 = ((g 13) * (g 14) * (g 14)) := by
  norm_num [atom1662, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1662_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1828838131200 : Int) atom1662) := by
  rw [SparsePolynomial.eval_scale, eval_atom1662]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1662Coded : CoefficientMerge.Poly := [(nat_lit 6041, Int.ofNat (nat_lit 1))]
theorem atom1662Coded_decode : atom1662 = SparsePolynomial.decodeCubic 21 atom1662Coded := by decide +kernel
theorem atom1662Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded) := by
  have h := atom1662_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1662Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1663 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1663Coded : CoefficientMerge.Poly := [(nat_lit 6043, Int.ofNat (nat_lit 1))]
theorem atom1663Coded_decode : atom1663 = SparsePolynomial.decodeCubic 21 atom1663Coded := by decide +kernel
theorem atom1663Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) := by
  have h := atom1663_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1663Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1664 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1664Coded : CoefficientMerge.Poly := [(nat_lit 6044, Int.ofNat (nat_lit 1))]
theorem atom1664Coded_decode : atom1664 = SparsePolynomial.decodeCubic 21 atom1664Coded := by decide +kernel
theorem atom1664Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) := by
  have h := atom1664_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1664Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1665 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1665Coded : CoefficientMerge.Poly := [(nat_lit 6045, Int.ofNat (nat_lit 1))]
theorem atom1665Coded_decode : atom1665 = SparsePolynomial.decodeCubic 21 atom1665Coded := by decide +kernel
theorem atom1665Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded) := by
  have h := atom1665_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1665Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1666 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1666Coded : CoefficientMerge.Poly := [(nat_lit 6046, Int.ofNat (nat_lit 1))]
theorem atom1666Coded_decode : atom1666 = SparsePolynomial.decodeCubic 21 atom1666Coded := by decide +kernel
theorem atom1666Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) := by
  have h := atom1666_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1666Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1667 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1667Coded : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 1))]
theorem atom1667Coded_decode : atom1667 = SparsePolynomial.decodeCubic 21 atom1667Coded := by decide +kernel
theorem atom1667Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded) := by
  have h := atom1667_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1667Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1668 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1668 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1668 = ((g 13) * (g 15) * (g 15)) := by
  norm_num [atom1668, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1668_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3550208205600 : Int) atom1668) := by
  rw [SparsePolynomial.eval_scale, eval_atom1668]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1668Coded : CoefficientMerge.Poly := [(nat_lit 6063, Int.ofNat (nat_lit 1))]
theorem atom1668Coded_decode : atom1668 = SparsePolynomial.decodeCubic 21 atom1668Coded := by decide +kernel
theorem atom1668Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) := by
  have h := atom1668_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1668Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1669 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1669Coded : CoefficientMerge.Poly := [(nat_lit 6064, Int.ofNat (nat_lit 1))]
theorem atom1669Coded_decode : atom1669 = SparsePolynomial.decodeCubic 21 atom1669Coded := by decide +kernel
theorem atom1669Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) := by
  have h := atom1669_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1669Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1670 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1670Coded : CoefficientMerge.Poly := [(nat_lit 6065, Int.ofNat (nat_lit 1))]
theorem atom1670Coded_decode : atom1670 = SparsePolynomial.decodeCubic 21 atom1670Coded := by decide +kernel
theorem atom1670Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded) := by
  have h := atom1670_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1670Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1671 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1671Coded : CoefficientMerge.Poly := [(nat_lit 6066, Int.ofNat (nat_lit 1))]
theorem atom1671Coded_decode : atom1671 = SparsePolynomial.decodeCubic 21 atom1671Coded := by decide +kernel
theorem atom1671Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) := by
  have h := atom1671_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1671Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1672 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1672Coded : CoefficientMerge.Poly := [(nat_lit 6067, Int.ofNat (nat_lit 1))]
theorem atom1672Coded_decode : atom1672 = SparsePolynomial.decodeCubic 21 atom1672Coded := by decide +kernel
theorem atom1672Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded) := by
  have h := atom1672_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1672Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1673 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1673Coded : CoefficientMerge.Poly := [(nat_lit 6068, Int.ofNat (nat_lit 1))]
theorem atom1673Coded_decode : atom1673 = SparsePolynomial.decodeCubic 21 atom1673Coded := by decide +kernel
theorem atom1673Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) := by
  have h := atom1673_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1673Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1674 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1674 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1674 = ((g 13) * (g 16) * (g 16)) := by
  norm_num [atom1674, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1674_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5924850140160 : Int) atom1674) := by
  rw [SparsePolynomial.eval_scale, eval_atom1674]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1674Coded : CoefficientMerge.Poly := [(nat_lit 6085, Int.ofNat (nat_lit 1))]
theorem atom1674Coded_decode : atom1674 = SparsePolynomial.decodeCubic 21 atom1674Coded := by decide +kernel
theorem atom1674Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) := by
  have h := atom1674_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1674Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1675 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1675Coded : CoefficientMerge.Poly := [(nat_lit 6086, Int.ofNat (nat_lit 1))]
theorem atom1675Coded_decode : atom1675 = SparsePolynomial.decodeCubic 21 atom1675Coded := by decide +kernel
theorem atom1675Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded) := by
  have h := atom1675_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1675Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1676 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1676Coded : CoefficientMerge.Poly := [(nat_lit 6087, Int.ofNat (nat_lit 1))]
theorem atom1676Coded_decode : atom1676 = SparsePolynomial.decodeCubic 21 atom1676Coded := by decide +kernel
theorem atom1676Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) := by
  have h := atom1676_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1676Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1677 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1677Coded : CoefficientMerge.Poly := [(nat_lit 6088, Int.ofNat (nat_lit 1))]
theorem atom1677Coded_decode : atom1677 = SparsePolynomial.decodeCubic 21 atom1677Coded := by decide +kernel
theorem atom1677Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded) := by
  have h := atom1677_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1677Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1678 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1678Coded : CoefficientMerge.Poly := [(nat_lit 6089, Int.ofNat (nat_lit 1))]
theorem atom1678Coded_decode : atom1678 = SparsePolynomial.decodeCubic 21 atom1678Coded := by decide +kernel
theorem atom1678Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) := by
  have h := atom1678_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1678Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1679 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1679 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1679 = ((g 13) * (g 17) * (g 17)) := by
  norm_num [atom1679, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1679_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38700065779200 : Int) atom1679) := by
  rw [SparsePolynomial.eval_scale, eval_atom1679]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1679Coded : CoefficientMerge.Poly := [(nat_lit 6107, Int.ofNat (nat_lit 1))]
theorem atom1679Coded_decode : atom1679 = SparsePolynomial.decodeCubic 21 atom1679Coded := by decide +kernel
theorem atom1679Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) := by
  have h := atom1679_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1679Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1680 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1680Coded : CoefficientMerge.Poly := [(nat_lit 6108, Int.ofNat (nat_lit 1))]
theorem atom1680Coded_decode : atom1680 = SparsePolynomial.decodeCubic 21 atom1680Coded := by decide +kernel
theorem atom1680Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded) := by
  have h := atom1680_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1680Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1681 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1681Coded : CoefficientMerge.Poly := [(nat_lit 6109, Int.ofNat (nat_lit 1))]
theorem atom1681Coded_decode : atom1681 = SparsePolynomial.decodeCubic 21 atom1681Coded := by decide +kernel
theorem atom1681Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) := by
  have h := atom1681_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1681Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1682 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1682Coded : CoefficientMerge.Poly := [(nat_lit 6110, Int.ofNat (nat_lit 1))]
theorem atom1682Coded_decode : atom1682 = SparsePolynomial.decodeCubic 21 atom1682Coded := by decide +kernel
theorem atom1682Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded) := by
  have h := atom1682_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1682Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1683 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1683 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1683 = ((g 13) * (g 18) * (g 18)) := by
  norm_num [atom1683, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1683_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36760668134400 : Int) atom1683) := by
  rw [SparsePolynomial.eval_scale, eval_atom1683]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 13) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1683Coded : CoefficientMerge.Poly := [(nat_lit 6129, Int.ofNat (nat_lit 1))]
theorem atom1683Coded_decode : atom1683 = SparsePolynomial.decodeCubic 21 atom1683Coded := by decide +kernel
theorem atom1683Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) := by
  have h := atom1683_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1683Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1684 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1684Coded : CoefficientMerge.Poly := [(nat_lit 6130, Int.ofNat (nat_lit 1))]
theorem atom1684Coded_decode : atom1684 = SparsePolynomial.decodeCubic 21 atom1684Coded := by decide +kernel
theorem atom1684Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) := by
  have h := atom1684_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1684Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1685 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1685Coded : CoefficientMerge.Poly := [(nat_lit 6131, Int.ofNat (nat_lit 1))]
theorem atom1685Coded_decode : atom1685 = SparsePolynomial.decodeCubic 21 atom1685Coded := by decide +kernel
theorem atom1685Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded) := by
  have h := atom1685_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1685Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1686 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1686 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1686 = ((g 13) * (g 19) * (g 19)) := by
  norm_num [atom1686, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1686_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36725564548800 : Int) atom1686) := by
  rw [SparsePolynomial.eval_scale, eval_atom1686]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 13) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1686Coded : CoefficientMerge.Poly := [(nat_lit 6151, Int.ofNat (nat_lit 1))]
theorem atom1686Coded_decode : atom1686 = SparsePolynomial.decodeCubic 21 atom1686Coded := by decide +kernel
theorem atom1686Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) := by
  have h := atom1686_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1686Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1687 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1687Coded : CoefficientMerge.Poly := [(nat_lit 6152, Int.ofNat (nat_lit 1))]
theorem atom1687Coded_decode : atom1687 = SparsePolynomial.decodeCubic 21 atom1687Coded := by decide +kernel
theorem atom1687Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded) := by
  have h := atom1687_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1687Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1688 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1688 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1688 = ((g 13) * (g 20) * (g 20)) := by
  norm_num [atom1688, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1688_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57215047680000 : Int) atom1688) := by
  rw [SparsePolynomial.eval_scale, eval_atom1688]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 13) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1688Coded : CoefficientMerge.Poly := [(nat_lit 6173, Int.ofNat (nat_lit 1))]
theorem atom1688Coded_decode : atom1688 = SparsePolynomial.decodeCubic 21 atom1688Coded := by decide +kernel
theorem atom1688Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) := by
  have h := atom1688_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1688Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1689 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1689 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1689 = ((g 14) * (g 14) * (g 14)) := by
  norm_num [atom1689, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1689_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1735780838400 : Int) atom1689) := by
  rw [SparsePolynomial.eval_scale, eval_atom1689]
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 14) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1689Coded : CoefficientMerge.Poly := [(nat_lit 6482, Int.ofNat (nat_lit 1))]
theorem atom1689Coded_decode : atom1689 = SparsePolynomial.decodeCubic 21 atom1689Coded := by decide +kernel
theorem atom1689Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) := by
  have h := atom1689_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1689Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1690 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1690 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1690 = ((g 14) * (g 14) * (g 17)) := by
  norm_num [atom1690, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1690_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13628959948800 : Int) atom1690) := by
  rw [SparsePolynomial.eval_scale, eval_atom1690]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1690Coded : CoefficientMerge.Poly := [(nat_lit 6485, Int.ofNat (nat_lit 1))]
theorem atom1690Coded_decode : atom1690 = SparsePolynomial.decodeCubic 21 atom1690Coded := by decide +kernel
theorem atom1690Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded) := by
  have h := atom1690_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1690Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1691 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1691 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1691 = ((g 14) * (g 14) * (g 18)) := by
  norm_num [atom1691, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1691_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14833387699200 : Int) atom1691) := by
  rw [SparsePolynomial.eval_scale, eval_atom1691]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 14) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1691Coded : CoefficientMerge.Poly := [(nat_lit 6486, Int.ofNat (nat_lit 1))]
theorem atom1691Coded_decode : atom1691 = SparsePolynomial.decodeCubic 21 atom1691Coded := by decide +kernel
theorem atom1691Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) := by
  have h := atom1691_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1691Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1692 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1692 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1692 = ((g 14) * (g 14) * (g 19)) := by
  norm_num [atom1692, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1692_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5586198912000 : Int) atom1692) := by
  rw [SparsePolynomial.eval_scale, eval_atom1692]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 14) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1692Coded : CoefficientMerge.Poly := [(nat_lit 6487, Int.ofNat (nat_lit 1))]
theorem atom1692Coded_decode : atom1692 = SparsePolynomial.decodeCubic 21 atom1692Coded := by decide +kernel
theorem atom1692Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded) := by
  have h := atom1692_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1692Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1693 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1693 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1693 = ((g 14) * (g 14) * (g 20)) := by
  norm_num [atom1693, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1693_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20249487820800 : Int) atom1693) := by
  rw [SparsePolynomial.eval_scale, eval_atom1693]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 14) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1693Coded : CoefficientMerge.Poly := [(nat_lit 6488, Int.ofNat (nat_lit 1))]
theorem atom1693Coded_decode : atom1693 = SparsePolynomial.decodeCubic 21 atom1693Coded := by decide +kernel
theorem atom1693Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) := by
  have h := atom1693_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1693Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1694 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1694 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1694 = ((g 14) * (g 15) * (g 15)) := by
  norm_num [atom1694, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1694_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (906549235200 : Int) atom1694) := by
  rw [SparsePolynomial.eval_scale, eval_atom1694]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 14) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1694Coded : CoefficientMerge.Poly := [(nat_lit 6504, Int.ofNat (nat_lit 1))]
theorem atom1694Coded_decode : atom1694 = SparsePolynomial.decodeCubic 21 atom1694Coded := by decide +kernel
theorem atom1694Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) := by
  have h := atom1694_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1694Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1695 : SparsePolynomial.Poly := [([nat_lit 14, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1695Coded : CoefficientMerge.Poly := [(nat_lit 6505, Int.ofNat (nat_lit 1))]
theorem atom1695Coded_decode : atom1695 = SparsePolynomial.decodeCubic 21 atom1695Coded := by decide +kernel
theorem atom1695Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded) := by
  have h := atom1695_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1695Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block022 : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 58329956563200)), (nat_lit 5249, Int.ofNat (nat_lit 71135158752000)), (nat_lit 5269, Int.ofNat (nat_lit 16986153139200)), (nat_lit 5270, Int.ofNat (nat_lit 48554288496000)), (nat_lit 5291, Int.ofNat (nat_lit 27477786268800)), (nat_lit 5556, Int.ofNat (nat_lit 142393305600)), (nat_lit 5561, Int.ofNat (nat_lit 3961249152000)), (nat_lit 5562, Int.ofNat (nat_lit 657701004800)), (nat_lit 5578, Int.ofNat (nat_lit 731019801600)), (nat_lit 5579, Int.ofNat (nat_lit 718685798400)), (nat_lit 5581, Int.ofNat (nat_lit 781859212800)), (nat_lit 5582, Int.ofNat (nat_lit 16022245108800)), (nat_lit 5583, Int.ofNat (nat_lit 13551194686400)), (nat_lit 5584, Int.ofNat (nat_lit 11776027622400)), (nat_lit 5585, Int.ofNat (nat_lit 24502199198400)), (nat_lit 5600, Int.ofNat (nat_lit 3414217766400)), (nat_lit 5602, Int.ofNat (nat_lit 1274989228800)), (nat_lit 5603, Int.ofNat (nat_lit 25932352051200)), (nat_lit 5604, Int.ofNat (nat_lit 27709905507200)), (nat_lit 5605, Int.ofNat (nat_lit 27473854060800)), (nat_lit 5606, Int.ofNat (nat_lit 53106823627200)), (nat_lit 5622, Int.ofNat (nat_lit 6357299110400)), (nat_lit 5623, Int.ofNat (nat_lit 19520661753600)), (nat_lit 5624, Int.ofNat (nat_lit 54017265971200)), (nat_lit 5625, Int.ofNat (nat_lit 60723048870400)), (nat_lit 5626, Int.ofNat (nat_lit 48904332915200)), (nat_lit 5627, Int.ofNat (nat_lit 82971805996800)), (nat_lit 5644, Int.ofNat (nat_lit 7890507752960)), (nat_lit 5645, Int.ofNat (nat_lit 48082095084800)), (nat_lit 5646, Int.ofNat (nat_lit 63896669200000)), (nat_lit 5647, Int.ofNat (nat_lit 55239224230400)), (nat_lit 5648, Int.ofNat (nat_lit 78568808472000)), (nat_lit 5666, Int.ofNat (nat_lit 39256609548800)), (nat_lit 5667, Int.ofNat (nat_lit 80549880678400)), (nat_lit 5668, Int.ofNat (nat_lit 69215540800000)), (nat_lit 5669, Int.ofNat (nat_lit 88196267756800)), (nat_lit 5688, Int.ofNat (nat_lit 35739932211200)), (nat_lit 5689, Int.ofNat (nat_lit 67106442681600)), (nat_lit 5690, Int.ofNat (nat_lit 90606689488000)), (nat_lit 5710, Int.ofNat (nat_lit 25516823091200)), (nat_lit 5711, Int.ofNat (nat_lit 77437241660800)), (nat_lit 5732, Int.ofNat (nat_lit 47533761553600)), (nat_lit 6019, Int.ofNat (nat_lit 390177907200)), (nat_lit 6023, Int.ofNat (nat_lit 7496187508800)), (nat_lit 6024, Int.ofNat (nat_lit 6223620657600)), (nat_lit 6026, Int.ofNat (nat_lit 6958414296000)), (nat_lit 6041, Int.ofNat (nat_lit 1828838131200)), (nat_lit 6043, Int.ofNat (nat_lit 2672152588800)), (nat_lit 6044, Int.ofNat (nat_lit 28714425307200)), (nat_lit 6045, Int.ofNat (nat_lit 31318438795200)), (nat_lit 6046, Int.ofNat (nat_lit 20764754611200)), (nat_lit 6047, Int.ofNat (nat_lit 47303583076800)), (nat_lit 6063, Int.ofNat (nat_lit 3550208205600)), (nat_lit 6064, Int.ofNat (nat_lit 14159602504800)), (nat_lit 6065, Int.ofNat (nat_lit 50540795877600)), (nat_lit 6066, Int.ofNat (nat_lit 58714949336400)), (nat_lit 6067, Int.ofNat (nat_lit 44621368840800)), (nat_lit 6068, Int.ofNat (nat_lit 82584805073400)), (nat_lit 6085, Int.ofNat (nat_lit 5924850140160)), (nat_lit 6086, Int.ofNat (nat_lit 46603049565600)), (nat_lit 6087, Int.ofNat (nat_lit 64561905414000)), (nat_lit 6088, Int.ofNat (nat_lit 58431178094400)), (nat_lit 6089, Int.ofNat (nat_lit 83751050082600)), (nat_lit 6107, Int.ofNat (nat_lit 38700065779200)), (nat_lit 6108, Int.ofNat (nat_lit 81441252748800)), (nat_lit 6109, Int.ofNat (nat_lit 76619479413600)), (nat_lit 6110, Int.ofNat (nat_lit 96041823897600)), (nat_lit 6129, Int.ofNat (nat_lit 36760668134400)), (nat_lit 6130, Int.ofNat (nat_lit 77891482429200)), (nat_lit 6131, Int.ofNat (nat_lit 100837655654400)), (nat_lit 6151, Int.ofNat (nat_lit 36725564548800)), (nat_lit 6152, Int.ofNat (nat_lit 99336377640600)), (nat_lit 6173, Int.ofNat (nat_lit 57215047680000)), (nat_lit 6482, Int.ofNat (nat_lit 1735780838400)), (nat_lit 6485, Int.ofNat (nat_lit 13628959948800)), (nat_lit 6486, Int.ofNat (nat_lit 14833387699200)), (nat_lit 6487, Int.ofNat (nat_lit 5586198912000)), (nat_lit 6488, Int.ofNat (nat_lit 20249487820800)), (nat_lit 6504, Int.ofNat (nat_lit 906549235200)), (nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
def block022_data_flat000 : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 58329956563200))]
theorem block022_data_flat000_step : block022_data_flat000 = (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) := by decide +kernel
theorem block022_data_flat000_original : block022_data_flat000 = (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) := by
  rw [block022_data_flat000_step]
def block022_data_flat001 : CoefficientMerge.Poly := [(nat_lit 5249, Int.ofNat (nat_lit 71135158752000))]
theorem block022_data_flat001_step : block022_data_flat001 = (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded) := by decide +kernel
theorem block022_data_flat001_original : block022_data_flat001 = (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded) := by
  rw [block022_data_flat001_step]
def block022_data_flat002 : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 58329956563200)), (nat_lit 5249, Int.ofNat (nat_lit 71135158752000))]
theorem block022_data_flat002_step : block022_data_flat002 = (CoefficientMerge.fastMerge block022_data_flat000 block022_data_flat001) := by decide +kernel
theorem block022_data_flat002_original : block022_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded)) := by
  rw [block022_data_flat002_step, block022_data_flat000_original, block022_data_flat001_original]
def block022_data_flat003 : CoefficientMerge.Poly := [(nat_lit 5269, Int.ofNat (nat_lit 16986153139200))]
theorem block022_data_flat003_step : block022_data_flat003 = (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) := by decide +kernel
theorem block022_data_flat003_original : block022_data_flat003 = (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) := by
  rw [block022_data_flat003_step]
def block022_data_flat004 : CoefficientMerge.Poly := [(nat_lit 5270, Int.ofNat (nat_lit 48554288496000))]
theorem block022_data_flat004_step : block022_data_flat004 = (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) := by decide +kernel
theorem block022_data_flat004_original : block022_data_flat004 = (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) := by
  rw [block022_data_flat004_step]
def block022_data_flat005 : CoefficientMerge.Poly := [(nat_lit 5291, Int.ofNat (nat_lit 27477786268800))]
theorem block022_data_flat005_step : block022_data_flat005 = (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded) := by decide +kernel
theorem block022_data_flat005_original : block022_data_flat005 = (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded) := by
  rw [block022_data_flat005_step]
def block022_data_flat006 : CoefficientMerge.Poly := [(nat_lit 5270, Int.ofNat (nat_lit 48554288496000)), (nat_lit 5291, Int.ofNat (nat_lit 27477786268800))]
theorem block022_data_flat006_step : block022_data_flat006 = (CoefficientMerge.fastMerge block022_data_flat004 block022_data_flat005) := by decide +kernel
theorem block022_data_flat006_original : block022_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded)) := by
  rw [block022_data_flat006_step, block022_data_flat004_original, block022_data_flat005_original]
def block022_data_flat007 : CoefficientMerge.Poly := [(nat_lit 5269, Int.ofNat (nat_lit 16986153139200)), (nat_lit 5270, Int.ofNat (nat_lit 48554288496000)), (nat_lit 5291, Int.ofNat (nat_lit 27477786268800))]
theorem block022_data_flat007_step : block022_data_flat007 = (CoefficientMerge.fastMerge block022_data_flat003 block022_data_flat006) := by decide +kernel
theorem block022_data_flat007_original : block022_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded))) := by
  rw [block022_data_flat007_step, block022_data_flat003_original, block022_data_flat006_original]
def block022_data_flat008 : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 58329956563200)), (nat_lit 5249, Int.ofNat (nat_lit 71135158752000)), (nat_lit 5269, Int.ofNat (nat_lit 16986153139200)), (nat_lit 5270, Int.ofNat (nat_lit 48554288496000)), (nat_lit 5291, Int.ofNat (nat_lit 27477786268800))]
theorem block022_data_flat008_step : block022_data_flat008 = (CoefficientMerge.fastMerge block022_data_flat002 block022_data_flat007) := by decide +kernel
theorem block022_data_flat008_original : block022_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded)))) := by
  rw [block022_data_flat008_step, block022_data_flat002_original, block022_data_flat007_original]
def block022_data_flat009 : CoefficientMerge.Poly := [(nat_lit 5556, Int.ofNat (nat_lit 142393305600))]
theorem block022_data_flat009_step : block022_data_flat009 = (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) := by decide +kernel
theorem block022_data_flat009_original : block022_data_flat009 = (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) := by
  rw [block022_data_flat009_step]
def block022_data_flat010 : CoefficientMerge.Poly := [(nat_lit 5561, Int.ofNat (nat_lit 3961249152000))]
theorem block022_data_flat010_step : block022_data_flat010 = (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded) := by decide +kernel
theorem block022_data_flat010_original : block022_data_flat010 = (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded) := by
  rw [block022_data_flat010_step]
def block022_data_flat011 : CoefficientMerge.Poly := [(nat_lit 5556, Int.ofNat (nat_lit 142393305600)), (nat_lit 5561, Int.ofNat (nat_lit 3961249152000))]
theorem block022_data_flat011_step : block022_data_flat011 = (CoefficientMerge.fastMerge block022_data_flat009 block022_data_flat010) := by decide +kernel
theorem block022_data_flat011_original : block022_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded)) := by
  rw [block022_data_flat011_step, block022_data_flat009_original, block022_data_flat010_original]
def block022_data_flat012 : CoefficientMerge.Poly := [(nat_lit 5562, Int.ofNat (nat_lit 657701004800))]
theorem block022_data_flat012_step : block022_data_flat012 = (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) := by decide +kernel
theorem block022_data_flat012_original : block022_data_flat012 = (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) := by
  rw [block022_data_flat012_step]
def block022_data_flat013 : CoefficientMerge.Poly := [(nat_lit 5578, Int.ofNat (nat_lit 731019801600))]
theorem block022_data_flat013_step : block022_data_flat013 = (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) := by decide +kernel
theorem block022_data_flat013_original : block022_data_flat013 = (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) := by
  rw [block022_data_flat013_step]
def block022_data_flat014 : CoefficientMerge.Poly := [(nat_lit 5579, Int.ofNat (nat_lit 718685798400))]
theorem block022_data_flat014_step : block022_data_flat014 = (CoefficientMerge.scale (718685798400 : Int) atom1625Coded) := by decide +kernel
theorem block022_data_flat014_original : block022_data_flat014 = (CoefficientMerge.scale (718685798400 : Int) atom1625Coded) := by
  rw [block022_data_flat014_step]
def block022_data_flat015 : CoefficientMerge.Poly := [(nat_lit 5578, Int.ofNat (nat_lit 731019801600)), (nat_lit 5579, Int.ofNat (nat_lit 718685798400))]
theorem block022_data_flat015_step : block022_data_flat015 = (CoefficientMerge.fastMerge block022_data_flat013 block022_data_flat014) := by decide +kernel
theorem block022_data_flat015_original : block022_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded)) := by
  rw [block022_data_flat015_step, block022_data_flat013_original, block022_data_flat014_original]
def block022_data_flat016 : CoefficientMerge.Poly := [(nat_lit 5562, Int.ofNat (nat_lit 657701004800)), (nat_lit 5578, Int.ofNat (nat_lit 731019801600)), (nat_lit 5579, Int.ofNat (nat_lit 718685798400))]
theorem block022_data_flat016_step : block022_data_flat016 = (CoefficientMerge.fastMerge block022_data_flat012 block022_data_flat015) := by decide +kernel
theorem block022_data_flat016_original : block022_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded))) := by
  rw [block022_data_flat016_step, block022_data_flat012_original, block022_data_flat015_original]
def block022_data_flat017 : CoefficientMerge.Poly := [(nat_lit 5556, Int.ofNat (nat_lit 142393305600)), (nat_lit 5561, Int.ofNat (nat_lit 3961249152000)), (nat_lit 5562, Int.ofNat (nat_lit 657701004800)), (nat_lit 5578, Int.ofNat (nat_lit 731019801600)), (nat_lit 5579, Int.ofNat (nat_lit 718685798400))]
theorem block022_data_flat017_step : block022_data_flat017 = (CoefficientMerge.fastMerge block022_data_flat011 block022_data_flat016) := by decide +kernel
theorem block022_data_flat017_original : block022_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded)))) := by
  rw [block022_data_flat017_step, block022_data_flat011_original, block022_data_flat016_original]
def block022_data_flat018 : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 58329956563200)), (nat_lit 5249, Int.ofNat (nat_lit 71135158752000)), (nat_lit 5269, Int.ofNat (nat_lit 16986153139200)), (nat_lit 5270, Int.ofNat (nat_lit 48554288496000)), (nat_lit 5291, Int.ofNat (nat_lit 27477786268800)), (nat_lit 5556, Int.ofNat (nat_lit 142393305600)), (nat_lit 5561, Int.ofNat (nat_lit 3961249152000)), (nat_lit 5562, Int.ofNat (nat_lit 657701004800)), (nat_lit 5578, Int.ofNat (nat_lit 731019801600)), (nat_lit 5579, Int.ofNat (nat_lit 718685798400))]
theorem block022_data_flat018_step : block022_data_flat018 = (CoefficientMerge.fastMerge block022_data_flat008 block022_data_flat017) := by decide +kernel
theorem block022_data_flat018_original : block022_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded))))) := by
  rw [block022_data_flat018_step, block022_data_flat008_original, block022_data_flat017_original]
def block022_data_flat019 : CoefficientMerge.Poly := [(nat_lit 5581, Int.ofNat (nat_lit 781859212800))]
theorem block022_data_flat019_step : block022_data_flat019 = (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) := by decide +kernel
theorem block022_data_flat019_original : block022_data_flat019 = (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) := by
  rw [block022_data_flat019_step]
def block022_data_flat020 : CoefficientMerge.Poly := [(nat_lit 5582, Int.ofNat (nat_lit 16022245108800))]
theorem block022_data_flat020_step : block022_data_flat020 = (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded) := by decide +kernel
theorem block022_data_flat020_original : block022_data_flat020 = (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded) := by
  rw [block022_data_flat020_step]
def block022_data_flat021 : CoefficientMerge.Poly := [(nat_lit 5581, Int.ofNat (nat_lit 781859212800)), (nat_lit 5582, Int.ofNat (nat_lit 16022245108800))]
theorem block022_data_flat021_step : block022_data_flat021 = (CoefficientMerge.fastMerge block022_data_flat019 block022_data_flat020) := by decide +kernel
theorem block022_data_flat021_original : block022_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded)) := by
  rw [block022_data_flat021_step, block022_data_flat019_original, block022_data_flat020_original]
def block022_data_flat022 : CoefficientMerge.Poly := [(nat_lit 5583, Int.ofNat (nat_lit 13551194686400))]
theorem block022_data_flat022_step : block022_data_flat022 = (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) := by decide +kernel
theorem block022_data_flat022_original : block022_data_flat022 = (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) := by
  rw [block022_data_flat022_step]
def block022_data_flat023 : CoefficientMerge.Poly := [(nat_lit 5584, Int.ofNat (nat_lit 11776027622400))]
theorem block022_data_flat023_step : block022_data_flat023 = (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) := by decide +kernel
theorem block022_data_flat023_original : block022_data_flat023 = (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) := by
  rw [block022_data_flat023_step]
def block022_data_flat024 : CoefficientMerge.Poly := [(nat_lit 5585, Int.ofNat (nat_lit 24502199198400))]
theorem block022_data_flat024_step : block022_data_flat024 = (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded) := by decide +kernel
theorem block022_data_flat024_original : block022_data_flat024 = (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded) := by
  rw [block022_data_flat024_step]
def block022_data_flat025 : CoefficientMerge.Poly := [(nat_lit 5584, Int.ofNat (nat_lit 11776027622400)), (nat_lit 5585, Int.ofNat (nat_lit 24502199198400))]
theorem block022_data_flat025_step : block022_data_flat025 = (CoefficientMerge.fastMerge block022_data_flat023 block022_data_flat024) := by decide +kernel
theorem block022_data_flat025_original : block022_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded)) := by
  rw [block022_data_flat025_step, block022_data_flat023_original, block022_data_flat024_original]
def block022_data_flat026 : CoefficientMerge.Poly := [(nat_lit 5583, Int.ofNat (nat_lit 13551194686400)), (nat_lit 5584, Int.ofNat (nat_lit 11776027622400)), (nat_lit 5585, Int.ofNat (nat_lit 24502199198400))]
theorem block022_data_flat026_step : block022_data_flat026 = (CoefficientMerge.fastMerge block022_data_flat022 block022_data_flat025) := by decide +kernel
theorem block022_data_flat026_original : block022_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded))) := by
  rw [block022_data_flat026_step, block022_data_flat022_original, block022_data_flat025_original]
def block022_data_flat027 : CoefficientMerge.Poly := [(nat_lit 5581, Int.ofNat (nat_lit 781859212800)), (nat_lit 5582, Int.ofNat (nat_lit 16022245108800)), (nat_lit 5583, Int.ofNat (nat_lit 13551194686400)), (nat_lit 5584, Int.ofNat (nat_lit 11776027622400)), (nat_lit 5585, Int.ofNat (nat_lit 24502199198400))]
theorem block022_data_flat027_step : block022_data_flat027 = (CoefficientMerge.fastMerge block022_data_flat021 block022_data_flat026) := by decide +kernel
theorem block022_data_flat027_original : block022_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded)))) := by
  rw [block022_data_flat027_step, block022_data_flat021_original, block022_data_flat026_original]
def block022_data_flat028 : CoefficientMerge.Poly := [(nat_lit 5600, Int.ofNat (nat_lit 3414217766400))]
theorem block022_data_flat028_step : block022_data_flat028 = (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) := by decide +kernel
theorem block022_data_flat028_original : block022_data_flat028 = (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) := by
  rw [block022_data_flat028_step]
def block022_data_flat029 : CoefficientMerge.Poly := [(nat_lit 5602, Int.ofNat (nat_lit 1274989228800))]
theorem block022_data_flat029_step : block022_data_flat029 = (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded) := by decide +kernel
theorem block022_data_flat029_original : block022_data_flat029 = (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded) := by
  rw [block022_data_flat029_step]
def block022_data_flat030 : CoefficientMerge.Poly := [(nat_lit 5600, Int.ofNat (nat_lit 3414217766400)), (nat_lit 5602, Int.ofNat (nat_lit 1274989228800))]
theorem block022_data_flat030_step : block022_data_flat030 = (CoefficientMerge.fastMerge block022_data_flat028 block022_data_flat029) := by decide +kernel
theorem block022_data_flat030_original : block022_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded)) := by
  rw [block022_data_flat030_step, block022_data_flat028_original, block022_data_flat029_original]
def block022_data_flat031 : CoefficientMerge.Poly := [(nat_lit 5603, Int.ofNat (nat_lit 25932352051200))]
theorem block022_data_flat031_step : block022_data_flat031 = (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) := by decide +kernel
theorem block022_data_flat031_original : block022_data_flat031 = (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) := by
  rw [block022_data_flat031_step]
def block022_data_flat032 : CoefficientMerge.Poly := [(nat_lit 5604, Int.ofNat (nat_lit 27709905507200))]
theorem block022_data_flat032_step : block022_data_flat032 = (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) := by decide +kernel
theorem block022_data_flat032_original : block022_data_flat032 = (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) := by
  rw [block022_data_flat032_step]
def block022_data_flat033 : CoefficientMerge.Poly := [(nat_lit 5605, Int.ofNat (nat_lit 27473854060800))]
theorem block022_data_flat033_step : block022_data_flat033 = (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded) := by decide +kernel
theorem block022_data_flat033_original : block022_data_flat033 = (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded) := by
  rw [block022_data_flat033_step]
def block022_data_flat034 : CoefficientMerge.Poly := [(nat_lit 5604, Int.ofNat (nat_lit 27709905507200)), (nat_lit 5605, Int.ofNat (nat_lit 27473854060800))]
theorem block022_data_flat034_step : block022_data_flat034 = (CoefficientMerge.fastMerge block022_data_flat032 block022_data_flat033) := by decide +kernel
theorem block022_data_flat034_original : block022_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded)) := by
  rw [block022_data_flat034_step, block022_data_flat032_original, block022_data_flat033_original]
def block022_data_flat035 : CoefficientMerge.Poly := [(nat_lit 5603, Int.ofNat (nat_lit 25932352051200)), (nat_lit 5604, Int.ofNat (nat_lit 27709905507200)), (nat_lit 5605, Int.ofNat (nat_lit 27473854060800))]
theorem block022_data_flat035_step : block022_data_flat035 = (CoefficientMerge.fastMerge block022_data_flat031 block022_data_flat034) := by decide +kernel
theorem block022_data_flat035_original : block022_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded))) := by
  rw [block022_data_flat035_step, block022_data_flat031_original, block022_data_flat034_original]
def block022_data_flat036 : CoefficientMerge.Poly := [(nat_lit 5600, Int.ofNat (nat_lit 3414217766400)), (nat_lit 5602, Int.ofNat (nat_lit 1274989228800)), (nat_lit 5603, Int.ofNat (nat_lit 25932352051200)), (nat_lit 5604, Int.ofNat (nat_lit 27709905507200)), (nat_lit 5605, Int.ofNat (nat_lit 27473854060800))]
theorem block022_data_flat036_step : block022_data_flat036 = (CoefficientMerge.fastMerge block022_data_flat030 block022_data_flat035) := by decide +kernel
theorem block022_data_flat036_original : block022_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded)))) := by
  rw [block022_data_flat036_step, block022_data_flat030_original, block022_data_flat035_original]
def block022_data_flat037 : CoefficientMerge.Poly := [(nat_lit 5581, Int.ofNat (nat_lit 781859212800)), (nat_lit 5582, Int.ofNat (nat_lit 16022245108800)), (nat_lit 5583, Int.ofNat (nat_lit 13551194686400)), (nat_lit 5584, Int.ofNat (nat_lit 11776027622400)), (nat_lit 5585, Int.ofNat (nat_lit 24502199198400)), (nat_lit 5600, Int.ofNat (nat_lit 3414217766400)), (nat_lit 5602, Int.ofNat (nat_lit 1274989228800)), (nat_lit 5603, Int.ofNat (nat_lit 25932352051200)), (nat_lit 5604, Int.ofNat (nat_lit 27709905507200)), (nat_lit 5605, Int.ofNat (nat_lit 27473854060800))]
theorem block022_data_flat037_step : block022_data_flat037 = (CoefficientMerge.fastMerge block022_data_flat027 block022_data_flat036) := by decide +kernel
theorem block022_data_flat037_original : block022_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded))))) := by
  rw [block022_data_flat037_step, block022_data_flat027_original, block022_data_flat036_original]
def block022_data_flat038 : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 58329956563200)), (nat_lit 5249, Int.ofNat (nat_lit 71135158752000)), (nat_lit 5269, Int.ofNat (nat_lit 16986153139200)), (nat_lit 5270, Int.ofNat (nat_lit 48554288496000)), (nat_lit 5291, Int.ofNat (nat_lit 27477786268800)), (nat_lit 5556, Int.ofNat (nat_lit 142393305600)), (nat_lit 5561, Int.ofNat (nat_lit 3961249152000)), (nat_lit 5562, Int.ofNat (nat_lit 657701004800)), (nat_lit 5578, Int.ofNat (nat_lit 731019801600)), (nat_lit 5579, Int.ofNat (nat_lit 718685798400)), (nat_lit 5581, Int.ofNat (nat_lit 781859212800)), (nat_lit 5582, Int.ofNat (nat_lit 16022245108800)), (nat_lit 5583, Int.ofNat (nat_lit 13551194686400)), (nat_lit 5584, Int.ofNat (nat_lit 11776027622400)), (nat_lit 5585, Int.ofNat (nat_lit 24502199198400)), (nat_lit 5600, Int.ofNat (nat_lit 3414217766400)), (nat_lit 5602, Int.ofNat (nat_lit 1274989228800)), (nat_lit 5603, Int.ofNat (nat_lit 25932352051200)), (nat_lit 5604, Int.ofNat (nat_lit 27709905507200)), (nat_lit 5605, Int.ofNat (nat_lit 27473854060800))]
theorem block022_data_flat038_step : block022_data_flat038 = (CoefficientMerge.fastMerge block022_data_flat018 block022_data_flat037) := by decide +kernel
theorem block022_data_flat038_original : block022_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded)))))) := by
  rw [block022_data_flat038_step, block022_data_flat018_original, block022_data_flat037_original]
def block022_data_flat039 : CoefficientMerge.Poly := [(nat_lit 5606, Int.ofNat (nat_lit 53106823627200))]
theorem block022_data_flat039_step : block022_data_flat039 = (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) := by decide +kernel
theorem block022_data_flat039_original : block022_data_flat039 = (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) := by
  rw [block022_data_flat039_step]
def block022_data_flat040 : CoefficientMerge.Poly := [(nat_lit 5622, Int.ofNat (nat_lit 6357299110400))]
theorem block022_data_flat040_step : block022_data_flat040 = (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded) := by decide +kernel
theorem block022_data_flat040_original : block022_data_flat040 = (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded) := by
  rw [block022_data_flat040_step]
def block022_data_flat041 : CoefficientMerge.Poly := [(nat_lit 5606, Int.ofNat (nat_lit 53106823627200)), (nat_lit 5622, Int.ofNat (nat_lit 6357299110400))]
theorem block022_data_flat041_step : block022_data_flat041 = (CoefficientMerge.fastMerge block022_data_flat039 block022_data_flat040) := by decide +kernel
theorem block022_data_flat041_original : block022_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded)) := by
  rw [block022_data_flat041_step, block022_data_flat039_original, block022_data_flat040_original]
def block022_data_flat042 : CoefficientMerge.Poly := [(nat_lit 5623, Int.ofNat (nat_lit 19520661753600))]
theorem block022_data_flat042_step : block022_data_flat042 = (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) := by decide +kernel
theorem block022_data_flat042_original : block022_data_flat042 = (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) := by
  rw [block022_data_flat042_step]
def block022_data_flat043 : CoefficientMerge.Poly := [(nat_lit 5624, Int.ofNat (nat_lit 54017265971200))]
theorem block022_data_flat043_step : block022_data_flat043 = (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) := by decide +kernel
theorem block022_data_flat043_original : block022_data_flat043 = (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) := by
  rw [block022_data_flat043_step]
def block022_data_flat044 : CoefficientMerge.Poly := [(nat_lit 5625, Int.ofNat (nat_lit 60723048870400))]
theorem block022_data_flat044_step : block022_data_flat044 = (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded) := by decide +kernel
theorem block022_data_flat044_original : block022_data_flat044 = (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded) := by
  rw [block022_data_flat044_step]
def block022_data_flat045 : CoefficientMerge.Poly := [(nat_lit 5624, Int.ofNat (nat_lit 54017265971200)), (nat_lit 5625, Int.ofNat (nat_lit 60723048870400))]
theorem block022_data_flat045_step : block022_data_flat045 = (CoefficientMerge.fastMerge block022_data_flat043 block022_data_flat044) := by decide +kernel
theorem block022_data_flat045_original : block022_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded)) := by
  rw [block022_data_flat045_step, block022_data_flat043_original, block022_data_flat044_original]
def block022_data_flat046 : CoefficientMerge.Poly := [(nat_lit 5623, Int.ofNat (nat_lit 19520661753600)), (nat_lit 5624, Int.ofNat (nat_lit 54017265971200)), (nat_lit 5625, Int.ofNat (nat_lit 60723048870400))]
theorem block022_data_flat046_step : block022_data_flat046 = (CoefficientMerge.fastMerge block022_data_flat042 block022_data_flat045) := by decide +kernel
theorem block022_data_flat046_original : block022_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded))) := by
  rw [block022_data_flat046_step, block022_data_flat042_original, block022_data_flat045_original]
def block022_data_flat047 : CoefficientMerge.Poly := [(nat_lit 5606, Int.ofNat (nat_lit 53106823627200)), (nat_lit 5622, Int.ofNat (nat_lit 6357299110400)), (nat_lit 5623, Int.ofNat (nat_lit 19520661753600)), (nat_lit 5624, Int.ofNat (nat_lit 54017265971200)), (nat_lit 5625, Int.ofNat (nat_lit 60723048870400))]
theorem block022_data_flat047_step : block022_data_flat047 = (CoefficientMerge.fastMerge block022_data_flat041 block022_data_flat046) := by decide +kernel
theorem block022_data_flat047_original : block022_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded)))) := by
  rw [block022_data_flat047_step, block022_data_flat041_original, block022_data_flat046_original]
def block022_data_flat048 : CoefficientMerge.Poly := [(nat_lit 5626, Int.ofNat (nat_lit 48904332915200))]
theorem block022_data_flat048_step : block022_data_flat048 = (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) := by decide +kernel
theorem block022_data_flat048_original : block022_data_flat048 = (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) := by
  rw [block022_data_flat048_step]
def block022_data_flat049 : CoefficientMerge.Poly := [(nat_lit 5627, Int.ofNat (nat_lit 82971805996800))]
theorem block022_data_flat049_step : block022_data_flat049 = (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded) := by decide +kernel
theorem block022_data_flat049_original : block022_data_flat049 = (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded) := by
  rw [block022_data_flat049_step]
def block022_data_flat050 : CoefficientMerge.Poly := [(nat_lit 5626, Int.ofNat (nat_lit 48904332915200)), (nat_lit 5627, Int.ofNat (nat_lit 82971805996800))]
theorem block022_data_flat050_step : block022_data_flat050 = (CoefficientMerge.fastMerge block022_data_flat048 block022_data_flat049) := by decide +kernel
theorem block022_data_flat050_original : block022_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded)) := by
  rw [block022_data_flat050_step, block022_data_flat048_original, block022_data_flat049_original]
def block022_data_flat051 : CoefficientMerge.Poly := [(nat_lit 5644, Int.ofNat (nat_lit 7890507752960))]
theorem block022_data_flat051_step : block022_data_flat051 = (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) := by decide +kernel
theorem block022_data_flat051_original : block022_data_flat051 = (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) := by
  rw [block022_data_flat051_step]
def block022_data_flat052 : CoefficientMerge.Poly := [(nat_lit 5645, Int.ofNat (nat_lit 48082095084800))]
theorem block022_data_flat052_step : block022_data_flat052 = (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) := by decide +kernel
theorem block022_data_flat052_original : block022_data_flat052 = (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) := by
  rw [block022_data_flat052_step]
def block022_data_flat053 : CoefficientMerge.Poly := [(nat_lit 5646, Int.ofNat (nat_lit 63896669200000))]
theorem block022_data_flat053_step : block022_data_flat053 = (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded) := by decide +kernel
theorem block022_data_flat053_original : block022_data_flat053 = (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded) := by
  rw [block022_data_flat053_step]
def block022_data_flat054 : CoefficientMerge.Poly := [(nat_lit 5645, Int.ofNat (nat_lit 48082095084800)), (nat_lit 5646, Int.ofNat (nat_lit 63896669200000))]
theorem block022_data_flat054_step : block022_data_flat054 = (CoefficientMerge.fastMerge block022_data_flat052 block022_data_flat053) := by decide +kernel
theorem block022_data_flat054_original : block022_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded)) := by
  rw [block022_data_flat054_step, block022_data_flat052_original, block022_data_flat053_original]
def block022_data_flat055 : CoefficientMerge.Poly := [(nat_lit 5644, Int.ofNat (nat_lit 7890507752960)), (nat_lit 5645, Int.ofNat (nat_lit 48082095084800)), (nat_lit 5646, Int.ofNat (nat_lit 63896669200000))]
theorem block022_data_flat055_step : block022_data_flat055 = (CoefficientMerge.fastMerge block022_data_flat051 block022_data_flat054) := by decide +kernel
theorem block022_data_flat055_original : block022_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded))) := by
  rw [block022_data_flat055_step, block022_data_flat051_original, block022_data_flat054_original]
def block022_data_flat056 : CoefficientMerge.Poly := [(nat_lit 5626, Int.ofNat (nat_lit 48904332915200)), (nat_lit 5627, Int.ofNat (nat_lit 82971805996800)), (nat_lit 5644, Int.ofNat (nat_lit 7890507752960)), (nat_lit 5645, Int.ofNat (nat_lit 48082095084800)), (nat_lit 5646, Int.ofNat (nat_lit 63896669200000))]
theorem block022_data_flat056_step : block022_data_flat056 = (CoefficientMerge.fastMerge block022_data_flat050 block022_data_flat055) := by decide +kernel
theorem block022_data_flat056_original : block022_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded)))) := by
  rw [block022_data_flat056_step, block022_data_flat050_original, block022_data_flat055_original]
def block022_data_flat057 : CoefficientMerge.Poly := [(nat_lit 5606, Int.ofNat (nat_lit 53106823627200)), (nat_lit 5622, Int.ofNat (nat_lit 6357299110400)), (nat_lit 5623, Int.ofNat (nat_lit 19520661753600)), (nat_lit 5624, Int.ofNat (nat_lit 54017265971200)), (nat_lit 5625, Int.ofNat (nat_lit 60723048870400)), (nat_lit 5626, Int.ofNat (nat_lit 48904332915200)), (nat_lit 5627, Int.ofNat (nat_lit 82971805996800)), (nat_lit 5644, Int.ofNat (nat_lit 7890507752960)), (nat_lit 5645, Int.ofNat (nat_lit 48082095084800)), (nat_lit 5646, Int.ofNat (nat_lit 63896669200000))]
theorem block022_data_flat057_step : block022_data_flat057 = (CoefficientMerge.fastMerge block022_data_flat047 block022_data_flat056) := by decide +kernel
theorem block022_data_flat057_original : block022_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded))))) := by
  rw [block022_data_flat057_step, block022_data_flat047_original, block022_data_flat056_original]
def block022_data_flat058 : CoefficientMerge.Poly := [(nat_lit 5647, Int.ofNat (nat_lit 55239224230400))]
theorem block022_data_flat058_step : block022_data_flat058 = (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) := by decide +kernel
theorem block022_data_flat058_original : block022_data_flat058 = (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) := by
  rw [block022_data_flat058_step]
def block022_data_flat059 : CoefficientMerge.Poly := [(nat_lit 5648, Int.ofNat (nat_lit 78568808472000))]
theorem block022_data_flat059_step : block022_data_flat059 = (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded) := by decide +kernel
theorem block022_data_flat059_original : block022_data_flat059 = (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded) := by
  rw [block022_data_flat059_step]
def block022_data_flat060 : CoefficientMerge.Poly := [(nat_lit 5647, Int.ofNat (nat_lit 55239224230400)), (nat_lit 5648, Int.ofNat (nat_lit 78568808472000))]
theorem block022_data_flat060_step : block022_data_flat060 = (CoefficientMerge.fastMerge block022_data_flat058 block022_data_flat059) := by decide +kernel
theorem block022_data_flat060_original : block022_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded)) := by
  rw [block022_data_flat060_step, block022_data_flat058_original, block022_data_flat059_original]
def block022_data_flat061 : CoefficientMerge.Poly := [(nat_lit 5666, Int.ofNat (nat_lit 39256609548800))]
theorem block022_data_flat061_step : block022_data_flat061 = (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) := by decide +kernel
theorem block022_data_flat061_original : block022_data_flat061 = (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) := by
  rw [block022_data_flat061_step]
def block022_data_flat062 : CoefficientMerge.Poly := [(nat_lit 5667, Int.ofNat (nat_lit 80549880678400))]
theorem block022_data_flat062_step : block022_data_flat062 = (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) := by decide +kernel
theorem block022_data_flat062_original : block022_data_flat062 = (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) := by
  rw [block022_data_flat062_step]
def block022_data_flat063 : CoefficientMerge.Poly := [(nat_lit 5668, Int.ofNat (nat_lit 69215540800000))]
theorem block022_data_flat063_step : block022_data_flat063 = (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded) := by decide +kernel
theorem block022_data_flat063_original : block022_data_flat063 = (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded) := by
  rw [block022_data_flat063_step]
def block022_data_flat064 : CoefficientMerge.Poly := [(nat_lit 5667, Int.ofNat (nat_lit 80549880678400)), (nat_lit 5668, Int.ofNat (nat_lit 69215540800000))]
theorem block022_data_flat064_step : block022_data_flat064 = (CoefficientMerge.fastMerge block022_data_flat062 block022_data_flat063) := by decide +kernel
theorem block022_data_flat064_original : block022_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded)) := by
  rw [block022_data_flat064_step, block022_data_flat062_original, block022_data_flat063_original]
def block022_data_flat065 : CoefficientMerge.Poly := [(nat_lit 5666, Int.ofNat (nat_lit 39256609548800)), (nat_lit 5667, Int.ofNat (nat_lit 80549880678400)), (nat_lit 5668, Int.ofNat (nat_lit 69215540800000))]
theorem block022_data_flat065_step : block022_data_flat065 = (CoefficientMerge.fastMerge block022_data_flat061 block022_data_flat064) := by decide +kernel
theorem block022_data_flat065_original : block022_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded))) := by
  rw [block022_data_flat065_step, block022_data_flat061_original, block022_data_flat064_original]
def block022_data_flat066 : CoefficientMerge.Poly := [(nat_lit 5647, Int.ofNat (nat_lit 55239224230400)), (nat_lit 5648, Int.ofNat (nat_lit 78568808472000)), (nat_lit 5666, Int.ofNat (nat_lit 39256609548800)), (nat_lit 5667, Int.ofNat (nat_lit 80549880678400)), (nat_lit 5668, Int.ofNat (nat_lit 69215540800000))]
theorem block022_data_flat066_step : block022_data_flat066 = (CoefficientMerge.fastMerge block022_data_flat060 block022_data_flat065) := by decide +kernel
theorem block022_data_flat066_original : block022_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded)))) := by
  rw [block022_data_flat066_step, block022_data_flat060_original, block022_data_flat065_original]
def block022_data_flat067 : CoefficientMerge.Poly := [(nat_lit 5669, Int.ofNat (nat_lit 88196267756800))]
theorem block022_data_flat067_step : block022_data_flat067 = (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) := by decide +kernel
theorem block022_data_flat067_original : block022_data_flat067 = (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) := by
  rw [block022_data_flat067_step]
def block022_data_flat068 : CoefficientMerge.Poly := [(nat_lit 5688, Int.ofNat (nat_lit 35739932211200))]
theorem block022_data_flat068_step : block022_data_flat068 = (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded) := by decide +kernel
theorem block022_data_flat068_original : block022_data_flat068 = (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded) := by
  rw [block022_data_flat068_step]
def block022_data_flat069 : CoefficientMerge.Poly := [(nat_lit 5669, Int.ofNat (nat_lit 88196267756800)), (nat_lit 5688, Int.ofNat (nat_lit 35739932211200))]
theorem block022_data_flat069_step : block022_data_flat069 = (CoefficientMerge.fastMerge block022_data_flat067 block022_data_flat068) := by decide +kernel
theorem block022_data_flat069_original : block022_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded)) := by
  rw [block022_data_flat069_step, block022_data_flat067_original, block022_data_flat068_original]
def block022_data_flat070 : CoefficientMerge.Poly := [(nat_lit 5689, Int.ofNat (nat_lit 67106442681600))]
theorem block022_data_flat070_step : block022_data_flat070 = (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) := by decide +kernel
theorem block022_data_flat070_original : block022_data_flat070 = (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) := by
  rw [block022_data_flat070_step]
def block022_data_flat071 : CoefficientMerge.Poly := [(nat_lit 5690, Int.ofNat (nat_lit 90606689488000))]
theorem block022_data_flat071_step : block022_data_flat071 = (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) := by decide +kernel
theorem block022_data_flat071_original : block022_data_flat071 = (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) := by
  rw [block022_data_flat071_step]
def block022_data_flat072 : CoefficientMerge.Poly := [(nat_lit 5710, Int.ofNat (nat_lit 25516823091200))]
theorem block022_data_flat072_step : block022_data_flat072 = (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded) := by decide +kernel
theorem block022_data_flat072_original : block022_data_flat072 = (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded) := by
  rw [block022_data_flat072_step]
def block022_data_flat073 : CoefficientMerge.Poly := [(nat_lit 5690, Int.ofNat (nat_lit 90606689488000)), (nat_lit 5710, Int.ofNat (nat_lit 25516823091200))]
theorem block022_data_flat073_step : block022_data_flat073 = (CoefficientMerge.fastMerge block022_data_flat071 block022_data_flat072) := by decide +kernel
theorem block022_data_flat073_original : block022_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded)) := by
  rw [block022_data_flat073_step, block022_data_flat071_original, block022_data_flat072_original]
def block022_data_flat074 : CoefficientMerge.Poly := [(nat_lit 5689, Int.ofNat (nat_lit 67106442681600)), (nat_lit 5690, Int.ofNat (nat_lit 90606689488000)), (nat_lit 5710, Int.ofNat (nat_lit 25516823091200))]
theorem block022_data_flat074_step : block022_data_flat074 = (CoefficientMerge.fastMerge block022_data_flat070 block022_data_flat073) := by decide +kernel
theorem block022_data_flat074_original : block022_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded))) := by
  rw [block022_data_flat074_step, block022_data_flat070_original, block022_data_flat073_original]
def block022_data_flat075 : CoefficientMerge.Poly := [(nat_lit 5669, Int.ofNat (nat_lit 88196267756800)), (nat_lit 5688, Int.ofNat (nat_lit 35739932211200)), (nat_lit 5689, Int.ofNat (nat_lit 67106442681600)), (nat_lit 5690, Int.ofNat (nat_lit 90606689488000)), (nat_lit 5710, Int.ofNat (nat_lit 25516823091200))]
theorem block022_data_flat075_step : block022_data_flat075 = (CoefficientMerge.fastMerge block022_data_flat069 block022_data_flat074) := by decide +kernel
theorem block022_data_flat075_original : block022_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded)))) := by
  rw [block022_data_flat075_step, block022_data_flat069_original, block022_data_flat074_original]
def block022_data_flat076 : CoefficientMerge.Poly := [(nat_lit 5647, Int.ofNat (nat_lit 55239224230400)), (nat_lit 5648, Int.ofNat (nat_lit 78568808472000)), (nat_lit 5666, Int.ofNat (nat_lit 39256609548800)), (nat_lit 5667, Int.ofNat (nat_lit 80549880678400)), (nat_lit 5668, Int.ofNat (nat_lit 69215540800000)), (nat_lit 5669, Int.ofNat (nat_lit 88196267756800)), (nat_lit 5688, Int.ofNat (nat_lit 35739932211200)), (nat_lit 5689, Int.ofNat (nat_lit 67106442681600)), (nat_lit 5690, Int.ofNat (nat_lit 90606689488000)), (nat_lit 5710, Int.ofNat (nat_lit 25516823091200))]
theorem block022_data_flat076_step : block022_data_flat076 = (CoefficientMerge.fastMerge block022_data_flat066 block022_data_flat075) := by decide +kernel
theorem block022_data_flat076_original : block022_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded))))) := by
  rw [block022_data_flat076_step, block022_data_flat066_original, block022_data_flat075_original]
def block022_data_flat077 : CoefficientMerge.Poly := [(nat_lit 5606, Int.ofNat (nat_lit 53106823627200)), (nat_lit 5622, Int.ofNat (nat_lit 6357299110400)), (nat_lit 5623, Int.ofNat (nat_lit 19520661753600)), (nat_lit 5624, Int.ofNat (nat_lit 54017265971200)), (nat_lit 5625, Int.ofNat (nat_lit 60723048870400)), (nat_lit 5626, Int.ofNat (nat_lit 48904332915200)), (nat_lit 5627, Int.ofNat (nat_lit 82971805996800)), (nat_lit 5644, Int.ofNat (nat_lit 7890507752960)), (nat_lit 5645, Int.ofNat (nat_lit 48082095084800)), (nat_lit 5646, Int.ofNat (nat_lit 63896669200000)), (nat_lit 5647, Int.ofNat (nat_lit 55239224230400)), (nat_lit 5648, Int.ofNat (nat_lit 78568808472000)), (nat_lit 5666, Int.ofNat (nat_lit 39256609548800)), (nat_lit 5667, Int.ofNat (nat_lit 80549880678400)), (nat_lit 5668, Int.ofNat (nat_lit 69215540800000)), (nat_lit 5669, Int.ofNat (nat_lit 88196267756800)), (nat_lit 5688, Int.ofNat (nat_lit 35739932211200)), (nat_lit 5689, Int.ofNat (nat_lit 67106442681600)), (nat_lit 5690, Int.ofNat (nat_lit 90606689488000)), (nat_lit 5710, Int.ofNat (nat_lit 25516823091200))]
theorem block022_data_flat077_step : block022_data_flat077 = (CoefficientMerge.fastMerge block022_data_flat057 block022_data_flat076) := by decide +kernel
theorem block022_data_flat077_original : block022_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded)))))) := by
  rw [block022_data_flat077_step, block022_data_flat057_original, block022_data_flat076_original]
def block022_data_flat078 : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 58329956563200)), (nat_lit 5249, Int.ofNat (nat_lit 71135158752000)), (nat_lit 5269, Int.ofNat (nat_lit 16986153139200)), (nat_lit 5270, Int.ofNat (nat_lit 48554288496000)), (nat_lit 5291, Int.ofNat (nat_lit 27477786268800)), (nat_lit 5556, Int.ofNat (nat_lit 142393305600)), (nat_lit 5561, Int.ofNat (nat_lit 3961249152000)), (nat_lit 5562, Int.ofNat (nat_lit 657701004800)), (nat_lit 5578, Int.ofNat (nat_lit 731019801600)), (nat_lit 5579, Int.ofNat (nat_lit 718685798400)), (nat_lit 5581, Int.ofNat (nat_lit 781859212800)), (nat_lit 5582, Int.ofNat (nat_lit 16022245108800)), (nat_lit 5583, Int.ofNat (nat_lit 13551194686400)), (nat_lit 5584, Int.ofNat (nat_lit 11776027622400)), (nat_lit 5585, Int.ofNat (nat_lit 24502199198400)), (nat_lit 5600, Int.ofNat (nat_lit 3414217766400)), (nat_lit 5602, Int.ofNat (nat_lit 1274989228800)), (nat_lit 5603, Int.ofNat (nat_lit 25932352051200)), (nat_lit 5604, Int.ofNat (nat_lit 27709905507200)), (nat_lit 5605, Int.ofNat (nat_lit 27473854060800)), (nat_lit 5606, Int.ofNat (nat_lit 53106823627200)), (nat_lit 5622, Int.ofNat (nat_lit 6357299110400)), (nat_lit 5623, Int.ofNat (nat_lit 19520661753600)), (nat_lit 5624, Int.ofNat (nat_lit 54017265971200)), (nat_lit 5625, Int.ofNat (nat_lit 60723048870400)), (nat_lit 5626, Int.ofNat (nat_lit 48904332915200)), (nat_lit 5627, Int.ofNat (nat_lit 82971805996800)), (nat_lit 5644, Int.ofNat (nat_lit 7890507752960)), (nat_lit 5645, Int.ofNat (nat_lit 48082095084800)), (nat_lit 5646, Int.ofNat (nat_lit 63896669200000)), (nat_lit 5647, Int.ofNat (nat_lit 55239224230400)), (nat_lit 5648, Int.ofNat (nat_lit 78568808472000)), (nat_lit 5666, Int.ofNat (nat_lit 39256609548800)), (nat_lit 5667, Int.ofNat (nat_lit 80549880678400)), (nat_lit 5668, Int.ofNat (nat_lit 69215540800000)), (nat_lit 5669, Int.ofNat (nat_lit 88196267756800)), (nat_lit 5688, Int.ofNat (nat_lit 35739932211200)), (nat_lit 5689, Int.ofNat (nat_lit 67106442681600)), (nat_lit 5690, Int.ofNat (nat_lit 90606689488000)), (nat_lit 5710, Int.ofNat (nat_lit 25516823091200))]
theorem block022_data_flat078_step : block022_data_flat078 = (CoefficientMerge.fastMerge block022_data_flat038 block022_data_flat077) := by decide +kernel
theorem block022_data_flat078_original : block022_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded))))))) := by
  rw [block022_data_flat078_step, block022_data_flat038_original, block022_data_flat077_original]
def block022_data_flat079 : CoefficientMerge.Poly := [(nat_lit 5711, Int.ofNat (nat_lit 77437241660800))]
theorem block022_data_flat079_step : block022_data_flat079 = (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) := by decide +kernel
theorem block022_data_flat079_original : block022_data_flat079 = (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) := by
  rw [block022_data_flat079_step]
def block022_data_flat080 : CoefficientMerge.Poly := [(nat_lit 5732, Int.ofNat (nat_lit 47533761553600))]
theorem block022_data_flat080_step : block022_data_flat080 = (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded) := by decide +kernel
theorem block022_data_flat080_original : block022_data_flat080 = (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded) := by
  rw [block022_data_flat080_step]
def block022_data_flat081 : CoefficientMerge.Poly := [(nat_lit 5711, Int.ofNat (nat_lit 77437241660800)), (nat_lit 5732, Int.ofNat (nat_lit 47533761553600))]
theorem block022_data_flat081_step : block022_data_flat081 = (CoefficientMerge.fastMerge block022_data_flat079 block022_data_flat080) := by decide +kernel
theorem block022_data_flat081_original : block022_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded)) := by
  rw [block022_data_flat081_step, block022_data_flat079_original, block022_data_flat080_original]
def block022_data_flat082 : CoefficientMerge.Poly := [(nat_lit 6019, Int.ofNat (nat_lit 390177907200))]
theorem block022_data_flat082_step : block022_data_flat082 = (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) := by decide +kernel
theorem block022_data_flat082_original : block022_data_flat082 = (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) := by
  rw [block022_data_flat082_step]
def block022_data_flat083 : CoefficientMerge.Poly := [(nat_lit 6023, Int.ofNat (nat_lit 7496187508800))]
theorem block022_data_flat083_step : block022_data_flat083 = (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) := by decide +kernel
theorem block022_data_flat083_original : block022_data_flat083 = (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) := by
  rw [block022_data_flat083_step]
def block022_data_flat084 : CoefficientMerge.Poly := [(nat_lit 6024, Int.ofNat (nat_lit 6223620657600))]
theorem block022_data_flat084_step : block022_data_flat084 = (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded) := by decide +kernel
theorem block022_data_flat084_original : block022_data_flat084 = (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded) := by
  rw [block022_data_flat084_step]
def block022_data_flat085 : CoefficientMerge.Poly := [(nat_lit 6023, Int.ofNat (nat_lit 7496187508800)), (nat_lit 6024, Int.ofNat (nat_lit 6223620657600))]
theorem block022_data_flat085_step : block022_data_flat085 = (CoefficientMerge.fastMerge block022_data_flat083 block022_data_flat084) := by decide +kernel
theorem block022_data_flat085_original : block022_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded)) := by
  rw [block022_data_flat085_step, block022_data_flat083_original, block022_data_flat084_original]
def block022_data_flat086 : CoefficientMerge.Poly := [(nat_lit 6019, Int.ofNat (nat_lit 390177907200)), (nat_lit 6023, Int.ofNat (nat_lit 7496187508800)), (nat_lit 6024, Int.ofNat (nat_lit 6223620657600))]
theorem block022_data_flat086_step : block022_data_flat086 = (CoefficientMerge.fastMerge block022_data_flat082 block022_data_flat085) := by decide +kernel
theorem block022_data_flat086_original : block022_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded))) := by
  rw [block022_data_flat086_step, block022_data_flat082_original, block022_data_flat085_original]
def block022_data_flat087 : CoefficientMerge.Poly := [(nat_lit 5711, Int.ofNat (nat_lit 77437241660800)), (nat_lit 5732, Int.ofNat (nat_lit 47533761553600)), (nat_lit 6019, Int.ofNat (nat_lit 390177907200)), (nat_lit 6023, Int.ofNat (nat_lit 7496187508800)), (nat_lit 6024, Int.ofNat (nat_lit 6223620657600))]
theorem block022_data_flat087_step : block022_data_flat087 = (CoefficientMerge.fastMerge block022_data_flat081 block022_data_flat086) := by decide +kernel
theorem block022_data_flat087_original : block022_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded)))) := by
  rw [block022_data_flat087_step, block022_data_flat081_original, block022_data_flat086_original]
def block022_data_flat088 : CoefficientMerge.Poly := [(nat_lit 6026, Int.ofNat (nat_lit 6958414296000))]
theorem block022_data_flat088_step : block022_data_flat088 = (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) := by decide +kernel
theorem block022_data_flat088_original : block022_data_flat088 = (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) := by
  rw [block022_data_flat088_step]
def block022_data_flat089 : CoefficientMerge.Poly := [(nat_lit 6041, Int.ofNat (nat_lit 1828838131200))]
theorem block022_data_flat089_step : block022_data_flat089 = (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded) := by decide +kernel
theorem block022_data_flat089_original : block022_data_flat089 = (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded) := by
  rw [block022_data_flat089_step]
def block022_data_flat090 : CoefficientMerge.Poly := [(nat_lit 6026, Int.ofNat (nat_lit 6958414296000)), (nat_lit 6041, Int.ofNat (nat_lit 1828838131200))]
theorem block022_data_flat090_step : block022_data_flat090 = (CoefficientMerge.fastMerge block022_data_flat088 block022_data_flat089) := by decide +kernel
theorem block022_data_flat090_original : block022_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded)) := by
  rw [block022_data_flat090_step, block022_data_flat088_original, block022_data_flat089_original]
def block022_data_flat091 : CoefficientMerge.Poly := [(nat_lit 6043, Int.ofNat (nat_lit 2672152588800))]
theorem block022_data_flat091_step : block022_data_flat091 = (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) := by decide +kernel
theorem block022_data_flat091_original : block022_data_flat091 = (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) := by
  rw [block022_data_flat091_step]
def block022_data_flat092 : CoefficientMerge.Poly := [(nat_lit 6044, Int.ofNat (nat_lit 28714425307200))]
theorem block022_data_flat092_step : block022_data_flat092 = (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) := by decide +kernel
theorem block022_data_flat092_original : block022_data_flat092 = (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) := by
  rw [block022_data_flat092_step]
def block022_data_flat093 : CoefficientMerge.Poly := [(nat_lit 6045, Int.ofNat (nat_lit 31318438795200))]
theorem block022_data_flat093_step : block022_data_flat093 = (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded) := by decide +kernel
theorem block022_data_flat093_original : block022_data_flat093 = (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded) := by
  rw [block022_data_flat093_step]
def block022_data_flat094 : CoefficientMerge.Poly := [(nat_lit 6044, Int.ofNat (nat_lit 28714425307200)), (nat_lit 6045, Int.ofNat (nat_lit 31318438795200))]
theorem block022_data_flat094_step : block022_data_flat094 = (CoefficientMerge.fastMerge block022_data_flat092 block022_data_flat093) := by decide +kernel
theorem block022_data_flat094_original : block022_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded)) := by
  rw [block022_data_flat094_step, block022_data_flat092_original, block022_data_flat093_original]
def block022_data_flat095 : CoefficientMerge.Poly := [(nat_lit 6043, Int.ofNat (nat_lit 2672152588800)), (nat_lit 6044, Int.ofNat (nat_lit 28714425307200)), (nat_lit 6045, Int.ofNat (nat_lit 31318438795200))]
theorem block022_data_flat095_step : block022_data_flat095 = (CoefficientMerge.fastMerge block022_data_flat091 block022_data_flat094) := by decide +kernel
theorem block022_data_flat095_original : block022_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded))) := by
  rw [block022_data_flat095_step, block022_data_flat091_original, block022_data_flat094_original]
def block022_data_flat096 : CoefficientMerge.Poly := [(nat_lit 6026, Int.ofNat (nat_lit 6958414296000)), (nat_lit 6041, Int.ofNat (nat_lit 1828838131200)), (nat_lit 6043, Int.ofNat (nat_lit 2672152588800)), (nat_lit 6044, Int.ofNat (nat_lit 28714425307200)), (nat_lit 6045, Int.ofNat (nat_lit 31318438795200))]
theorem block022_data_flat096_step : block022_data_flat096 = (CoefficientMerge.fastMerge block022_data_flat090 block022_data_flat095) := by decide +kernel
theorem block022_data_flat096_original : block022_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded)))) := by
  rw [block022_data_flat096_step, block022_data_flat090_original, block022_data_flat095_original]
def block022_data_flat097 : CoefficientMerge.Poly := [(nat_lit 5711, Int.ofNat (nat_lit 77437241660800)), (nat_lit 5732, Int.ofNat (nat_lit 47533761553600)), (nat_lit 6019, Int.ofNat (nat_lit 390177907200)), (nat_lit 6023, Int.ofNat (nat_lit 7496187508800)), (nat_lit 6024, Int.ofNat (nat_lit 6223620657600)), (nat_lit 6026, Int.ofNat (nat_lit 6958414296000)), (nat_lit 6041, Int.ofNat (nat_lit 1828838131200)), (nat_lit 6043, Int.ofNat (nat_lit 2672152588800)), (nat_lit 6044, Int.ofNat (nat_lit 28714425307200)), (nat_lit 6045, Int.ofNat (nat_lit 31318438795200))]
theorem block022_data_flat097_step : block022_data_flat097 = (CoefficientMerge.fastMerge block022_data_flat087 block022_data_flat096) := by decide +kernel
theorem block022_data_flat097_original : block022_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded))))) := by
  rw [block022_data_flat097_step, block022_data_flat087_original, block022_data_flat096_original]
def block022_data_flat098 : CoefficientMerge.Poly := [(nat_lit 6046, Int.ofNat (nat_lit 20764754611200))]
theorem block022_data_flat098_step : block022_data_flat098 = (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) := by decide +kernel
theorem block022_data_flat098_original : block022_data_flat098 = (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) := by
  rw [block022_data_flat098_step]
def block022_data_flat099 : CoefficientMerge.Poly := [(nat_lit 6047, Int.ofNat (nat_lit 47303583076800))]
theorem block022_data_flat099_step : block022_data_flat099 = (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded) := by decide +kernel
theorem block022_data_flat099_original : block022_data_flat099 = (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded) := by
  rw [block022_data_flat099_step]
def block022_data_flat100 : CoefficientMerge.Poly := [(nat_lit 6046, Int.ofNat (nat_lit 20764754611200)), (nat_lit 6047, Int.ofNat (nat_lit 47303583076800))]
theorem block022_data_flat100_step : block022_data_flat100 = (CoefficientMerge.fastMerge block022_data_flat098 block022_data_flat099) := by decide +kernel
theorem block022_data_flat100_original : block022_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded)) := by
  rw [block022_data_flat100_step, block022_data_flat098_original, block022_data_flat099_original]
def block022_data_flat101 : CoefficientMerge.Poly := [(nat_lit 6063, Int.ofNat (nat_lit 3550208205600))]
theorem block022_data_flat101_step : block022_data_flat101 = (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) := by decide +kernel
theorem block022_data_flat101_original : block022_data_flat101 = (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) := by
  rw [block022_data_flat101_step]
def block022_data_flat102 : CoefficientMerge.Poly := [(nat_lit 6064, Int.ofNat (nat_lit 14159602504800))]
theorem block022_data_flat102_step : block022_data_flat102 = (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) := by decide +kernel
theorem block022_data_flat102_original : block022_data_flat102 = (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) := by
  rw [block022_data_flat102_step]
def block022_data_flat103 : CoefficientMerge.Poly := [(nat_lit 6065, Int.ofNat (nat_lit 50540795877600))]
theorem block022_data_flat103_step : block022_data_flat103 = (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded) := by decide +kernel
theorem block022_data_flat103_original : block022_data_flat103 = (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded) := by
  rw [block022_data_flat103_step]
def block022_data_flat104 : CoefficientMerge.Poly := [(nat_lit 6064, Int.ofNat (nat_lit 14159602504800)), (nat_lit 6065, Int.ofNat (nat_lit 50540795877600))]
theorem block022_data_flat104_step : block022_data_flat104 = (CoefficientMerge.fastMerge block022_data_flat102 block022_data_flat103) := by decide +kernel
theorem block022_data_flat104_original : block022_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded)) := by
  rw [block022_data_flat104_step, block022_data_flat102_original, block022_data_flat103_original]
def block022_data_flat105 : CoefficientMerge.Poly := [(nat_lit 6063, Int.ofNat (nat_lit 3550208205600)), (nat_lit 6064, Int.ofNat (nat_lit 14159602504800)), (nat_lit 6065, Int.ofNat (nat_lit 50540795877600))]
theorem block022_data_flat105_step : block022_data_flat105 = (CoefficientMerge.fastMerge block022_data_flat101 block022_data_flat104) := by decide +kernel
theorem block022_data_flat105_original : block022_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded))) := by
  rw [block022_data_flat105_step, block022_data_flat101_original, block022_data_flat104_original]
def block022_data_flat106 : CoefficientMerge.Poly := [(nat_lit 6046, Int.ofNat (nat_lit 20764754611200)), (nat_lit 6047, Int.ofNat (nat_lit 47303583076800)), (nat_lit 6063, Int.ofNat (nat_lit 3550208205600)), (nat_lit 6064, Int.ofNat (nat_lit 14159602504800)), (nat_lit 6065, Int.ofNat (nat_lit 50540795877600))]
theorem block022_data_flat106_step : block022_data_flat106 = (CoefficientMerge.fastMerge block022_data_flat100 block022_data_flat105) := by decide +kernel
theorem block022_data_flat106_original : block022_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded)))) := by
  rw [block022_data_flat106_step, block022_data_flat100_original, block022_data_flat105_original]
def block022_data_flat107 : CoefficientMerge.Poly := [(nat_lit 6066, Int.ofNat (nat_lit 58714949336400))]
theorem block022_data_flat107_step : block022_data_flat107 = (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) := by decide +kernel
theorem block022_data_flat107_original : block022_data_flat107 = (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) := by
  rw [block022_data_flat107_step]
def block022_data_flat108 : CoefficientMerge.Poly := [(nat_lit 6067, Int.ofNat (nat_lit 44621368840800))]
theorem block022_data_flat108_step : block022_data_flat108 = (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded) := by decide +kernel
theorem block022_data_flat108_original : block022_data_flat108 = (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded) := by
  rw [block022_data_flat108_step]
def block022_data_flat109 : CoefficientMerge.Poly := [(nat_lit 6066, Int.ofNat (nat_lit 58714949336400)), (nat_lit 6067, Int.ofNat (nat_lit 44621368840800))]
theorem block022_data_flat109_step : block022_data_flat109 = (CoefficientMerge.fastMerge block022_data_flat107 block022_data_flat108) := by decide +kernel
theorem block022_data_flat109_original : block022_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded)) := by
  rw [block022_data_flat109_step, block022_data_flat107_original, block022_data_flat108_original]
def block022_data_flat110 : CoefficientMerge.Poly := [(nat_lit 6068, Int.ofNat (nat_lit 82584805073400))]
theorem block022_data_flat110_step : block022_data_flat110 = (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) := by decide +kernel
theorem block022_data_flat110_original : block022_data_flat110 = (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) := by
  rw [block022_data_flat110_step]
def block022_data_flat111 : CoefficientMerge.Poly := [(nat_lit 6085, Int.ofNat (nat_lit 5924850140160))]
theorem block022_data_flat111_step : block022_data_flat111 = (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) := by decide +kernel
theorem block022_data_flat111_original : block022_data_flat111 = (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) := by
  rw [block022_data_flat111_step]
def block022_data_flat112 : CoefficientMerge.Poly := [(nat_lit 6086, Int.ofNat (nat_lit 46603049565600))]
theorem block022_data_flat112_step : block022_data_flat112 = (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded) := by decide +kernel
theorem block022_data_flat112_original : block022_data_flat112 = (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded) := by
  rw [block022_data_flat112_step]
def block022_data_flat113 : CoefficientMerge.Poly := [(nat_lit 6085, Int.ofNat (nat_lit 5924850140160)), (nat_lit 6086, Int.ofNat (nat_lit 46603049565600))]
theorem block022_data_flat113_step : block022_data_flat113 = (CoefficientMerge.fastMerge block022_data_flat111 block022_data_flat112) := by decide +kernel
theorem block022_data_flat113_original : block022_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded)) := by
  rw [block022_data_flat113_step, block022_data_flat111_original, block022_data_flat112_original]
def block022_data_flat114 : CoefficientMerge.Poly := [(nat_lit 6068, Int.ofNat (nat_lit 82584805073400)), (nat_lit 6085, Int.ofNat (nat_lit 5924850140160)), (nat_lit 6086, Int.ofNat (nat_lit 46603049565600))]
theorem block022_data_flat114_step : block022_data_flat114 = (CoefficientMerge.fastMerge block022_data_flat110 block022_data_flat113) := by decide +kernel
theorem block022_data_flat114_original : block022_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded))) := by
  rw [block022_data_flat114_step, block022_data_flat110_original, block022_data_flat113_original]
def block022_data_flat115 : CoefficientMerge.Poly := [(nat_lit 6066, Int.ofNat (nat_lit 58714949336400)), (nat_lit 6067, Int.ofNat (nat_lit 44621368840800)), (nat_lit 6068, Int.ofNat (nat_lit 82584805073400)), (nat_lit 6085, Int.ofNat (nat_lit 5924850140160)), (nat_lit 6086, Int.ofNat (nat_lit 46603049565600))]
theorem block022_data_flat115_step : block022_data_flat115 = (CoefficientMerge.fastMerge block022_data_flat109 block022_data_flat114) := by decide +kernel
theorem block022_data_flat115_original : block022_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded)))) := by
  rw [block022_data_flat115_step, block022_data_flat109_original, block022_data_flat114_original]
def block022_data_flat116 : CoefficientMerge.Poly := [(nat_lit 6046, Int.ofNat (nat_lit 20764754611200)), (nat_lit 6047, Int.ofNat (nat_lit 47303583076800)), (nat_lit 6063, Int.ofNat (nat_lit 3550208205600)), (nat_lit 6064, Int.ofNat (nat_lit 14159602504800)), (nat_lit 6065, Int.ofNat (nat_lit 50540795877600)), (nat_lit 6066, Int.ofNat (nat_lit 58714949336400)), (nat_lit 6067, Int.ofNat (nat_lit 44621368840800)), (nat_lit 6068, Int.ofNat (nat_lit 82584805073400)), (nat_lit 6085, Int.ofNat (nat_lit 5924850140160)), (nat_lit 6086, Int.ofNat (nat_lit 46603049565600))]
theorem block022_data_flat116_step : block022_data_flat116 = (CoefficientMerge.fastMerge block022_data_flat106 block022_data_flat115) := by decide +kernel
theorem block022_data_flat116_original : block022_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded))))) := by
  rw [block022_data_flat116_step, block022_data_flat106_original, block022_data_flat115_original]
def block022_data_flat117 : CoefficientMerge.Poly := [(nat_lit 5711, Int.ofNat (nat_lit 77437241660800)), (nat_lit 5732, Int.ofNat (nat_lit 47533761553600)), (nat_lit 6019, Int.ofNat (nat_lit 390177907200)), (nat_lit 6023, Int.ofNat (nat_lit 7496187508800)), (nat_lit 6024, Int.ofNat (nat_lit 6223620657600)), (nat_lit 6026, Int.ofNat (nat_lit 6958414296000)), (nat_lit 6041, Int.ofNat (nat_lit 1828838131200)), (nat_lit 6043, Int.ofNat (nat_lit 2672152588800)), (nat_lit 6044, Int.ofNat (nat_lit 28714425307200)), (nat_lit 6045, Int.ofNat (nat_lit 31318438795200)), (nat_lit 6046, Int.ofNat (nat_lit 20764754611200)), (nat_lit 6047, Int.ofNat (nat_lit 47303583076800)), (nat_lit 6063, Int.ofNat (nat_lit 3550208205600)), (nat_lit 6064, Int.ofNat (nat_lit 14159602504800)), (nat_lit 6065, Int.ofNat (nat_lit 50540795877600)), (nat_lit 6066, Int.ofNat (nat_lit 58714949336400)), (nat_lit 6067, Int.ofNat (nat_lit 44621368840800)), (nat_lit 6068, Int.ofNat (nat_lit 82584805073400)), (nat_lit 6085, Int.ofNat (nat_lit 5924850140160)), (nat_lit 6086, Int.ofNat (nat_lit 46603049565600))]
theorem block022_data_flat117_step : block022_data_flat117 = (CoefficientMerge.fastMerge block022_data_flat097 block022_data_flat116) := by decide +kernel
theorem block022_data_flat117_original : block022_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded)))))) := by
  rw [block022_data_flat117_step, block022_data_flat097_original, block022_data_flat116_original]
def block022_data_flat118 : CoefficientMerge.Poly := [(nat_lit 6087, Int.ofNat (nat_lit 64561905414000))]
theorem block022_data_flat118_step : block022_data_flat118 = (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) := by decide +kernel
theorem block022_data_flat118_original : block022_data_flat118 = (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) := by
  rw [block022_data_flat118_step]
def block022_data_flat119 : CoefficientMerge.Poly := [(nat_lit 6088, Int.ofNat (nat_lit 58431178094400))]
theorem block022_data_flat119_step : block022_data_flat119 = (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded) := by decide +kernel
theorem block022_data_flat119_original : block022_data_flat119 = (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded) := by
  rw [block022_data_flat119_step]
def block022_data_flat120 : CoefficientMerge.Poly := [(nat_lit 6087, Int.ofNat (nat_lit 64561905414000)), (nat_lit 6088, Int.ofNat (nat_lit 58431178094400))]
theorem block022_data_flat120_step : block022_data_flat120 = (CoefficientMerge.fastMerge block022_data_flat118 block022_data_flat119) := by decide +kernel
theorem block022_data_flat120_original : block022_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded)) := by
  rw [block022_data_flat120_step, block022_data_flat118_original, block022_data_flat119_original]
def block022_data_flat121 : CoefficientMerge.Poly := [(nat_lit 6089, Int.ofNat (nat_lit 83751050082600))]
theorem block022_data_flat121_step : block022_data_flat121 = (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) := by decide +kernel
theorem block022_data_flat121_original : block022_data_flat121 = (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) := by
  rw [block022_data_flat121_step]
def block022_data_flat122 : CoefficientMerge.Poly := [(nat_lit 6107, Int.ofNat (nat_lit 38700065779200))]
theorem block022_data_flat122_step : block022_data_flat122 = (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) := by decide +kernel
theorem block022_data_flat122_original : block022_data_flat122 = (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) := by
  rw [block022_data_flat122_step]
def block022_data_flat123 : CoefficientMerge.Poly := [(nat_lit 6108, Int.ofNat (nat_lit 81441252748800))]
theorem block022_data_flat123_step : block022_data_flat123 = (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded) := by decide +kernel
theorem block022_data_flat123_original : block022_data_flat123 = (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded) := by
  rw [block022_data_flat123_step]
def block022_data_flat124 : CoefficientMerge.Poly := [(nat_lit 6107, Int.ofNat (nat_lit 38700065779200)), (nat_lit 6108, Int.ofNat (nat_lit 81441252748800))]
theorem block022_data_flat124_step : block022_data_flat124 = (CoefficientMerge.fastMerge block022_data_flat122 block022_data_flat123) := by decide +kernel
theorem block022_data_flat124_original : block022_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded)) := by
  rw [block022_data_flat124_step, block022_data_flat122_original, block022_data_flat123_original]
def block022_data_flat125 : CoefficientMerge.Poly := [(nat_lit 6089, Int.ofNat (nat_lit 83751050082600)), (nat_lit 6107, Int.ofNat (nat_lit 38700065779200)), (nat_lit 6108, Int.ofNat (nat_lit 81441252748800))]
theorem block022_data_flat125_step : block022_data_flat125 = (CoefficientMerge.fastMerge block022_data_flat121 block022_data_flat124) := by decide +kernel
theorem block022_data_flat125_original : block022_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded))) := by
  rw [block022_data_flat125_step, block022_data_flat121_original, block022_data_flat124_original]
def block022_data_flat126 : CoefficientMerge.Poly := [(nat_lit 6087, Int.ofNat (nat_lit 64561905414000)), (nat_lit 6088, Int.ofNat (nat_lit 58431178094400)), (nat_lit 6089, Int.ofNat (nat_lit 83751050082600)), (nat_lit 6107, Int.ofNat (nat_lit 38700065779200)), (nat_lit 6108, Int.ofNat (nat_lit 81441252748800))]
theorem block022_data_flat126_step : block022_data_flat126 = (CoefficientMerge.fastMerge block022_data_flat120 block022_data_flat125) := by decide +kernel
theorem block022_data_flat126_original : block022_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded)))) := by
  rw [block022_data_flat126_step, block022_data_flat120_original, block022_data_flat125_original]
def block022_data_flat127 : CoefficientMerge.Poly := [(nat_lit 6109, Int.ofNat (nat_lit 76619479413600))]
theorem block022_data_flat127_step : block022_data_flat127 = (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) := by decide +kernel
theorem block022_data_flat127_original : block022_data_flat127 = (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) := by
  rw [block022_data_flat127_step]
def block022_data_flat128 : CoefficientMerge.Poly := [(nat_lit 6110, Int.ofNat (nat_lit 96041823897600))]
theorem block022_data_flat128_step : block022_data_flat128 = (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded) := by decide +kernel
theorem block022_data_flat128_original : block022_data_flat128 = (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded) := by
  rw [block022_data_flat128_step]
def block022_data_flat129 : CoefficientMerge.Poly := [(nat_lit 6109, Int.ofNat (nat_lit 76619479413600)), (nat_lit 6110, Int.ofNat (nat_lit 96041823897600))]
theorem block022_data_flat129_step : block022_data_flat129 = (CoefficientMerge.fastMerge block022_data_flat127 block022_data_flat128) := by decide +kernel
theorem block022_data_flat129_original : block022_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded)) := by
  rw [block022_data_flat129_step, block022_data_flat127_original, block022_data_flat128_original]
def block022_data_flat130 : CoefficientMerge.Poly := [(nat_lit 6129, Int.ofNat (nat_lit 36760668134400))]
theorem block022_data_flat130_step : block022_data_flat130 = (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) := by decide +kernel
theorem block022_data_flat130_original : block022_data_flat130 = (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) := by
  rw [block022_data_flat130_step]
def block022_data_flat131 : CoefficientMerge.Poly := [(nat_lit 6130, Int.ofNat (nat_lit 77891482429200))]
theorem block022_data_flat131_step : block022_data_flat131 = (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) := by decide +kernel
theorem block022_data_flat131_original : block022_data_flat131 = (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) := by
  rw [block022_data_flat131_step]
def block022_data_flat132 : CoefficientMerge.Poly := [(nat_lit 6131, Int.ofNat (nat_lit 100837655654400))]
theorem block022_data_flat132_step : block022_data_flat132 = (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded) := by decide +kernel
theorem block022_data_flat132_original : block022_data_flat132 = (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded) := by
  rw [block022_data_flat132_step]
def block022_data_flat133 : CoefficientMerge.Poly := [(nat_lit 6130, Int.ofNat (nat_lit 77891482429200)), (nat_lit 6131, Int.ofNat (nat_lit 100837655654400))]
theorem block022_data_flat133_step : block022_data_flat133 = (CoefficientMerge.fastMerge block022_data_flat131 block022_data_flat132) := by decide +kernel
theorem block022_data_flat133_original : block022_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded)) := by
  rw [block022_data_flat133_step, block022_data_flat131_original, block022_data_flat132_original]
def block022_data_flat134 : CoefficientMerge.Poly := [(nat_lit 6129, Int.ofNat (nat_lit 36760668134400)), (nat_lit 6130, Int.ofNat (nat_lit 77891482429200)), (nat_lit 6131, Int.ofNat (nat_lit 100837655654400))]
theorem block022_data_flat134_step : block022_data_flat134 = (CoefficientMerge.fastMerge block022_data_flat130 block022_data_flat133) := by decide +kernel
theorem block022_data_flat134_original : block022_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded))) := by
  rw [block022_data_flat134_step, block022_data_flat130_original, block022_data_flat133_original]
def block022_data_flat135 : CoefficientMerge.Poly := [(nat_lit 6109, Int.ofNat (nat_lit 76619479413600)), (nat_lit 6110, Int.ofNat (nat_lit 96041823897600)), (nat_lit 6129, Int.ofNat (nat_lit 36760668134400)), (nat_lit 6130, Int.ofNat (nat_lit 77891482429200)), (nat_lit 6131, Int.ofNat (nat_lit 100837655654400))]
theorem block022_data_flat135_step : block022_data_flat135 = (CoefficientMerge.fastMerge block022_data_flat129 block022_data_flat134) := by decide +kernel
theorem block022_data_flat135_original : block022_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded)))) := by
  rw [block022_data_flat135_step, block022_data_flat129_original, block022_data_flat134_original]
def block022_data_flat136 : CoefficientMerge.Poly := [(nat_lit 6087, Int.ofNat (nat_lit 64561905414000)), (nat_lit 6088, Int.ofNat (nat_lit 58431178094400)), (nat_lit 6089, Int.ofNat (nat_lit 83751050082600)), (nat_lit 6107, Int.ofNat (nat_lit 38700065779200)), (nat_lit 6108, Int.ofNat (nat_lit 81441252748800)), (nat_lit 6109, Int.ofNat (nat_lit 76619479413600)), (nat_lit 6110, Int.ofNat (nat_lit 96041823897600)), (nat_lit 6129, Int.ofNat (nat_lit 36760668134400)), (nat_lit 6130, Int.ofNat (nat_lit 77891482429200)), (nat_lit 6131, Int.ofNat (nat_lit 100837655654400))]
theorem block022_data_flat136_step : block022_data_flat136 = (CoefficientMerge.fastMerge block022_data_flat126 block022_data_flat135) := by decide +kernel
theorem block022_data_flat136_original : block022_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded))))) := by
  rw [block022_data_flat136_step, block022_data_flat126_original, block022_data_flat135_original]
def block022_data_flat137 : CoefficientMerge.Poly := [(nat_lit 6151, Int.ofNat (nat_lit 36725564548800))]
theorem block022_data_flat137_step : block022_data_flat137 = (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) := by decide +kernel
theorem block022_data_flat137_original : block022_data_flat137 = (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) := by
  rw [block022_data_flat137_step]
def block022_data_flat138 : CoefficientMerge.Poly := [(nat_lit 6152, Int.ofNat (nat_lit 99336377640600))]
theorem block022_data_flat138_step : block022_data_flat138 = (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded) := by decide +kernel
theorem block022_data_flat138_original : block022_data_flat138 = (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded) := by
  rw [block022_data_flat138_step]
def block022_data_flat139 : CoefficientMerge.Poly := [(nat_lit 6151, Int.ofNat (nat_lit 36725564548800)), (nat_lit 6152, Int.ofNat (nat_lit 99336377640600))]
theorem block022_data_flat139_step : block022_data_flat139 = (CoefficientMerge.fastMerge block022_data_flat137 block022_data_flat138) := by decide +kernel
theorem block022_data_flat139_original : block022_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded)) := by
  rw [block022_data_flat139_step, block022_data_flat137_original, block022_data_flat138_original]
def block022_data_flat140 : CoefficientMerge.Poly := [(nat_lit 6173, Int.ofNat (nat_lit 57215047680000))]
theorem block022_data_flat140_step : block022_data_flat140 = (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) := by decide +kernel
theorem block022_data_flat140_original : block022_data_flat140 = (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) := by
  rw [block022_data_flat140_step]
def block022_data_flat141 : CoefficientMerge.Poly := [(nat_lit 6482, Int.ofNat (nat_lit 1735780838400))]
theorem block022_data_flat141_step : block022_data_flat141 = (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) := by decide +kernel
theorem block022_data_flat141_original : block022_data_flat141 = (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) := by
  rw [block022_data_flat141_step]
def block022_data_flat142 : CoefficientMerge.Poly := [(nat_lit 6485, Int.ofNat (nat_lit 13628959948800))]
theorem block022_data_flat142_step : block022_data_flat142 = (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded) := by decide +kernel
theorem block022_data_flat142_original : block022_data_flat142 = (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded) := by
  rw [block022_data_flat142_step]
def block022_data_flat143 : CoefficientMerge.Poly := [(nat_lit 6482, Int.ofNat (nat_lit 1735780838400)), (nat_lit 6485, Int.ofNat (nat_lit 13628959948800))]
theorem block022_data_flat143_step : block022_data_flat143 = (CoefficientMerge.fastMerge block022_data_flat141 block022_data_flat142) := by decide +kernel
theorem block022_data_flat143_original : block022_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded)) := by
  rw [block022_data_flat143_step, block022_data_flat141_original, block022_data_flat142_original]
def block022_data_flat144 : CoefficientMerge.Poly := [(nat_lit 6173, Int.ofNat (nat_lit 57215047680000)), (nat_lit 6482, Int.ofNat (nat_lit 1735780838400)), (nat_lit 6485, Int.ofNat (nat_lit 13628959948800))]
theorem block022_data_flat144_step : block022_data_flat144 = (CoefficientMerge.fastMerge block022_data_flat140 block022_data_flat143) := by decide +kernel
theorem block022_data_flat144_original : block022_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded))) := by
  rw [block022_data_flat144_step, block022_data_flat140_original, block022_data_flat143_original]
def block022_data_flat145 : CoefficientMerge.Poly := [(nat_lit 6151, Int.ofNat (nat_lit 36725564548800)), (nat_lit 6152, Int.ofNat (nat_lit 99336377640600)), (nat_lit 6173, Int.ofNat (nat_lit 57215047680000)), (nat_lit 6482, Int.ofNat (nat_lit 1735780838400)), (nat_lit 6485, Int.ofNat (nat_lit 13628959948800))]
theorem block022_data_flat145_step : block022_data_flat145 = (CoefficientMerge.fastMerge block022_data_flat139 block022_data_flat144) := by decide +kernel
theorem block022_data_flat145_original : block022_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded)))) := by
  rw [block022_data_flat145_step, block022_data_flat139_original, block022_data_flat144_original]
def block022_data_flat146 : CoefficientMerge.Poly := [(nat_lit 6486, Int.ofNat (nat_lit 14833387699200))]
theorem block022_data_flat146_step : block022_data_flat146 = (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) := by decide +kernel
theorem block022_data_flat146_original : block022_data_flat146 = (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) := by
  rw [block022_data_flat146_step]
def block022_data_flat147 : CoefficientMerge.Poly := [(nat_lit 6487, Int.ofNat (nat_lit 5586198912000))]
theorem block022_data_flat147_step : block022_data_flat147 = (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded) := by decide +kernel
theorem block022_data_flat147_original : block022_data_flat147 = (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded) := by
  rw [block022_data_flat147_step]
def block022_data_flat148 : CoefficientMerge.Poly := [(nat_lit 6486, Int.ofNat (nat_lit 14833387699200)), (nat_lit 6487, Int.ofNat (nat_lit 5586198912000))]
theorem block022_data_flat148_step : block022_data_flat148 = (CoefficientMerge.fastMerge block022_data_flat146 block022_data_flat147) := by decide +kernel
theorem block022_data_flat148_original : block022_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded)) := by
  rw [block022_data_flat148_step, block022_data_flat146_original, block022_data_flat147_original]
def block022_data_flat149 : CoefficientMerge.Poly := [(nat_lit 6488, Int.ofNat (nat_lit 20249487820800))]
theorem block022_data_flat149_step : block022_data_flat149 = (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) := by decide +kernel
theorem block022_data_flat149_original : block022_data_flat149 = (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) := by
  rw [block022_data_flat149_step]
def block022_data_flat150 : CoefficientMerge.Poly := [(nat_lit 6504, Int.ofNat (nat_lit 906549235200))]
theorem block022_data_flat150_step : block022_data_flat150 = (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) := by decide +kernel
theorem block022_data_flat150_original : block022_data_flat150 = (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) := by
  rw [block022_data_flat150_step]
def block022_data_flat151 : CoefficientMerge.Poly := [(nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
theorem block022_data_flat151_step : block022_data_flat151 = (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded) := by decide +kernel
theorem block022_data_flat151_original : block022_data_flat151 = (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded) := by
  rw [block022_data_flat151_step]
def block022_data_flat152 : CoefficientMerge.Poly := [(nat_lit 6504, Int.ofNat (nat_lit 906549235200)), (nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
theorem block022_data_flat152_step : block022_data_flat152 = (CoefficientMerge.fastMerge block022_data_flat150 block022_data_flat151) := by decide +kernel
theorem block022_data_flat152_original : block022_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded)) := by
  rw [block022_data_flat152_step, block022_data_flat150_original, block022_data_flat151_original]
def block022_data_flat153 : CoefficientMerge.Poly := [(nat_lit 6488, Int.ofNat (nat_lit 20249487820800)), (nat_lit 6504, Int.ofNat (nat_lit 906549235200)), (nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
theorem block022_data_flat153_step : block022_data_flat153 = (CoefficientMerge.fastMerge block022_data_flat149 block022_data_flat152) := by decide +kernel
theorem block022_data_flat153_original : block022_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded))) := by
  rw [block022_data_flat153_step, block022_data_flat149_original, block022_data_flat152_original]
def block022_data_flat154 : CoefficientMerge.Poly := [(nat_lit 6486, Int.ofNat (nat_lit 14833387699200)), (nat_lit 6487, Int.ofNat (nat_lit 5586198912000)), (nat_lit 6488, Int.ofNat (nat_lit 20249487820800)), (nat_lit 6504, Int.ofNat (nat_lit 906549235200)), (nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
theorem block022_data_flat154_step : block022_data_flat154 = (CoefficientMerge.fastMerge block022_data_flat148 block022_data_flat153) := by decide +kernel
theorem block022_data_flat154_original : block022_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded)))) := by
  rw [block022_data_flat154_step, block022_data_flat148_original, block022_data_flat153_original]
def block022_data_flat155 : CoefficientMerge.Poly := [(nat_lit 6151, Int.ofNat (nat_lit 36725564548800)), (nat_lit 6152, Int.ofNat (nat_lit 99336377640600)), (nat_lit 6173, Int.ofNat (nat_lit 57215047680000)), (nat_lit 6482, Int.ofNat (nat_lit 1735780838400)), (nat_lit 6485, Int.ofNat (nat_lit 13628959948800)), (nat_lit 6486, Int.ofNat (nat_lit 14833387699200)), (nat_lit 6487, Int.ofNat (nat_lit 5586198912000)), (nat_lit 6488, Int.ofNat (nat_lit 20249487820800)), (nat_lit 6504, Int.ofNat (nat_lit 906549235200)), (nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
theorem block022_data_flat155_step : block022_data_flat155 = (CoefficientMerge.fastMerge block022_data_flat145 block022_data_flat154) := by decide +kernel
theorem block022_data_flat155_original : block022_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded))))) := by
  rw [block022_data_flat155_step, block022_data_flat145_original, block022_data_flat154_original]
def block022_data_flat156 : CoefficientMerge.Poly := [(nat_lit 6087, Int.ofNat (nat_lit 64561905414000)), (nat_lit 6088, Int.ofNat (nat_lit 58431178094400)), (nat_lit 6089, Int.ofNat (nat_lit 83751050082600)), (nat_lit 6107, Int.ofNat (nat_lit 38700065779200)), (nat_lit 6108, Int.ofNat (nat_lit 81441252748800)), (nat_lit 6109, Int.ofNat (nat_lit 76619479413600)), (nat_lit 6110, Int.ofNat (nat_lit 96041823897600)), (nat_lit 6129, Int.ofNat (nat_lit 36760668134400)), (nat_lit 6130, Int.ofNat (nat_lit 77891482429200)), (nat_lit 6131, Int.ofNat (nat_lit 100837655654400)), (nat_lit 6151, Int.ofNat (nat_lit 36725564548800)), (nat_lit 6152, Int.ofNat (nat_lit 99336377640600)), (nat_lit 6173, Int.ofNat (nat_lit 57215047680000)), (nat_lit 6482, Int.ofNat (nat_lit 1735780838400)), (nat_lit 6485, Int.ofNat (nat_lit 13628959948800)), (nat_lit 6486, Int.ofNat (nat_lit 14833387699200)), (nat_lit 6487, Int.ofNat (nat_lit 5586198912000)), (nat_lit 6488, Int.ofNat (nat_lit 20249487820800)), (nat_lit 6504, Int.ofNat (nat_lit 906549235200)), (nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
theorem block022_data_flat156_step : block022_data_flat156 = (CoefficientMerge.fastMerge block022_data_flat136 block022_data_flat155) := by decide +kernel
theorem block022_data_flat156_original : block022_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded)))))) := by
  rw [block022_data_flat156_step, block022_data_flat136_original, block022_data_flat155_original]
def block022_data_flat157 : CoefficientMerge.Poly := [(nat_lit 5711, Int.ofNat (nat_lit 77437241660800)), (nat_lit 5732, Int.ofNat (nat_lit 47533761553600)), (nat_lit 6019, Int.ofNat (nat_lit 390177907200)), (nat_lit 6023, Int.ofNat (nat_lit 7496187508800)), (nat_lit 6024, Int.ofNat (nat_lit 6223620657600)), (nat_lit 6026, Int.ofNat (nat_lit 6958414296000)), (nat_lit 6041, Int.ofNat (nat_lit 1828838131200)), (nat_lit 6043, Int.ofNat (nat_lit 2672152588800)), (nat_lit 6044, Int.ofNat (nat_lit 28714425307200)), (nat_lit 6045, Int.ofNat (nat_lit 31318438795200)), (nat_lit 6046, Int.ofNat (nat_lit 20764754611200)), (nat_lit 6047, Int.ofNat (nat_lit 47303583076800)), (nat_lit 6063, Int.ofNat (nat_lit 3550208205600)), (nat_lit 6064, Int.ofNat (nat_lit 14159602504800)), (nat_lit 6065, Int.ofNat (nat_lit 50540795877600)), (nat_lit 6066, Int.ofNat (nat_lit 58714949336400)), (nat_lit 6067, Int.ofNat (nat_lit 44621368840800)), (nat_lit 6068, Int.ofNat (nat_lit 82584805073400)), (nat_lit 6085, Int.ofNat (nat_lit 5924850140160)), (nat_lit 6086, Int.ofNat (nat_lit 46603049565600)), (nat_lit 6087, Int.ofNat (nat_lit 64561905414000)), (nat_lit 6088, Int.ofNat (nat_lit 58431178094400)), (nat_lit 6089, Int.ofNat (nat_lit 83751050082600)), (nat_lit 6107, Int.ofNat (nat_lit 38700065779200)), (nat_lit 6108, Int.ofNat (nat_lit 81441252748800)), (nat_lit 6109, Int.ofNat (nat_lit 76619479413600)), (nat_lit 6110, Int.ofNat (nat_lit 96041823897600)), (nat_lit 6129, Int.ofNat (nat_lit 36760668134400)), (nat_lit 6130, Int.ofNat (nat_lit 77891482429200)), (nat_lit 6131, Int.ofNat (nat_lit 100837655654400)), (nat_lit 6151, Int.ofNat (nat_lit 36725564548800)), (nat_lit 6152, Int.ofNat (nat_lit 99336377640600)), (nat_lit 6173, Int.ofNat (nat_lit 57215047680000)), (nat_lit 6482, Int.ofNat (nat_lit 1735780838400)), (nat_lit 6485, Int.ofNat (nat_lit 13628959948800)), (nat_lit 6486, Int.ofNat (nat_lit 14833387699200)), (nat_lit 6487, Int.ofNat (nat_lit 5586198912000)), (nat_lit 6488, Int.ofNat (nat_lit 20249487820800)), (nat_lit 6504, Int.ofNat (nat_lit 906549235200)), (nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
theorem block022_data_flat157_step : block022_data_flat157 = (CoefficientMerge.fastMerge block022_data_flat117 block022_data_flat156) := by decide +kernel
theorem block022_data_flat157_original : block022_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded))))))) := by
  rw [block022_data_flat157_step, block022_data_flat117_original, block022_data_flat156_original]
def block022_data_flat158 : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 58329956563200)), (nat_lit 5249, Int.ofNat (nat_lit 71135158752000)), (nat_lit 5269, Int.ofNat (nat_lit 16986153139200)), (nat_lit 5270, Int.ofNat (nat_lit 48554288496000)), (nat_lit 5291, Int.ofNat (nat_lit 27477786268800)), (nat_lit 5556, Int.ofNat (nat_lit 142393305600)), (nat_lit 5561, Int.ofNat (nat_lit 3961249152000)), (nat_lit 5562, Int.ofNat (nat_lit 657701004800)), (nat_lit 5578, Int.ofNat (nat_lit 731019801600)), (nat_lit 5579, Int.ofNat (nat_lit 718685798400)), (nat_lit 5581, Int.ofNat (nat_lit 781859212800)), (nat_lit 5582, Int.ofNat (nat_lit 16022245108800)), (nat_lit 5583, Int.ofNat (nat_lit 13551194686400)), (nat_lit 5584, Int.ofNat (nat_lit 11776027622400)), (nat_lit 5585, Int.ofNat (nat_lit 24502199198400)), (nat_lit 5600, Int.ofNat (nat_lit 3414217766400)), (nat_lit 5602, Int.ofNat (nat_lit 1274989228800)), (nat_lit 5603, Int.ofNat (nat_lit 25932352051200)), (nat_lit 5604, Int.ofNat (nat_lit 27709905507200)), (nat_lit 5605, Int.ofNat (nat_lit 27473854060800)), (nat_lit 5606, Int.ofNat (nat_lit 53106823627200)), (nat_lit 5622, Int.ofNat (nat_lit 6357299110400)), (nat_lit 5623, Int.ofNat (nat_lit 19520661753600)), (nat_lit 5624, Int.ofNat (nat_lit 54017265971200)), (nat_lit 5625, Int.ofNat (nat_lit 60723048870400)), (nat_lit 5626, Int.ofNat (nat_lit 48904332915200)), (nat_lit 5627, Int.ofNat (nat_lit 82971805996800)), (nat_lit 5644, Int.ofNat (nat_lit 7890507752960)), (nat_lit 5645, Int.ofNat (nat_lit 48082095084800)), (nat_lit 5646, Int.ofNat (nat_lit 63896669200000)), (nat_lit 5647, Int.ofNat (nat_lit 55239224230400)), (nat_lit 5648, Int.ofNat (nat_lit 78568808472000)), (nat_lit 5666, Int.ofNat (nat_lit 39256609548800)), (nat_lit 5667, Int.ofNat (nat_lit 80549880678400)), (nat_lit 5668, Int.ofNat (nat_lit 69215540800000)), (nat_lit 5669, Int.ofNat (nat_lit 88196267756800)), (nat_lit 5688, Int.ofNat (nat_lit 35739932211200)), (nat_lit 5689, Int.ofNat (nat_lit 67106442681600)), (nat_lit 5690, Int.ofNat (nat_lit 90606689488000)), (nat_lit 5710, Int.ofNat (nat_lit 25516823091200)), (nat_lit 5711, Int.ofNat (nat_lit 77437241660800)), (nat_lit 5732, Int.ofNat (nat_lit 47533761553600)), (nat_lit 6019, Int.ofNat (nat_lit 390177907200)), (nat_lit 6023, Int.ofNat (nat_lit 7496187508800)), (nat_lit 6024, Int.ofNat (nat_lit 6223620657600)), (nat_lit 6026, Int.ofNat (nat_lit 6958414296000)), (nat_lit 6041, Int.ofNat (nat_lit 1828838131200)), (nat_lit 6043, Int.ofNat (nat_lit 2672152588800)), (nat_lit 6044, Int.ofNat (nat_lit 28714425307200)), (nat_lit 6045, Int.ofNat (nat_lit 31318438795200)), (nat_lit 6046, Int.ofNat (nat_lit 20764754611200)), (nat_lit 6047, Int.ofNat (nat_lit 47303583076800)), (nat_lit 6063, Int.ofNat (nat_lit 3550208205600)), (nat_lit 6064, Int.ofNat (nat_lit 14159602504800)), (nat_lit 6065, Int.ofNat (nat_lit 50540795877600)), (nat_lit 6066, Int.ofNat (nat_lit 58714949336400)), (nat_lit 6067, Int.ofNat (nat_lit 44621368840800)), (nat_lit 6068, Int.ofNat (nat_lit 82584805073400)), (nat_lit 6085, Int.ofNat (nat_lit 5924850140160)), (nat_lit 6086, Int.ofNat (nat_lit 46603049565600)), (nat_lit 6087, Int.ofNat (nat_lit 64561905414000)), (nat_lit 6088, Int.ofNat (nat_lit 58431178094400)), (nat_lit 6089, Int.ofNat (nat_lit 83751050082600)), (nat_lit 6107, Int.ofNat (nat_lit 38700065779200)), (nat_lit 6108, Int.ofNat (nat_lit 81441252748800)), (nat_lit 6109, Int.ofNat (nat_lit 76619479413600)), (nat_lit 6110, Int.ofNat (nat_lit 96041823897600)), (nat_lit 6129, Int.ofNat (nat_lit 36760668134400)), (nat_lit 6130, Int.ofNat (nat_lit 77891482429200)), (nat_lit 6131, Int.ofNat (nat_lit 100837655654400)), (nat_lit 6151, Int.ofNat (nat_lit 36725564548800)), (nat_lit 6152, Int.ofNat (nat_lit 99336377640600)), (nat_lit 6173, Int.ofNat (nat_lit 57215047680000)), (nat_lit 6482, Int.ofNat (nat_lit 1735780838400)), (nat_lit 6485, Int.ofNat (nat_lit 13628959948800)), (nat_lit 6486, Int.ofNat (nat_lit 14833387699200)), (nat_lit 6487, Int.ofNat (nat_lit 5586198912000)), (nat_lit 6488, Int.ofNat (nat_lit 20249487820800)), (nat_lit 6504, Int.ofNat (nat_lit 906549235200)), (nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
theorem block022_data_flat158_step : block022_data_flat158 = (CoefficientMerge.fastMerge block022_data_flat078 block022_data_flat157) := by decide +kernel
theorem block022_data_flat158_original : block022_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded)))))))) := by
  rw [block022_data_flat158_step, block022_data_flat078_original, block022_data_flat157_original]
def block022_data_flat159 : CoefficientMerge.Poly := [(nat_lit 5248, Int.ofNat (nat_lit 58329956563200)), (nat_lit 5249, Int.ofNat (nat_lit 71135158752000)), (nat_lit 5269, Int.ofNat (nat_lit 16986153139200)), (nat_lit 5270, Int.ofNat (nat_lit 48554288496000)), (nat_lit 5291, Int.ofNat (nat_lit 27477786268800)), (nat_lit 5556, Int.ofNat (nat_lit 142393305600)), (nat_lit 5561, Int.ofNat (nat_lit 3961249152000)), (nat_lit 5562, Int.ofNat (nat_lit 657701004800)), (nat_lit 5578, Int.ofNat (nat_lit 731019801600)), (nat_lit 5579, Int.ofNat (nat_lit 718685798400)), (nat_lit 5581, Int.ofNat (nat_lit 781859212800)), (nat_lit 5582, Int.ofNat (nat_lit 16022245108800)), (nat_lit 5583, Int.ofNat (nat_lit 13551194686400)), (nat_lit 5584, Int.ofNat (nat_lit 11776027622400)), (nat_lit 5585, Int.ofNat (nat_lit 24502199198400)), (nat_lit 5600, Int.ofNat (nat_lit 3414217766400)), (nat_lit 5602, Int.ofNat (nat_lit 1274989228800)), (nat_lit 5603, Int.ofNat (nat_lit 25932352051200)), (nat_lit 5604, Int.ofNat (nat_lit 27709905507200)), (nat_lit 5605, Int.ofNat (nat_lit 27473854060800)), (nat_lit 5606, Int.ofNat (nat_lit 53106823627200)), (nat_lit 5622, Int.ofNat (nat_lit 6357299110400)), (nat_lit 5623, Int.ofNat (nat_lit 19520661753600)), (nat_lit 5624, Int.ofNat (nat_lit 54017265971200)), (nat_lit 5625, Int.ofNat (nat_lit 60723048870400)), (nat_lit 5626, Int.ofNat (nat_lit 48904332915200)), (nat_lit 5627, Int.ofNat (nat_lit 82971805996800)), (nat_lit 5644, Int.ofNat (nat_lit 7890507752960)), (nat_lit 5645, Int.ofNat (nat_lit 48082095084800)), (nat_lit 5646, Int.ofNat (nat_lit 63896669200000)), (nat_lit 5647, Int.ofNat (nat_lit 55239224230400)), (nat_lit 5648, Int.ofNat (nat_lit 78568808472000)), (nat_lit 5666, Int.ofNat (nat_lit 39256609548800)), (nat_lit 5667, Int.ofNat (nat_lit 80549880678400)), (nat_lit 5668, Int.ofNat (nat_lit 69215540800000)), (nat_lit 5669, Int.ofNat (nat_lit 88196267756800)), (nat_lit 5688, Int.ofNat (nat_lit 35739932211200)), (nat_lit 5689, Int.ofNat (nat_lit 67106442681600)), (nat_lit 5690, Int.ofNat (nat_lit 90606689488000)), (nat_lit 5710, Int.ofNat (nat_lit 25516823091200)), (nat_lit 5711, Int.ofNat (nat_lit 77437241660800)), (nat_lit 5732, Int.ofNat (nat_lit 47533761553600)), (nat_lit 6019, Int.ofNat (nat_lit 390177907200)), (nat_lit 6023, Int.ofNat (nat_lit 7496187508800)), (nat_lit 6024, Int.ofNat (nat_lit 6223620657600)), (nat_lit 6026, Int.ofNat (nat_lit 6958414296000)), (nat_lit 6041, Int.ofNat (nat_lit 1828838131200)), (nat_lit 6043, Int.ofNat (nat_lit 2672152588800)), (nat_lit 6044, Int.ofNat (nat_lit 28714425307200)), (nat_lit 6045, Int.ofNat (nat_lit 31318438795200)), (nat_lit 6046, Int.ofNat (nat_lit 20764754611200)), (nat_lit 6047, Int.ofNat (nat_lit 47303583076800)), (nat_lit 6063, Int.ofNat (nat_lit 3550208205600)), (nat_lit 6064, Int.ofNat (nat_lit 14159602504800)), (nat_lit 6065, Int.ofNat (nat_lit 50540795877600)), (nat_lit 6066, Int.ofNat (nat_lit 58714949336400)), (nat_lit 6067, Int.ofNat (nat_lit 44621368840800)), (nat_lit 6068, Int.ofNat (nat_lit 82584805073400)), (nat_lit 6085, Int.ofNat (nat_lit 5924850140160)), (nat_lit 6086, Int.ofNat (nat_lit 46603049565600)), (nat_lit 6087, Int.ofNat (nat_lit 64561905414000)), (nat_lit 6088, Int.ofNat (nat_lit 58431178094400)), (nat_lit 6089, Int.ofNat (nat_lit 83751050082600)), (nat_lit 6107, Int.ofNat (nat_lit 38700065779200)), (nat_lit 6108, Int.ofNat (nat_lit 81441252748800)), (nat_lit 6109, Int.ofNat (nat_lit 76619479413600)), (nat_lit 6110, Int.ofNat (nat_lit 96041823897600)), (nat_lit 6129, Int.ofNat (nat_lit 36760668134400)), (nat_lit 6130, Int.ofNat (nat_lit 77891482429200)), (nat_lit 6131, Int.ofNat (nat_lit 100837655654400)), (nat_lit 6151, Int.ofNat (nat_lit 36725564548800)), (nat_lit 6152, Int.ofNat (nat_lit 99336377640600)), (nat_lit 6173, Int.ofNat (nat_lit 57215047680000)), (nat_lit 6482, Int.ofNat (nat_lit 1735780838400)), (nat_lit 6485, Int.ofNat (nat_lit 13628959948800)), (nat_lit 6486, Int.ofNat (nat_lit 14833387699200)), (nat_lit 6487, Int.ofNat (nat_lit 5586198912000)), (nat_lit 6488, Int.ofNat (nat_lit 20249487820800)), (nat_lit 6504, Int.ofNat (nat_lit 906549235200)), (nat_lit 6505, Int.ofNat (nat_lit 9616380480000))]
theorem block022_data_flat159_step : block022_data_flat159 = (CoefficientMerge.trim block022_data_flat158) := by decide +kernel
theorem block022_data_flat159_original : block022_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded))))))))) := by
  rw [block022_data_flat159_step, block022_data_flat158_original]
theorem block022_data : block022 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58329956563200 : Int) atom1616Coded) (CoefficientMerge.scale (71135158752000 : Int) atom1617Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16986153139200 : Int) atom1618Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48554288496000 : Int) atom1619Coded) (CoefficientMerge.scale (27477786268800 : Int) atom1620Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142393305600 : Int) atom1621Coded) (CoefficientMerge.scale (3961249152000 : Int) atom1622Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (657701004800 : Int) atom1623Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (731019801600 : Int) atom1624Coded) (CoefficientMerge.scale (718685798400 : Int) atom1625Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781859212800 : Int) atom1626Coded) (CoefficientMerge.scale (16022245108800 : Int) atom1627Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13551194686400 : Int) atom1628Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11776027622400 : Int) atom1629Coded) (CoefficientMerge.scale (24502199198400 : Int) atom1630Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3414217766400 : Int) atom1631Coded) (CoefficientMerge.scale (1274989228800 : Int) atom1632Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25932352051200 : Int) atom1633Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27709905507200 : Int) atom1634Coded) (CoefficientMerge.scale (27473854060800 : Int) atom1635Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53106823627200 : Int) atom1636Coded) (CoefficientMerge.scale (6357299110400 : Int) atom1637Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19520661753600 : Int) atom1638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54017265971200 : Int) atom1639Coded) (CoefficientMerge.scale (60723048870400 : Int) atom1640Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (48904332915200 : Int) atom1641Coded) (CoefficientMerge.scale (82971805996800 : Int) atom1642Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7890507752960 : Int) atom1643Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48082095084800 : Int) atom1644Coded) (CoefficientMerge.scale (63896669200000 : Int) atom1645Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55239224230400 : Int) atom1646Coded) (CoefficientMerge.scale (78568808472000 : Int) atom1647Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39256609548800 : Int) atom1648Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80549880678400 : Int) atom1649Coded) (CoefficientMerge.scale (69215540800000 : Int) atom1650Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (88196267756800 : Int) atom1651Coded) (CoefficientMerge.scale (35739932211200 : Int) atom1652Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (67106442681600 : Int) atom1653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (90606689488000 : Int) atom1654Coded) (CoefficientMerge.scale (25516823091200 : Int) atom1655Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77437241660800 : Int) atom1656Coded) (CoefficientMerge.scale (47533761553600 : Int) atom1657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390177907200 : Int) atom1658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7496187508800 : Int) atom1659Coded) (CoefficientMerge.scale (6223620657600 : Int) atom1660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6958414296000 : Int) atom1661Coded) (CoefficientMerge.scale (1828838131200 : Int) atom1662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2672152588800 : Int) atom1663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28714425307200 : Int) atom1664Coded) (CoefficientMerge.scale (31318438795200 : Int) atom1665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20764754611200 : Int) atom1666Coded) (CoefficientMerge.scale (47303583076800 : Int) atom1667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3550208205600 : Int) atom1668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14159602504800 : Int) atom1669Coded) (CoefficientMerge.scale (50540795877600 : Int) atom1670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58714949336400 : Int) atom1671Coded) (CoefficientMerge.scale (44621368840800 : Int) atom1672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82584805073400 : Int) atom1673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5924850140160 : Int) atom1674Coded) (CoefficientMerge.scale (46603049565600 : Int) atom1675Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64561905414000 : Int) atom1676Coded) (CoefficientMerge.scale (58431178094400 : Int) atom1677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83751050082600 : Int) atom1678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38700065779200 : Int) atom1679Coded) (CoefficientMerge.scale (81441252748800 : Int) atom1680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (76619479413600 : Int) atom1681Coded) (CoefficientMerge.scale (96041823897600 : Int) atom1682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36760668134400 : Int) atom1683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77891482429200 : Int) atom1684Coded) (CoefficientMerge.scale (100837655654400 : Int) atom1685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36725564548800 : Int) atom1686Coded) (CoefficientMerge.scale (99336377640600 : Int) atom1687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57215047680000 : Int) atom1688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1735780838400 : Int) atom1689Coded) (CoefficientMerge.scale (13628959948800 : Int) atom1690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14833387699200 : Int) atom1691Coded) (CoefficientMerge.scale (5586198912000 : Int) atom1692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20249487820800 : Int) atom1693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906549235200 : Int) atom1694Coded) (CoefficientMerge.scale (9616380480000 : Int) atom1695Coded)))))))) := by
  have h : block022 = block022_data_flat159 := by decide +kernel
  exact h.trans block022_data_flat159_original
theorem block022_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block022 := by
  rw [block022_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1616Coded_nonneg g hg hA hB) (atom1617Coded_nonneg g hg hA hB)) (add_nonneg (atom1618Coded_nonneg g hg hA hB) (add_nonneg (atom1619Coded_nonneg g hg hA hB) (atom1620Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1621Coded_nonneg g hg hA hB) (atom1622Coded_nonneg g hg hA hB)) (add_nonneg (atom1623Coded_nonneg g hg hA hB) (add_nonneg (atom1624Coded_nonneg g hg hA hB) (atom1625Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1626Coded_nonneg g hg hA hB) (atom1627Coded_nonneg g hg hA hB)) (add_nonneg (atom1628Coded_nonneg g hg hA hB) (add_nonneg (atom1629Coded_nonneg g hg hA hB) (atom1630Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1631Coded_nonneg g hg hA hB) (atom1632Coded_nonneg g hg hA hB)) (add_nonneg (atom1633Coded_nonneg g hg hA hB) (add_nonneg (atom1634Coded_nonneg g hg hA hB) (atom1635Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1636Coded_nonneg g hg hA hB) (atom1637Coded_nonneg g hg hA hB)) (add_nonneg (atom1638Coded_nonneg g hg hA hB) (add_nonneg (atom1639Coded_nonneg g hg hA hB) (atom1640Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1641Coded_nonneg g hg hA hB) (atom1642Coded_nonneg g hg hA hB)) (add_nonneg (atom1643Coded_nonneg g hg hA hB) (add_nonneg (atom1644Coded_nonneg g hg hA hB) (atom1645Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1646Coded_nonneg g hg hA hB) (atom1647Coded_nonneg g hg hA hB)) (add_nonneg (atom1648Coded_nonneg g hg hA hB) (add_nonneg (atom1649Coded_nonneg g hg hA hB) (atom1650Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1651Coded_nonneg g hg hA hB) (atom1652Coded_nonneg g hg hA hB)) (add_nonneg (atom1653Coded_nonneg g hg hA hB) (add_nonneg (atom1654Coded_nonneg g hg hA hB) (atom1655Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1656Coded_nonneg g hg hA hB) (atom1657Coded_nonneg g hg hA hB)) (add_nonneg (atom1658Coded_nonneg g hg hA hB) (add_nonneg (atom1659Coded_nonneg g hg hA hB) (atom1660Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1661Coded_nonneg g hg hA hB) (atom1662Coded_nonneg g hg hA hB)) (add_nonneg (atom1663Coded_nonneg g hg hA hB) (add_nonneg (atom1664Coded_nonneg g hg hA hB) (atom1665Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1666Coded_nonneg g hg hA hB) (atom1667Coded_nonneg g hg hA hB)) (add_nonneg (atom1668Coded_nonneg g hg hA hB) (add_nonneg (atom1669Coded_nonneg g hg hA hB) (atom1670Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1671Coded_nonneg g hg hA hB) (atom1672Coded_nonneg g hg hA hB)) (add_nonneg (atom1673Coded_nonneg g hg hA hB) (add_nonneg (atom1674Coded_nonneg g hg hA hB) (atom1675Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1676Coded_nonneg g hg hA hB) (atom1677Coded_nonneg g hg hA hB)) (add_nonneg (atom1678Coded_nonneg g hg hA hB) (add_nonneg (atom1679Coded_nonneg g hg hA hB) (atom1680Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1681Coded_nonneg g hg hA hB) (atom1682Coded_nonneg g hg hA hB)) (add_nonneg (atom1683Coded_nonneg g hg hA hB) (add_nonneg (atom1684Coded_nonneg g hg hA hB) (atom1685Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1686Coded_nonneg g hg hA hB) (atom1687Coded_nonneg g hg hA hB)) (add_nonneg (atom1688Coded_nonneg g hg hA hB) (add_nonneg (atom1689Coded_nonneg g hg hA hB) (atom1690Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1691Coded_nonneg g hg hA hB) (atom1692Coded_nonneg g hg hA hB)) (add_nonneg (atom1693Coded_nonneg g hg hA hB) (add_nonneg (atom1694Coded_nonneg g hg hA hB) (atom1695Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
