-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1649 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1649 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1649 = ((g 6) * (g 8) * (g 9)) := by
  norm_num [atom1649, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1649_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19897350303600 : Int) atom1649) := by
  rw [SparsePolynomial.eval_scale, eval_atom1649]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1649Coded : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 1))]
theorem atom1649Coded_decode : atom1649 = SparsePolynomial.decodeCubic 24 atom1649Coded := by decide +kernel
theorem atom1649Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) := by
  have h := atom1649_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1649Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1650 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1650 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1650 = ((g 6) * (g 8) * (g 13)) := by
  norm_num [atom1650, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1650_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5145488409600 : Int) atom1650) := by
  rw [SparsePolynomial.eval_scale, eval_atom1650]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1650Coded : CoefficientMerge.Poly := [(nat_lit 3661, Int.ofNat (nat_lit 1))]
theorem atom1650Coded_decode : atom1650 = SparsePolynomial.decodeCubic 24 atom1650Coded := by decide +kernel
theorem atom1650Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded) := by
  have h := atom1650_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1650Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1651 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1651 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1651 = ((g 6) * (g 8) * (g 14)) := by
  norm_num [atom1651, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1651_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10290976819200 : Int) atom1651) := by
  rw [SparsePolynomial.eval_scale, eval_atom1651]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1651Coded : CoefficientMerge.Poly := [(nat_lit 3662, Int.ofNat (nat_lit 1))]
theorem atom1651Coded_decode : atom1651 = SparsePolynomial.decodeCubic 24 atom1651Coded := by decide +kernel
theorem atom1651Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) := by
  have h := atom1651_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1651Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1652 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1652 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1652 = ((g 6) * (g 8) * (g 15)) := by
  norm_num [atom1652, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1652_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15436465228800 : Int) atom1652) := by
  rw [SparsePolynomial.eval_scale, eval_atom1652]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1652Coded : CoefficientMerge.Poly := [(nat_lit 3663, Int.ofNat (nat_lit 1))]
theorem atom1652Coded_decode : atom1652 = SparsePolynomial.decodeCubic 24 atom1652Coded := by decide +kernel
theorem atom1652Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) := by
  have h := atom1652_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1652Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1653 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1653 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1653 = ((g 6) * (g 8) * (g 16)) := by
  norm_num [atom1653, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1653_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20581953638400 : Int) atom1653) := by
  rw [SparsePolynomial.eval_scale, eval_atom1653]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1653Coded : CoefficientMerge.Poly := [(nat_lit 3664, Int.ofNat (nat_lit 1))]
theorem atom1653Coded_decode : atom1653 = SparsePolynomial.decodeCubic 24 atom1653Coded := by decide +kernel
theorem atom1653Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded) := by
  have h := atom1653_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1653Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1654 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1654 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1654 = ((g 6) * (g 8) * (g 17)) := by
  norm_num [atom1654, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1654_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25727442048000 : Int) atom1654) := by
  rw [SparsePolynomial.eval_scale, eval_atom1654]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1654Coded : CoefficientMerge.Poly := [(nat_lit 3665, Int.ofNat (nat_lit 1))]
theorem atom1654Coded_decode : atom1654 = SparsePolynomial.decodeCubic 24 atom1654Coded := by decide +kernel
theorem atom1654Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) := by
  have h := atom1654_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1654Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1655 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1655 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1655 = ((g 6) * (g 8) * (g 18)) := by
  norm_num [atom1655, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1655_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11587980096000 : Int) atom1655) := by
  rw [SparsePolynomial.eval_scale, eval_atom1655]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1655Coded : CoefficientMerge.Poly := [(nat_lit 3666, Int.ofNat (nat_lit 1))]
theorem atom1655Coded_decode : atom1655 = SparsePolynomial.decodeCubic 24 atom1655Coded := by decide +kernel
theorem atom1655Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded) := by
  have h := atom1655_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1655Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1656 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1656 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1656 = ((g 6) * (g 8) * (g 19)) := by
  norm_num [atom1656, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1656_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19816509081600 : Int) atom1656) := by
  rw [SparsePolynomial.eval_scale, eval_atom1656]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1656Coded : CoefficientMerge.Poly := [(nat_lit 3667, Int.ofNat (nat_lit 1))]
theorem atom1656Coded_decode : atom1656 = SparsePolynomial.decodeCubic 24 atom1656Coded := by decide +kernel
theorem atom1656Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) := by
  have h := atom1656_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1656Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1657 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1657 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1657 = ((g 6) * (g 8) * (g 20)) := by
  norm_num [atom1657, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1657_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28045038067200 : Int) atom1657) := by
  rw [SparsePolynomial.eval_scale, eval_atom1657]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1657Coded : CoefficientMerge.Poly := [(nat_lit 3668, Int.ofNat (nat_lit 1))]
theorem atom1657Coded_decode : atom1657 = SparsePolynomial.decodeCubic 24 atom1657Coded := by decide +kernel
theorem atom1657Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) := by
  have h := atom1657_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1657Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1658 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1658 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1658 = ((g 6) * (g 8) * (g 21)) := by
  norm_num [atom1658, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1658_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101836019577600 : Int) atom1658) := by
  rw [SparsePolynomial.eval_scale, eval_atom1658]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1658Coded : CoefficientMerge.Poly := [(nat_lit 3669, Int.ofNat (nat_lit 1))]
theorem atom1658Coded_decode : atom1658 = SparsePolynomial.decodeCubic 24 atom1658Coded := by decide +kernel
theorem atom1658Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded) := by
  have h := atom1658_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1658Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1659 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1659 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1659 = ((g 6) * (g 8) * (g 22)) := by
  norm_num [atom1659, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1659_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175627001088000 : Int) atom1659) := by
  rw [SparsePolynomial.eval_scale, eval_atom1659]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1659Coded : CoefficientMerge.Poly := [(nat_lit 3670, Int.ofNat (nat_lit 1))]
theorem atom1659Coded_decode : atom1659 = SparsePolynomial.decodeCubic 24 atom1659Coded := by decide +kernel
theorem atom1659Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) := by
  have h := atom1659_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1659Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1660 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1660 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1660 = ((g 6) * (g 8) * (g 23)) := by
  norm_num [atom1660, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1660_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (259831217923200 : Int) atom1660) := by
  rw [SparsePolynomial.eval_scale, eval_atom1660]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1660Coded : CoefficientMerge.Poly := [(nat_lit 3671, Int.ofNat (nat_lit 1))]
theorem atom1660Coded_decode : atom1660 = SparsePolynomial.decodeCubic 24 atom1660Coded := by decide +kernel
theorem atom1660Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded) := by
  have h := atom1660_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1660Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1661 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1661 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1661 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom1661, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1661_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31293969260400 : Int) atom1661) := by
  rw [SparsePolynomial.eval_scale, eval_atom1661]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1661Coded : CoefficientMerge.Poly := [(nat_lit 3681, Int.ofNat (nat_lit 1))]
theorem atom1661Coded_decode : atom1661 = SparsePolynomial.decodeCubic 24 atom1661Coded := by decide +kernel
theorem atom1661Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) := by
  have h := atom1661_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1661Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1662 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1662 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1662 = ((g 6) * (g 9) * (g 10)) := by
  norm_num [atom1662, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1662_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43670515451904 : Int) atom1662) := by
  rw [SparsePolynomial.eval_scale, eval_atom1662]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1662Coded : CoefficientMerge.Poly := [(nat_lit 3682, Int.ofNat (nat_lit 1))]
theorem atom1662Coded_decode : atom1662 = SparsePolynomial.decodeCubic 24 atom1662Coded := by decide +kernel
theorem atom1662Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) := by
  have h := atom1662_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1662Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1663 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1663 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1663 = ((g 6) * (g 9) * (g 11)) := by
  norm_num [atom1663, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1663_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22669871994000 : Int) atom1663) := by
  rw [SparsePolynomial.eval_scale, eval_atom1663]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1663Coded : CoefficientMerge.Poly := [(nat_lit 3683, Int.ofNat (nat_lit 1))]
theorem atom1663Coded_decode : atom1663 = SparsePolynomial.decodeCubic 24 atom1663Coded := by decide +kernel
theorem atom1663Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded) := by
  have h := atom1663_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1663Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1664 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1664 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1664 = ((g 6) * (g 9) * (g 12)) := by
  norm_num [atom1664, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1664_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26794767661200 : Int) atom1664) := by
  rw [SparsePolynomial.eval_scale, eval_atom1664]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1664Coded : CoefficientMerge.Poly := [(nat_lit 3684, Int.ofNat (nat_lit 1))]
theorem atom1664Coded_decode : atom1664 = SparsePolynomial.decodeCubic 24 atom1664Coded := by decide +kernel
theorem atom1664Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) := by
  have h := atom1664_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1664Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1665 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1665 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1665 = ((g 6) * (g 9) * (g 13)) := by
  norm_num [atom1665, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1665_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29899070586000 : Int) atom1665) := by
  rw [SparsePolynomial.eval_scale, eval_atom1665]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1665Coded : CoefficientMerge.Poly := [(nat_lit 3685, Int.ofNat (nat_lit 1))]
theorem atom1665Coded_decode : atom1665 = SparsePolynomial.decodeCubic 24 atom1665Coded := by decide +kernel
theorem atom1665Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded) := by
  have h := atom1665_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1665Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1666 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1666 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1666 = ((g 6) * (g 9) * (g 14)) := by
  norm_num [atom1666, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1666_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36086414086800 : Int) atom1666) := by
  rw [SparsePolynomial.eval_scale, eval_atom1666]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1666Coded : CoefficientMerge.Poly := [(nat_lit 3686, Int.ofNat (nat_lit 1))]
theorem atom1666Coded_decode : atom1666 = SparsePolynomial.decodeCubic 24 atom1666Coded := by decide +kernel
theorem atom1666Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) := by
  have h := atom1666_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1666Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1667 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1667 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1667 = ((g 6) * (g 9) * (g 15)) := by
  norm_num [atom1667, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1667_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42273757587600 : Int) atom1667) := by
  rw [SparsePolynomial.eval_scale, eval_atom1667]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1667Coded : CoefficientMerge.Poly := [(nat_lit 3687, Int.ofNat (nat_lit 1))]
theorem atom1667Coded_decode : atom1667 = SparsePolynomial.decodeCubic 24 atom1667Coded := by decide +kernel
theorem atom1667Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) := by
  have h := atom1667_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1667Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1668 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1668 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1668 = ((g 6) * (g 9) * (g 16)) := by
  norm_num [atom1668, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1668_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48461101088400 : Int) atom1668) := by
  rw [SparsePolynomial.eval_scale, eval_atom1668]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1668Coded : CoefficientMerge.Poly := [(nat_lit 3688, Int.ofNat (nat_lit 1))]
theorem atom1668Coded_decode : atom1668 = SparsePolynomial.decodeCubic 24 atom1668Coded := by decide +kernel
theorem atom1668Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded) := by
  have h := atom1668_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1668Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1669 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1669 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1669 = ((g 6) * (g 9) * (g 17)) := by
  norm_num [atom1669, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1669_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54648444589200 : Int) atom1669) := by
  rw [SparsePolynomial.eval_scale, eval_atom1669]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1669Coded : CoefficientMerge.Poly := [(nat_lit 3689, Int.ofNat (nat_lit 1))]
theorem atom1669Coded_decode : atom1669 = SparsePolynomial.decodeCubic 24 atom1669Coded := by decide +kernel
theorem atom1669Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) := by
  have h := atom1669_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1669Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1670 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1670 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1670 = ((g 6) * (g 9) * (g 18)) := by
  norm_num [atom1670, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1670_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47823313522248 : Int) atom1670) := by
  rw [SparsePolynomial.eval_scale, eval_atom1670]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1670Coded : CoefficientMerge.Poly := [(nat_lit 3690, Int.ofNat (nat_lit 1))]
theorem atom1670Coded_decode : atom1670 = SparsePolynomial.decodeCubic 24 atom1670Coded := by decide +kernel
theorem atom1670Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded) := by
  have h := atom1670_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1670Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1671 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1671 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1671 = ((g 6) * (g 9) * (g 19)) := by
  norm_num [atom1671, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1671_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65569641223680 : Int) atom1671) := by
  rw [SparsePolynomial.eval_scale, eval_atom1671]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1671Coded : CoefficientMerge.Poly := [(nat_lit 3691, Int.ofNat (nat_lit 1))]
theorem atom1671Coded_decode : atom1671 = SparsePolynomial.decodeCubic 24 atom1671Coded := by decide +kernel
theorem atom1671Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) := by
  have h := atom1671_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1671Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1672 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1672 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1672 = ((g 6) * (g 9) * (g 20)) := by
  norm_num [atom1672, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1672_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83315968925112 : Int) atom1672) := by
  rw [SparsePolynomial.eval_scale, eval_atom1672]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1672Coded : CoefficientMerge.Poly := [(nat_lit 3692, Int.ofNat (nat_lit 1))]
theorem atom1672Coded_decode : atom1672 = SparsePolynomial.decodeCubic 24 atom1672Coded := by decide +kernel
theorem atom1672Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) := by
  have h := atom1672_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1672Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1673 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1673 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1673 = ((g 6) * (g 9) * (g 21)) := by
  norm_num [atom1673, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1673_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168997180831380 : Int) atom1673) := by
  rw [SparsePolynomial.eval_scale, eval_atom1673]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1673Coded : CoefficientMerge.Poly := [(nat_lit 3693, Int.ofNat (nat_lit 1))]
theorem atom1673Coded_decode : atom1673 = SparsePolynomial.decodeCubic 24 atom1673Coded := by decide +kernel
theorem atom1673Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded) := by
  have h := atom1673_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1673Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1674 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1674 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1674 = ((g 6) * (g 9) * (g 22)) := by
  norm_num [atom1674, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1674_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254678392737648 : Int) atom1674) := by
  rw [SparsePolynomial.eval_scale, eval_atom1674]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1674Coded : CoefficientMerge.Poly := [(nat_lit 3694, Int.ofNat (nat_lit 1))]
theorem atom1674Coded_decode : atom1674 = SparsePolynomial.decodeCubic 24 atom1674Coded := by decide +kernel
theorem atom1674Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) := by
  have h := atom1674_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1674Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1675 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1675 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1675 = ((g 6) * (g 9) * (g 23)) := by
  norm_num [atom1675, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1675_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349755587977950 : Int) atom1675) := by
  rw [SparsePolynomial.eval_scale, eval_atom1675]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1675Coded : CoefficientMerge.Poly := [(nat_lit 3695, Int.ofNat (nat_lit 1))]
theorem atom1675Coded_decode : atom1675 = SparsePolynomial.decodeCubic 24 atom1675Coded := by decide +kernel
theorem atom1675Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded) := by
  have h := atom1675_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1675Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1676 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1676 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1676 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom1676, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1676_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41144504117904 : Int) atom1676) := by
  rw [SparsePolynomial.eval_scale, eval_atom1676]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1676Coded : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 1))]
theorem atom1676Coded_decode : atom1676 = SparsePolynomial.decodeCubic 24 atom1676Coded := by decide +kernel
theorem atom1676Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) := by
  have h := atom1676_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1676Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1677 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1677 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1677 = ((g 6) * (g 10) * (g 11)) := by
  norm_num [atom1677, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1677_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68517563369904 : Int) atom1677) := by
  rw [SparsePolynomial.eval_scale, eval_atom1677]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1677Coded : CoefficientMerge.Poly := [(nat_lit 3707, Int.ofNat (nat_lit 1))]
theorem atom1677Coded_decode : atom1677 = SparsePolynomial.decodeCubic 24 atom1677Coded := by decide +kernel
theorem atom1677Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) := by
  have h := atom1677_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1677Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1678 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1678 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1678 = ((g 6) * (g 10) * (g 12)) := by
  norm_num [atom1678, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1678_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69580680809904 : Int) atom1678) := by
  rw [SparsePolynomial.eval_scale, eval_atom1678]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1678Coded : CoefficientMerge.Poly := [(nat_lit 3708, Int.ofNat (nat_lit 1))]
theorem atom1678Coded_decode : atom1678 = SparsePolynomial.decodeCubic 24 atom1678Coded := by decide +kernel
theorem atom1678Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded) := by
  have h := atom1678_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1678Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1679 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1679 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1679 = ((g 6) * (g 10) * (g 13)) := by
  norm_num [atom1679, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1679_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75789286659504 : Int) atom1679) := by
  rw [SparsePolynomial.eval_scale, eval_atom1679]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1679Coded : CoefficientMerge.Poly := [(nat_lit 3709, Int.ofNat (nat_lit 1))]
theorem atom1679Coded_decode : atom1679 = SparsePolynomial.decodeCubic 24 atom1679Coded := by decide +kernel
theorem atom1679Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) := by
  have h := atom1679_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1679Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1680 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1680 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1680 = ((g 6) * (g 10) * (g 14)) := by
  norm_num [atom1680, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1680_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81997892509104 : Int) atom1680) := by
  rw [SparsePolynomial.eval_scale, eval_atom1680]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1680Coded : CoefficientMerge.Poly := [(nat_lit 3710, Int.ofNat (nat_lit 1))]
theorem atom1680Coded_decode : atom1680 = SparsePolynomial.decodeCubic 24 atom1680Coded := by decide +kernel
theorem atom1680Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded) := by
  have h := atom1680_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1680Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1681 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1681 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1681 = ((g 6) * (g 10) * (g 15)) := by
  norm_num [atom1681, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1681_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (88206498358704 : Int) atom1681) := by
  rw [SparsePolynomial.eval_scale, eval_atom1681]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1681Coded : CoefficientMerge.Poly := [(nat_lit 3711, Int.ofNat (nat_lit 1))]
theorem atom1681Coded_decode : atom1681 = SparsePolynomial.decodeCubic 24 atom1681Coded := by decide +kernel
theorem atom1681Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) := by
  have h := atom1681_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1681Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1682 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1682 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1682 = ((g 6) * (g 10) * (g 16)) := by
  norm_num [atom1682, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1682_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (94415104208304 : Int) atom1682) := by
  rw [SparsePolynomial.eval_scale, eval_atom1682]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1682Coded : CoefficientMerge.Poly := [(nat_lit 3712, Int.ofNat (nat_lit 1))]
theorem atom1682Coded_decode : atom1682 = SparsePolynomial.decodeCubic 24 atom1682Coded := by decide +kernel
theorem atom1682Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) := by
  have h := atom1682_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1682Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1683 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1683 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1683 = ((g 6) * (g 10) * (g 17)) := by
  norm_num [atom1683, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1683_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100623710057904 : Int) atom1683) := by
  rw [SparsePolynomial.eval_scale, eval_atom1683]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1683Coded : CoefficientMerge.Poly := [(nat_lit 3713, Int.ofNat (nat_lit 1))]
theorem atom1683Coded_decode : atom1683 = SparsePolynomial.decodeCubic 24 atom1683Coded := by decide +kernel
theorem atom1683Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded) := by
  have h := atom1683_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1683Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1684 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1684 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1684 = ((g 6) * (g 10) * (g 18)) := by
  norm_num [atom1684, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1684_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99978636340440 : Int) atom1684) := by
  rw [SparsePolynomial.eval_scale, eval_atom1684]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1684Coded : CoefficientMerge.Poly := [(nat_lit 3714, Int.ofNat (nat_lit 1))]
theorem atom1684Coded_decode : atom1684 = SparsePolynomial.decodeCubic 24 atom1684Coded := by decide +kernel
theorem atom1684Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) := by
  have h := atom1684_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1684Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1685 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1685 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1685 = ((g 6) * (g 10) * (g 19)) := by
  norm_num [atom1685, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1685_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122637785402880 : Int) atom1685) := by
  rw [SparsePolynomial.eval_scale, eval_atom1685]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1685Coded : CoefficientMerge.Poly := [(nat_lit 3715, Int.ofNat (nat_lit 1))]
theorem atom1685Coded_decode : atom1685 = SparsePolynomial.decodeCubic 24 atom1685Coded := by decide +kernel
theorem atom1685Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded) := by
  have h := atom1685_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1685Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1686 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1686 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1686 = ((g 6) * (g 10) * (g 20)) := by
  norm_num [atom1686, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1686_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145296934465320 : Int) atom1686) := by
  rw [SparsePolynomial.eval_scale, eval_atom1686]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1686Coded : CoefficientMerge.Poly := [(nat_lit 3716, Int.ofNat (nat_lit 1))]
theorem atom1686Coded_decode : atom1686 = SparsePolynomial.decodeCubic 24 atom1686Coded := by decide +kernel
theorem atom1686Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) := by
  have h := atom1686_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1686Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1687 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1687 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1687 = ((g 6) * (g 10) * (g 21)) := by
  norm_num [atom1687, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1687_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229643480261052 : Int) atom1687) := by
  rw [SparsePolynomial.eval_scale, eval_atom1687]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1687Coded : CoefficientMerge.Poly := [(nat_lit 3717, Int.ofNat (nat_lit 1))]
theorem atom1687Coded_decode : atom1687 = SparsePolynomial.decodeCubic 24 atom1687Coded := by decide +kernel
theorem atom1687Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) := by
  have h := atom1687_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1687Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1688 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1688 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1688 = ((g 6) * (g 10) * (g 22)) := by
  norm_num [atom1688, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1688_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (313990026056784 : Int) atom1688) := by
  rw [SparsePolynomial.eval_scale, eval_atom1688]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1688Coded : CoefficientMerge.Poly := [(nat_lit 3718, Int.ofNat (nat_lit 1))]
theorem atom1688Coded_decode : atom1688 = SparsePolynomial.decodeCubic 24 atom1688Coded := by decide +kernel
theorem atom1688Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded) := by
  have h := atom1688_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1688Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1689 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1689 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1689 = ((g 6) * (g 10) * (g 23)) := by
  norm_num [atom1689, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1689_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (405876047439258 : Int) atom1689) := by
  rw [SparsePolynomial.eval_scale, eval_atom1689]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1689Coded : CoefficientMerge.Poly := [(nat_lit 3719, Int.ofNat (nat_lit 1))]
theorem atom1689Coded_decode : atom1689 = SparsePolynomial.decodeCubic 24 atom1689Coded := by decide +kernel
theorem atom1689Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) := by
  have h := atom1689_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1689Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1690 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1690 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1690 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom1690, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1690_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62307098330400 : Int) atom1690) := by
  rw [SparsePolynomial.eval_scale, eval_atom1690]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1690Coded : CoefficientMerge.Poly := [(nat_lit 3731, Int.ofNat (nat_lit 1))]
theorem atom1690Coded_decode : atom1690 = SparsePolynomial.decodeCubic 24 atom1690Coded := by decide +kernel
theorem atom1690Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded) := by
  have h := atom1690_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1690Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1691 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1691 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1691 = ((g 6) * (g 11) * (g 12)) := by
  norm_num [atom1691, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1691_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104900012632800 : Int) atom1691) := by
  rw [SparsePolynomial.eval_scale, eval_atom1691]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1691Coded : CoefficientMerge.Poly := [(nat_lit 3732, Int.ofNat (nat_lit 1))]
theorem atom1691Coded_decode : atom1691 = SparsePolynomial.decodeCubic 24 atom1691Coded := by decide +kernel
theorem atom1691Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) := by
  have h := atom1691_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1691Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1692 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1692 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1692 = ((g 6) * (g 11) * (g 13)) := by
  norm_num [atom1692, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1692_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107026247512800 : Int) atom1692) := by
  rw [SparsePolynomial.eval_scale, eval_atom1692]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1692Coded : CoefficientMerge.Poly := [(nat_lit 3733, Int.ofNat (nat_lit 1))]
theorem atom1692Coded_decode : atom1692 = SparsePolynomial.decodeCubic 24 atom1692Coded := by decide +kernel
theorem atom1692Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) := by
  have h := atom1692_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1692Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1693 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1693 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1693 = ((g 6) * (g 11) * (g 14)) := by
  norm_num [atom1693, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1693_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109152482392800 : Int) atom1693) := by
  rw [SparsePolynomial.eval_scale, eval_atom1693]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1693Coded : CoefficientMerge.Poly := [(nat_lit 3734, Int.ofNat (nat_lit 1))]
theorem atom1693Coded_decode : atom1693 = SparsePolynomial.decodeCubic 24 atom1693Coded := by decide +kernel
theorem atom1693Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded) := by
  have h := atom1693_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1693Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1694 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1694 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1694 = ((g 6) * (g 11) * (g 15)) := by
  norm_num [atom1694, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1694_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (111278717272800 : Int) atom1694) := by
  rw [SparsePolynomial.eval_scale, eval_atom1694]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1694Coded : CoefficientMerge.Poly := [(nat_lit 3735, Int.ofNat (nat_lit 1))]
theorem atom1694Coded_decode : atom1694 = SparsePolynomial.decodeCubic 24 atom1694Coded := by decide +kernel
theorem atom1694Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) := by
  have h := atom1694_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1694Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1695 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1695 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1695 = ((g 6) * (g 11) * (g 16)) := by
  norm_num [atom1695, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1695_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (116487992728800 : Int) atom1695) := by
  rw [SparsePolynomial.eval_scale, eval_atom1695]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1695Coded : CoefficientMerge.Poly := [(nat_lit 3736, Int.ofNat (nat_lit 1))]
theorem atom1695Coded_decode : atom1695 = SparsePolynomial.decodeCubic 24 atom1695Coded := by decide +kernel
theorem atom1695Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded) := by
  have h := atom1695_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1695Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1696 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1696 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1696 = ((g 6) * (g 11) * (g 17)) := by
  norm_num [atom1696, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1696_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121697268184800 : Int) atom1696) := by
  rw [SparsePolynomial.eval_scale, eval_atom1696]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1696Coded : CoefficientMerge.Poly := [(nat_lit 3737, Int.ofNat (nat_lit 1))]
theorem atom1696Coded_decode : atom1696 = SparsePolynomial.decodeCubic 24 atom1696Coded := by decide +kernel
theorem atom1696Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) := by
  have h := atom1696_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1696Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1697 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1697 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1697 = ((g 6) * (g 11) * (g 18)) := by
  norm_num [atom1697, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1697_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142977134375856 : Int) atom1697) := by
  rw [SparsePolynomial.eval_scale, eval_atom1697]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1697Coded : CoefficientMerge.Poly := [(nat_lit 3738, Int.ofNat (nat_lit 1))]
theorem atom1697Coded_decode : atom1697 = SparsePolynomial.decodeCubic 24 atom1697Coded := by decide +kernel
theorem atom1697Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) := by
  have h := atom1697_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1697Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1698 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1698 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1698 = ((g 6) * (g 11) * (g 19)) := by
  norm_num [atom1698, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1698_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164808313021440 : Int) atom1698) := by
  rw [SparsePolynomial.eval_scale, eval_atom1698]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1698Coded : CoefficientMerge.Poly := [(nat_lit 3739, Int.ofNat (nat_lit 1))]
theorem atom1698Coded_decode : atom1698 = SparsePolynomial.decodeCubic 24 atom1698Coded := by decide +kernel
theorem atom1698Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded) := by
  have h := atom1698_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1698Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1699 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1699 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1699 = ((g 6) * (g 11) * (g 20)) := by
  norm_num [atom1699, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1699_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208556285438160 : Int) atom1699) := by
  rw [SparsePolynomial.eval_scale, eval_atom1699]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1699Coded : CoefficientMerge.Poly := [(nat_lit 3740, Int.ofNat (nat_lit 1))]
theorem atom1699Coded_decode : atom1699 = SparsePolynomial.decodeCubic 24 atom1699Coded := by decide +kernel
theorem atom1699Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) := by
  have h := atom1699_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1699Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1700 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1700 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1700 = ((g 6) * (g 11) * (g 21)) := by
  norm_num [atom1700, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1700_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (289029266970840 : Int) atom1700) := by
  rw [SparsePolynomial.eval_scale, eval_atom1700]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1700Coded : CoefficientMerge.Poly := [(nat_lit 3741, Int.ofNat (nat_lit 1))]
theorem atom1700Coded_decode : atom1700 = SparsePolynomial.decodeCubic 24 atom1700Coded := by decide +kernel
theorem atom1700Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded) := by
  have h := atom1700_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1700Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1701 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1701 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1701 = ((g 6) * (g 11) * (g 22)) := by
  norm_num [atom1701, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1701_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379790294156064 : Int) atom1701) := by
  rw [SparsePolynomial.eval_scale, eval_atom1701]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1701Coded : CoefficientMerge.Poly := [(nat_lit 3742, Int.ofNat (nat_lit 1))]
theorem atom1701Coded_decode : atom1701 = SparsePolynomial.decodeCubic 24 atom1701Coded := by decide +kernel
theorem atom1701Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) := by
  have h := atom1701_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1701Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1702 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1702 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1702 = ((g 6) * (g 11) * (g 23)) := by
  norm_num [atom1702, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1702_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (475393062860100 : Int) atom1702) := by
  rw [SparsePolynomial.eval_scale, eval_atom1702]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1702Coded : CoefficientMerge.Poly := [(nat_lit 3743, Int.ofNat (nat_lit 1))]
theorem atom1702Coded_decode : atom1702 = SparsePolynomial.decodeCubic 24 atom1702Coded := by decide +kernel
theorem atom1702Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) := by
  have h := atom1702_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1702Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1703 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1703 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1703 = ((g 6) * (g 12) * (g 12)) := by
  norm_num [atom1703, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1703_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77526953380800 : Int) atom1703) := by
  rw [SparsePolynomial.eval_scale, eval_atom1703]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1703Coded : CoefficientMerge.Poly := [(nat_lit 3756, Int.ofNat (nat_lit 1))]
theorem atom1703Coded_decode : atom1703 = SparsePolynomial.decodeCubic 24 atom1703Coded := by decide +kernel
theorem atom1703Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded) := by
  have h := atom1703_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1703Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1704 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1704 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1704 = ((g 6) * (g 12) * (g 13)) := by
  norm_num [atom1704, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1704_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146429366529600 : Int) atom1704) := by
  rw [SparsePolynomial.eval_scale, eval_atom1704]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1704Coded : CoefficientMerge.Poly := [(nat_lit 3757, Int.ofNat (nat_lit 1))]
theorem atom1704Coded_decode : atom1704 = SparsePolynomial.decodeCubic 24 atom1704Coded := by decide +kernel
theorem atom1704Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) := by
  have h := atom1704_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1704Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1705 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1705 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1705 = ((g 6) * (g 12) * (g 14)) := by
  norm_num [atom1705, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1705_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (149618718849600 : Int) atom1705) := by
  rw [SparsePolynomial.eval_scale, eval_atom1705]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1705Coded : CoefficientMerge.Poly := [(nat_lit 3758, Int.ofNat (nat_lit 1))]
theorem atom1705Coded_decode : atom1705 = SparsePolynomial.decodeCubic 24 atom1705Coded := by decide +kernel
theorem atom1705Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded) := by
  have h := atom1705_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1705Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1706 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1706 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1706 = ((g 6) * (g 12) * (g 15)) := by
  norm_num [atom1706, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1706_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152808071169600 : Int) atom1706) := by
  rw [SparsePolynomial.eval_scale, eval_atom1706]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1706Coded : CoefficientMerge.Poly := [(nat_lit 3759, Int.ofNat (nat_lit 1))]
theorem atom1706Coded_decode : atom1706 = SparsePolynomial.decodeCubic 24 atom1706Coded := by decide +kernel
theorem atom1706Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) := by
  have h := atom1706_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1706Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1707 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1707 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1707 = ((g 6) * (g 12) * (g 16)) := by
  norm_num [atom1707, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1707_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155997423489600 : Int) atom1707) := by
  rw [SparsePolynomial.eval_scale, eval_atom1707]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1707Coded : CoefficientMerge.Poly := [(nat_lit 3760, Int.ofNat (nat_lit 1))]
theorem atom1707Coded_decode : atom1707 = SparsePolynomial.decodeCubic 24 atom1707Coded := by decide +kernel
theorem atom1707Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) := by
  have h := atom1707_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1707Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1708 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1708 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1708 = ((g 6) * (g 12) * (g 17)) := by
  norm_num [atom1708, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1708_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159186775809600 : Int) atom1708) := by
  rw [SparsePolynomial.eval_scale, eval_atom1708]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1708Coded : CoefficientMerge.Poly := [(nat_lit 3761, Int.ofNat (nat_lit 1))]
theorem atom1708Coded_decode : atom1708 = SparsePolynomial.decodeCubic 24 atom1708Coded := by decide +kernel
theorem atom1708Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded) := by
  have h := atom1708_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1708Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1709 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1709 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1709 = ((g 6) * (g 12) * (g 18)) := by
  norm_num [atom1709, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1709_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (219028702232736 : Int) atom1709) := by
  rw [SparsePolynomial.eval_scale, eval_atom1709]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1709Coded : CoefficientMerge.Poly := [(nat_lit 3762, Int.ofNat (nat_lit 1))]
theorem atom1709Coded_decode : atom1709 = SparsePolynomial.decodeCubic 24 atom1709Coded := by decide +kernel
theorem atom1709Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) := by
  have h := atom1709_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1709Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1710 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1710 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1710 = ((g 6) * (g 12) * (g 19)) := by
  norm_num [atom1710, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1710_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218857203671040 : Int) atom1710) := by
  rw [SparsePolynomial.eval_scale, eval_atom1710]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1710Coded : CoefficientMerge.Poly := [(nat_lit 3763, Int.ofNat (nat_lit 1))]
theorem atom1710Coded_decode : atom1710 = SparsePolynomial.decodeCubic 24 atom1710Coded := by decide +kernel
theorem atom1710Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded) := by
  have h := atom1710_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1710Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1711 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1711 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1711 = ((g 6) * (g 12) * (g 20)) := by
  norm_num [atom1711, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1711_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (328731745304160 : Int) atom1711) := by
  rw [SparsePolynomial.eval_scale, eval_atom1711]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1711Coded : CoefficientMerge.Poly := [(nat_lit 3764, Int.ofNat (nat_lit 1))]
theorem atom1711Coded_decode : atom1711 = SparsePolynomial.decodeCubic 24 atom1711Coded := by decide +kernel
theorem atom1711Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) := by
  have h := atom1711_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1711Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1712 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1712 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1712 = ((g 6) * (g 12) * (g 21)) := by
  norm_num [atom1712, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1712_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (342942277922640 : Int) atom1712) := by
  rw [SparsePolynomial.eval_scale, eval_atom1712]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1712Coded : CoefficientMerge.Poly := [(nat_lit 3765, Int.ofNat (nat_lit 1))]
theorem atom1712Coded_decode : atom1712 = SparsePolynomial.decodeCubic 24 atom1712Coded := by decide +kernel
theorem atom1712Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) := by
  have h := atom1712_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1712Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1713 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1713 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1713 = ((g 6) * (g 12) * (g 22)) := by
  norm_num [atom1713, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1713_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (426827127950784 : Int) atom1713) := by
  rw [SparsePolynomial.eval_scale, eval_atom1713]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1713Coded : CoefficientMerge.Poly := [(nat_lit 3766, Int.ofNat (nat_lit 1))]
theorem atom1713Coded_decode : atom1713 = SparsePolynomial.decodeCubic 24 atom1713Coded := by decide +kernel
theorem atom1713Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded) := by
  have h := atom1713_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1713Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1714 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1714 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1714 = ((g 6) * (g 12) * (g 23)) := by
  norm_num [atom1714, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1714_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (511824270295800 : Int) atom1714) := by
  rw [SparsePolynomial.eval_scale, eval_atom1714]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1714Coded : CoefficientMerge.Poly := [(nat_lit 3767, Int.ofNat (nat_lit 1))]
theorem atom1714Coded_decode : atom1714 = SparsePolynomial.decodeCubic 24 atom1714Coded := by decide +kernel
theorem atom1714Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) := by
  have h := atom1714_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1714Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1715 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1715 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1715 = ((g 6) * (g 13) * (g 13)) := by
  norm_num [atom1715, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1715_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103836452227200 : Int) atom1715) := by
  rw [SparsePolynomial.eval_scale, eval_atom1715]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1715Coded : CoefficientMerge.Poly := [(nat_lit 3781, Int.ofNat (nat_lit 1))]
theorem atom1715Coded_decode : atom1715 = SparsePolynomial.decodeCubic 24 atom1715Coded := by decide +kernel
theorem atom1715Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded) := by
  have h := atom1715_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1715Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1716 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1716 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1716 = ((g 6) * (g 13) * (g 14)) := by
  norm_num [atom1716, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1716_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (195494894179200 : Int) atom1716) := by
  rw [SparsePolynomial.eval_scale, eval_atom1716]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1716Coded : CoefficientMerge.Poly := [(nat_lit 3782, Int.ofNat (nat_lit 1))]
theorem atom1716Coded_decode : atom1716 = SparsePolynomial.decodeCubic 24 atom1716Coded := by decide +kernel
theorem atom1716Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) := by
  have h := atom1716_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1716Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1717 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1717 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1717 = ((g 6) * (g 13) * (g 15)) := by
  norm_num [atom1717, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1717_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (192560690044800 : Int) atom1717) := by
  rw [SparsePolynomial.eval_scale, eval_atom1717]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1717Coded : CoefficientMerge.Poly := [(nat_lit 3783, Int.ofNat (nat_lit 1))]
theorem atom1717Coded_decode : atom1717 = SparsePolynomial.decodeCubic 24 atom1717Coded := by decide +kernel
theorem atom1717Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) := by
  have h := atom1717_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1717Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1718 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1718 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1718 = ((g 6) * (g 13) * (g 16)) := by
  norm_num [atom1718, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1718_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (192709526486400 : Int) atom1718) := by
  rw [SparsePolynomial.eval_scale, eval_atom1718]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1718Coded : CoefficientMerge.Poly := [(nat_lit 3784, Int.ofNat (nat_lit 1))]
theorem atom1718Coded_decode : atom1718 = SparsePolynomial.decodeCubic 24 atom1718Coded := by decide +kernel
theorem atom1718Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded) := by
  have h := atom1718_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1718Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1719 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1719 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1719 = ((g 6) * (g 13) * (g 17)) := by
  norm_num [atom1719, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1719_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (192858362928000 : Int) atom1719) := by
  rw [SparsePolynomial.eval_scale, eval_atom1719]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1719Coded : CoefficientMerge.Poly := [(nat_lit 3785, Int.ofNat (nat_lit 1))]
theorem atom1719Coded_decode : atom1719 = SparsePolynomial.decodeCubic 24 atom1719Coded := by decide +kernel
theorem atom1719Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) := by
  have h := atom1719_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1719Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1720 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1720 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1720 = ((g 6) * (g 13) * (g 18)) := by
  norm_num [atom1720, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1720_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241236824875200 : Int) atom1720) := by
  rw [SparsePolynomial.eval_scale, eval_atom1720]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1720Coded : CoefficientMerge.Poly := [(nat_lit 3786, Int.ofNat (nat_lit 1))]
theorem atom1720Coded_decode : atom1720 = SparsePolynomial.decodeCubic 24 atom1720Coded := by decide +kernel
theorem atom1720Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded) := by
  have h := atom1720_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1720Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1721 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1721 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1721 = ((g 6) * (g 13) * (g 19)) := by
  norm_num [atom1721, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1721_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (242826237561600 : Int) atom1721) := by
  rw [SparsePolynomial.eval_scale, eval_atom1721]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1721Coded : CoefficientMerge.Poly := [(nat_lit 3787, Int.ofNat (nat_lit 1))]
theorem atom1721Coded_decode : atom1721 = SparsePolynomial.decodeCubic 24 atom1721Coded := by decide +kernel
theorem atom1721Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) := by
  have h := atom1721_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1721Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1722 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1722 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1722 = ((g 6) * (g 13) * (g 20)) := by
  norm_num [atom1722, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1722_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (356418199368000 : Int) atom1722) := by
  rw [SparsePolynomial.eval_scale, eval_atom1722]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1722Coded : CoefficientMerge.Poly := [(nat_lit 3788, Int.ofNat (nat_lit 1))]
theorem atom1722Coded_decode : atom1722 = SparsePolynomial.decodeCubic 24 atom1722Coded := by decide +kernel
theorem atom1722Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) := by
  have h := atom1722_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1722Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1723 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1723 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1723 = ((g 6) * (g 13) * (g 21)) := by
  norm_num [atom1723, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1723_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (364599695829600 : Int) atom1723) := by
  rw [SparsePolynomial.eval_scale, eval_atom1723]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1723Coded : CoefficientMerge.Poly := [(nat_lit 3789, Int.ofNat (nat_lit 1))]
theorem atom1723Coded_decode : atom1723 = SparsePolynomial.decodeCubic 24 atom1723Coded := by decide +kernel
theorem atom1723Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded) := by
  have h := atom1723_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1723Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1724 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1724 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1724 = ((g 6) * (g 13) * (g 22)) := by
  norm_num [atom1724, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1724_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (450159465571200 : Int) atom1724) := by
  rw [SparsePolynomial.eval_scale, eval_atom1724]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1724Coded : CoefficientMerge.Poly := [(nat_lit 3790, Int.ofNat (nat_lit 1))]
theorem atom1724Coded_decode : atom1724 = SparsePolynomial.decodeCubic 24 atom1724Coded := by decide +kernel
theorem atom1724Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) := by
  have h := atom1724_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1724Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1725 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1725 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1725 = ((g 6) * (g 13) * (g 23)) := by
  norm_num [atom1725, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1725_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (537932773501200 : Int) atom1725) := by
  rw [SparsePolynomial.eval_scale, eval_atom1725]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1725Coded : CoefficientMerge.Poly := [(nat_lit 3791, Int.ofNat (nat_lit 1))]
theorem atom1725Coded_decode : atom1725 = SparsePolynomial.decodeCubic 24 atom1725Coded := by decide +kernel
theorem atom1725Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded) := by
  have h := atom1725_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1725Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1726 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1726 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1726 = ((g 6) * (g 14) * (g 14)) := by
  norm_num [atom1726, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1726_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126592481030400 : Int) atom1726) := by
  rw [SparsePolynomial.eval_scale, eval_atom1726]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1726Coded : CoefficientMerge.Poly := [(nat_lit 3806, Int.ofNat (nat_lit 1))]
theorem atom1726Coded_decode : atom1726 = SparsePolynomial.decodeCubic 24 atom1726Coded := by decide +kernel
theorem atom1726Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) := by
  have h := atom1726_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1726Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1727 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1727 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1727 = ((g 6) * (g 14) * (g 15)) := by
  norm_num [atom1727, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1727_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241054792070400 : Int) atom1727) := by
  rw [SparsePolynomial.eval_scale, eval_atom1727]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1727Coded : CoefficientMerge.Poly := [(nat_lit 3807, Int.ofNat (nat_lit 1))]
theorem atom1727Coded_decode : atom1727 = SparsePolynomial.decodeCubic 24 atom1727Coded := by decide +kernel
theorem atom1727Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) := by
  have h := atom1727_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1727Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1728 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1728 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1728 = ((g 6) * (g 14) * (g 16)) := by
  norm_num [atom1728, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1728_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (237142519891200 : Int) atom1728) := by
  rw [SparsePolynomial.eval_scale, eval_atom1728]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1728Coded : CoefficientMerge.Poly := [(nat_lit 3808, Int.ofNat (nat_lit 1))]
theorem atom1728Coded_decode : atom1728 = SparsePolynomial.decodeCubic 24 atom1728Coded := by decide +kernel
theorem atom1728Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded) := by
  have h := atom1728_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1728Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block023 : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 19897350303600)), (nat_lit 3661, Int.ofNat (nat_lit 5145488409600)), (nat_lit 3662, Int.ofNat (nat_lit 10290976819200)), (nat_lit 3663, Int.ofNat (nat_lit 15436465228800)), (nat_lit 3664, Int.ofNat (nat_lit 20581953638400)), (nat_lit 3665, Int.ofNat (nat_lit 25727442048000)), (nat_lit 3666, Int.ofNat (nat_lit 11587980096000)), (nat_lit 3667, Int.ofNat (nat_lit 19816509081600)), (nat_lit 3668, Int.ofNat (nat_lit 28045038067200)), (nat_lit 3669, Int.ofNat (nat_lit 101836019577600)), (nat_lit 3670, Int.ofNat (nat_lit 175627001088000)), (nat_lit 3671, Int.ofNat (nat_lit 259831217923200)), (nat_lit 3681, Int.ofNat (nat_lit 31293969260400)), (nat_lit 3682, Int.ofNat (nat_lit 43670515451904)), (nat_lit 3683, Int.ofNat (nat_lit 22669871994000)), (nat_lit 3684, Int.ofNat (nat_lit 26794767661200)), (nat_lit 3685, Int.ofNat (nat_lit 29899070586000)), (nat_lit 3686, Int.ofNat (nat_lit 36086414086800)), (nat_lit 3687, Int.ofNat (nat_lit 42273757587600)), (nat_lit 3688, Int.ofNat (nat_lit 48461101088400)), (nat_lit 3689, Int.ofNat (nat_lit 54648444589200)), (nat_lit 3690, Int.ofNat (nat_lit 47823313522248)), (nat_lit 3691, Int.ofNat (nat_lit 65569641223680)), (nat_lit 3692, Int.ofNat (nat_lit 83315968925112)), (nat_lit 3693, Int.ofNat (nat_lit 168997180831380)), (nat_lit 3694, Int.ofNat (nat_lit 254678392737648)), (nat_lit 3695, Int.ofNat (nat_lit 349755587977950)), (nat_lit 3706, Int.ofNat (nat_lit 41144504117904)), (nat_lit 3707, Int.ofNat (nat_lit 68517563369904)), (nat_lit 3708, Int.ofNat (nat_lit 69580680809904)), (nat_lit 3709, Int.ofNat (nat_lit 75789286659504)), (nat_lit 3710, Int.ofNat (nat_lit 81997892509104)), (nat_lit 3711, Int.ofNat (nat_lit 88206498358704)), (nat_lit 3712, Int.ofNat (nat_lit 94415104208304)), (nat_lit 3713, Int.ofNat (nat_lit 100623710057904)), (nat_lit 3714, Int.ofNat (nat_lit 99978636340440)), (nat_lit 3715, Int.ofNat (nat_lit 122637785402880)), (nat_lit 3716, Int.ofNat (nat_lit 145296934465320)), (nat_lit 3717, Int.ofNat (nat_lit 229643480261052)), (nat_lit 3718, Int.ofNat (nat_lit 313990026056784)), (nat_lit 3719, Int.ofNat (nat_lit 405876047439258)), (nat_lit 3731, Int.ofNat (nat_lit 62307098330400)), (nat_lit 3732, Int.ofNat (nat_lit 104900012632800)), (nat_lit 3733, Int.ofNat (nat_lit 107026247512800)), (nat_lit 3734, Int.ofNat (nat_lit 109152482392800)), (nat_lit 3735, Int.ofNat (nat_lit 111278717272800)), (nat_lit 3736, Int.ofNat (nat_lit 116487992728800)), (nat_lit 3737, Int.ofNat (nat_lit 121697268184800)), (nat_lit 3738, Int.ofNat (nat_lit 142977134375856)), (nat_lit 3739, Int.ofNat (nat_lit 164808313021440)), (nat_lit 3740, Int.ofNat (nat_lit 208556285438160)), (nat_lit 3741, Int.ofNat (nat_lit 289029266970840)), (nat_lit 3742, Int.ofNat (nat_lit 379790294156064)), (nat_lit 3743, Int.ofNat (nat_lit 475393062860100)), (nat_lit 3756, Int.ofNat (nat_lit 77526953380800)), (nat_lit 3757, Int.ofNat (nat_lit 146429366529600)), (nat_lit 3758, Int.ofNat (nat_lit 149618718849600)), (nat_lit 3759, Int.ofNat (nat_lit 152808071169600)), (nat_lit 3760, Int.ofNat (nat_lit 155997423489600)), (nat_lit 3761, Int.ofNat (nat_lit 159186775809600)), (nat_lit 3762, Int.ofNat (nat_lit 219028702232736)), (nat_lit 3763, Int.ofNat (nat_lit 218857203671040)), (nat_lit 3764, Int.ofNat (nat_lit 328731745304160)), (nat_lit 3765, Int.ofNat (nat_lit 342942277922640)), (nat_lit 3766, Int.ofNat (nat_lit 426827127950784)), (nat_lit 3767, Int.ofNat (nat_lit 511824270295800)), (nat_lit 3781, Int.ofNat (nat_lit 103836452227200)), (nat_lit 3782, Int.ofNat (nat_lit 195494894179200)), (nat_lit 3783, Int.ofNat (nat_lit 192560690044800)), (nat_lit 3784, Int.ofNat (nat_lit 192709526486400)), (nat_lit 3785, Int.ofNat (nat_lit 192858362928000)), (nat_lit 3786, Int.ofNat (nat_lit 241236824875200)), (nat_lit 3787, Int.ofNat (nat_lit 242826237561600)), (nat_lit 3788, Int.ofNat (nat_lit 356418199368000)), (nat_lit 3789, Int.ofNat (nat_lit 364599695829600)), (nat_lit 3790, Int.ofNat (nat_lit 450159465571200)), (nat_lit 3791, Int.ofNat (nat_lit 537932773501200)), (nat_lit 3806, Int.ofNat (nat_lit 126592481030400)), (nat_lit 3807, Int.ofNat (nat_lit 241054792070400)), (nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
def block023_data_flat000 : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 19897350303600))]
theorem block023_data_flat000_step : block023_data_flat000 = (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) := by decide +kernel
theorem block023_data_flat000_original : block023_data_flat000 = (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) := by
  rw [block023_data_flat000_step]
def block023_data_flat001 : CoefficientMerge.Poly := [(nat_lit 3661, Int.ofNat (nat_lit 5145488409600))]
theorem block023_data_flat001_step : block023_data_flat001 = (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded) := by decide +kernel
theorem block023_data_flat001_original : block023_data_flat001 = (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded) := by
  rw [block023_data_flat001_step]
def block023_data_flat002 : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 19897350303600)), (nat_lit 3661, Int.ofNat (nat_lit 5145488409600))]
theorem block023_data_flat002_step : block023_data_flat002 = (CoefficientMerge.fastMerge block023_data_flat000 block023_data_flat001) := by decide +kernel
theorem block023_data_flat002_original : block023_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded)) := by
  rw [block023_data_flat002_step, block023_data_flat000_original, block023_data_flat001_original]
def block023_data_flat003 : CoefficientMerge.Poly := [(nat_lit 3662, Int.ofNat (nat_lit 10290976819200))]
theorem block023_data_flat003_step : block023_data_flat003 = (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) := by decide +kernel
theorem block023_data_flat003_original : block023_data_flat003 = (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) := by
  rw [block023_data_flat003_step]
def block023_data_flat004 : CoefficientMerge.Poly := [(nat_lit 3663, Int.ofNat (nat_lit 15436465228800))]
theorem block023_data_flat004_step : block023_data_flat004 = (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) := by decide +kernel
theorem block023_data_flat004_original : block023_data_flat004 = (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) := by
  rw [block023_data_flat004_step]
def block023_data_flat005 : CoefficientMerge.Poly := [(nat_lit 3664, Int.ofNat (nat_lit 20581953638400))]
theorem block023_data_flat005_step : block023_data_flat005 = (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded) := by decide +kernel
theorem block023_data_flat005_original : block023_data_flat005 = (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded) := by
  rw [block023_data_flat005_step]
def block023_data_flat006 : CoefficientMerge.Poly := [(nat_lit 3663, Int.ofNat (nat_lit 15436465228800)), (nat_lit 3664, Int.ofNat (nat_lit 20581953638400))]
theorem block023_data_flat006_step : block023_data_flat006 = (CoefficientMerge.fastMerge block023_data_flat004 block023_data_flat005) := by decide +kernel
theorem block023_data_flat006_original : block023_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded)) := by
  rw [block023_data_flat006_step, block023_data_flat004_original, block023_data_flat005_original]
def block023_data_flat007 : CoefficientMerge.Poly := [(nat_lit 3662, Int.ofNat (nat_lit 10290976819200)), (nat_lit 3663, Int.ofNat (nat_lit 15436465228800)), (nat_lit 3664, Int.ofNat (nat_lit 20581953638400))]
theorem block023_data_flat007_step : block023_data_flat007 = (CoefficientMerge.fastMerge block023_data_flat003 block023_data_flat006) := by decide +kernel
theorem block023_data_flat007_original : block023_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded))) := by
  rw [block023_data_flat007_step, block023_data_flat003_original, block023_data_flat006_original]
def block023_data_flat008 : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 19897350303600)), (nat_lit 3661, Int.ofNat (nat_lit 5145488409600)), (nat_lit 3662, Int.ofNat (nat_lit 10290976819200)), (nat_lit 3663, Int.ofNat (nat_lit 15436465228800)), (nat_lit 3664, Int.ofNat (nat_lit 20581953638400))]
theorem block023_data_flat008_step : block023_data_flat008 = (CoefficientMerge.fastMerge block023_data_flat002 block023_data_flat007) := by decide +kernel
theorem block023_data_flat008_original : block023_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded)))) := by
  rw [block023_data_flat008_step, block023_data_flat002_original, block023_data_flat007_original]
def block023_data_flat009 : CoefficientMerge.Poly := [(nat_lit 3665, Int.ofNat (nat_lit 25727442048000))]
theorem block023_data_flat009_step : block023_data_flat009 = (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) := by decide +kernel
theorem block023_data_flat009_original : block023_data_flat009 = (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) := by
  rw [block023_data_flat009_step]
def block023_data_flat010 : CoefficientMerge.Poly := [(nat_lit 3666, Int.ofNat (nat_lit 11587980096000))]
theorem block023_data_flat010_step : block023_data_flat010 = (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded) := by decide +kernel
theorem block023_data_flat010_original : block023_data_flat010 = (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded) := by
  rw [block023_data_flat010_step]
def block023_data_flat011 : CoefficientMerge.Poly := [(nat_lit 3665, Int.ofNat (nat_lit 25727442048000)), (nat_lit 3666, Int.ofNat (nat_lit 11587980096000))]
theorem block023_data_flat011_step : block023_data_flat011 = (CoefficientMerge.fastMerge block023_data_flat009 block023_data_flat010) := by decide +kernel
theorem block023_data_flat011_original : block023_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded)) := by
  rw [block023_data_flat011_step, block023_data_flat009_original, block023_data_flat010_original]
def block023_data_flat012 : CoefficientMerge.Poly := [(nat_lit 3667, Int.ofNat (nat_lit 19816509081600))]
theorem block023_data_flat012_step : block023_data_flat012 = (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) := by decide +kernel
theorem block023_data_flat012_original : block023_data_flat012 = (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) := by
  rw [block023_data_flat012_step]
def block023_data_flat013 : CoefficientMerge.Poly := [(nat_lit 3668, Int.ofNat (nat_lit 28045038067200))]
theorem block023_data_flat013_step : block023_data_flat013 = (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) := by decide +kernel
theorem block023_data_flat013_original : block023_data_flat013 = (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) := by
  rw [block023_data_flat013_step]
def block023_data_flat014 : CoefficientMerge.Poly := [(nat_lit 3669, Int.ofNat (nat_lit 101836019577600))]
theorem block023_data_flat014_step : block023_data_flat014 = (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded) := by decide +kernel
theorem block023_data_flat014_original : block023_data_flat014 = (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded) := by
  rw [block023_data_flat014_step]
def block023_data_flat015 : CoefficientMerge.Poly := [(nat_lit 3668, Int.ofNat (nat_lit 28045038067200)), (nat_lit 3669, Int.ofNat (nat_lit 101836019577600))]
theorem block023_data_flat015_step : block023_data_flat015 = (CoefficientMerge.fastMerge block023_data_flat013 block023_data_flat014) := by decide +kernel
theorem block023_data_flat015_original : block023_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded)) := by
  rw [block023_data_flat015_step, block023_data_flat013_original, block023_data_flat014_original]
def block023_data_flat016 : CoefficientMerge.Poly := [(nat_lit 3667, Int.ofNat (nat_lit 19816509081600)), (nat_lit 3668, Int.ofNat (nat_lit 28045038067200)), (nat_lit 3669, Int.ofNat (nat_lit 101836019577600))]
theorem block023_data_flat016_step : block023_data_flat016 = (CoefficientMerge.fastMerge block023_data_flat012 block023_data_flat015) := by decide +kernel
theorem block023_data_flat016_original : block023_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded))) := by
  rw [block023_data_flat016_step, block023_data_flat012_original, block023_data_flat015_original]
def block023_data_flat017 : CoefficientMerge.Poly := [(nat_lit 3665, Int.ofNat (nat_lit 25727442048000)), (nat_lit 3666, Int.ofNat (nat_lit 11587980096000)), (nat_lit 3667, Int.ofNat (nat_lit 19816509081600)), (nat_lit 3668, Int.ofNat (nat_lit 28045038067200)), (nat_lit 3669, Int.ofNat (nat_lit 101836019577600))]
theorem block023_data_flat017_step : block023_data_flat017 = (CoefficientMerge.fastMerge block023_data_flat011 block023_data_flat016) := by decide +kernel
theorem block023_data_flat017_original : block023_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded)))) := by
  rw [block023_data_flat017_step, block023_data_flat011_original, block023_data_flat016_original]
def block023_data_flat018 : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 19897350303600)), (nat_lit 3661, Int.ofNat (nat_lit 5145488409600)), (nat_lit 3662, Int.ofNat (nat_lit 10290976819200)), (nat_lit 3663, Int.ofNat (nat_lit 15436465228800)), (nat_lit 3664, Int.ofNat (nat_lit 20581953638400)), (nat_lit 3665, Int.ofNat (nat_lit 25727442048000)), (nat_lit 3666, Int.ofNat (nat_lit 11587980096000)), (nat_lit 3667, Int.ofNat (nat_lit 19816509081600)), (nat_lit 3668, Int.ofNat (nat_lit 28045038067200)), (nat_lit 3669, Int.ofNat (nat_lit 101836019577600))]
theorem block023_data_flat018_step : block023_data_flat018 = (CoefficientMerge.fastMerge block023_data_flat008 block023_data_flat017) := by decide +kernel
theorem block023_data_flat018_original : block023_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded))))) := by
  rw [block023_data_flat018_step, block023_data_flat008_original, block023_data_flat017_original]
def block023_data_flat019 : CoefficientMerge.Poly := [(nat_lit 3670, Int.ofNat (nat_lit 175627001088000))]
theorem block023_data_flat019_step : block023_data_flat019 = (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) := by decide +kernel
theorem block023_data_flat019_original : block023_data_flat019 = (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) := by
  rw [block023_data_flat019_step]
def block023_data_flat020 : CoefficientMerge.Poly := [(nat_lit 3671, Int.ofNat (nat_lit 259831217923200))]
theorem block023_data_flat020_step : block023_data_flat020 = (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded) := by decide +kernel
theorem block023_data_flat020_original : block023_data_flat020 = (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded) := by
  rw [block023_data_flat020_step]
def block023_data_flat021 : CoefficientMerge.Poly := [(nat_lit 3670, Int.ofNat (nat_lit 175627001088000)), (nat_lit 3671, Int.ofNat (nat_lit 259831217923200))]
theorem block023_data_flat021_step : block023_data_flat021 = (CoefficientMerge.fastMerge block023_data_flat019 block023_data_flat020) := by decide +kernel
theorem block023_data_flat021_original : block023_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded)) := by
  rw [block023_data_flat021_step, block023_data_flat019_original, block023_data_flat020_original]
def block023_data_flat022 : CoefficientMerge.Poly := [(nat_lit 3681, Int.ofNat (nat_lit 31293969260400))]
theorem block023_data_flat022_step : block023_data_flat022 = (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) := by decide +kernel
theorem block023_data_flat022_original : block023_data_flat022 = (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) := by
  rw [block023_data_flat022_step]
def block023_data_flat023 : CoefficientMerge.Poly := [(nat_lit 3682, Int.ofNat (nat_lit 43670515451904))]
theorem block023_data_flat023_step : block023_data_flat023 = (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) := by decide +kernel
theorem block023_data_flat023_original : block023_data_flat023 = (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) := by
  rw [block023_data_flat023_step]
def block023_data_flat024 : CoefficientMerge.Poly := [(nat_lit 3683, Int.ofNat (nat_lit 22669871994000))]
theorem block023_data_flat024_step : block023_data_flat024 = (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded) := by decide +kernel
theorem block023_data_flat024_original : block023_data_flat024 = (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded) := by
  rw [block023_data_flat024_step]
def block023_data_flat025 : CoefficientMerge.Poly := [(nat_lit 3682, Int.ofNat (nat_lit 43670515451904)), (nat_lit 3683, Int.ofNat (nat_lit 22669871994000))]
theorem block023_data_flat025_step : block023_data_flat025 = (CoefficientMerge.fastMerge block023_data_flat023 block023_data_flat024) := by decide +kernel
theorem block023_data_flat025_original : block023_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded)) := by
  rw [block023_data_flat025_step, block023_data_flat023_original, block023_data_flat024_original]
def block023_data_flat026 : CoefficientMerge.Poly := [(nat_lit 3681, Int.ofNat (nat_lit 31293969260400)), (nat_lit 3682, Int.ofNat (nat_lit 43670515451904)), (nat_lit 3683, Int.ofNat (nat_lit 22669871994000))]
theorem block023_data_flat026_step : block023_data_flat026 = (CoefficientMerge.fastMerge block023_data_flat022 block023_data_flat025) := by decide +kernel
theorem block023_data_flat026_original : block023_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded))) := by
  rw [block023_data_flat026_step, block023_data_flat022_original, block023_data_flat025_original]
def block023_data_flat027 : CoefficientMerge.Poly := [(nat_lit 3670, Int.ofNat (nat_lit 175627001088000)), (nat_lit 3671, Int.ofNat (nat_lit 259831217923200)), (nat_lit 3681, Int.ofNat (nat_lit 31293969260400)), (nat_lit 3682, Int.ofNat (nat_lit 43670515451904)), (nat_lit 3683, Int.ofNat (nat_lit 22669871994000))]
theorem block023_data_flat027_step : block023_data_flat027 = (CoefficientMerge.fastMerge block023_data_flat021 block023_data_flat026) := by decide +kernel
theorem block023_data_flat027_original : block023_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded)))) := by
  rw [block023_data_flat027_step, block023_data_flat021_original, block023_data_flat026_original]
def block023_data_flat028 : CoefficientMerge.Poly := [(nat_lit 3684, Int.ofNat (nat_lit 26794767661200))]
theorem block023_data_flat028_step : block023_data_flat028 = (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) := by decide +kernel
theorem block023_data_flat028_original : block023_data_flat028 = (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) := by
  rw [block023_data_flat028_step]
def block023_data_flat029 : CoefficientMerge.Poly := [(nat_lit 3685, Int.ofNat (nat_lit 29899070586000))]
theorem block023_data_flat029_step : block023_data_flat029 = (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded) := by decide +kernel
theorem block023_data_flat029_original : block023_data_flat029 = (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded) := by
  rw [block023_data_flat029_step]
def block023_data_flat030 : CoefficientMerge.Poly := [(nat_lit 3684, Int.ofNat (nat_lit 26794767661200)), (nat_lit 3685, Int.ofNat (nat_lit 29899070586000))]
theorem block023_data_flat030_step : block023_data_flat030 = (CoefficientMerge.fastMerge block023_data_flat028 block023_data_flat029) := by decide +kernel
theorem block023_data_flat030_original : block023_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded)) := by
  rw [block023_data_flat030_step, block023_data_flat028_original, block023_data_flat029_original]
def block023_data_flat031 : CoefficientMerge.Poly := [(nat_lit 3686, Int.ofNat (nat_lit 36086414086800))]
theorem block023_data_flat031_step : block023_data_flat031 = (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) := by decide +kernel
theorem block023_data_flat031_original : block023_data_flat031 = (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) := by
  rw [block023_data_flat031_step]
def block023_data_flat032 : CoefficientMerge.Poly := [(nat_lit 3687, Int.ofNat (nat_lit 42273757587600))]
theorem block023_data_flat032_step : block023_data_flat032 = (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) := by decide +kernel
theorem block023_data_flat032_original : block023_data_flat032 = (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) := by
  rw [block023_data_flat032_step]
def block023_data_flat033 : CoefficientMerge.Poly := [(nat_lit 3688, Int.ofNat (nat_lit 48461101088400))]
theorem block023_data_flat033_step : block023_data_flat033 = (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded) := by decide +kernel
theorem block023_data_flat033_original : block023_data_flat033 = (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded) := by
  rw [block023_data_flat033_step]
def block023_data_flat034 : CoefficientMerge.Poly := [(nat_lit 3687, Int.ofNat (nat_lit 42273757587600)), (nat_lit 3688, Int.ofNat (nat_lit 48461101088400))]
theorem block023_data_flat034_step : block023_data_flat034 = (CoefficientMerge.fastMerge block023_data_flat032 block023_data_flat033) := by decide +kernel
theorem block023_data_flat034_original : block023_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded)) := by
  rw [block023_data_flat034_step, block023_data_flat032_original, block023_data_flat033_original]
def block023_data_flat035 : CoefficientMerge.Poly := [(nat_lit 3686, Int.ofNat (nat_lit 36086414086800)), (nat_lit 3687, Int.ofNat (nat_lit 42273757587600)), (nat_lit 3688, Int.ofNat (nat_lit 48461101088400))]
theorem block023_data_flat035_step : block023_data_flat035 = (CoefficientMerge.fastMerge block023_data_flat031 block023_data_flat034) := by decide +kernel
theorem block023_data_flat035_original : block023_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded))) := by
  rw [block023_data_flat035_step, block023_data_flat031_original, block023_data_flat034_original]
def block023_data_flat036 : CoefficientMerge.Poly := [(nat_lit 3684, Int.ofNat (nat_lit 26794767661200)), (nat_lit 3685, Int.ofNat (nat_lit 29899070586000)), (nat_lit 3686, Int.ofNat (nat_lit 36086414086800)), (nat_lit 3687, Int.ofNat (nat_lit 42273757587600)), (nat_lit 3688, Int.ofNat (nat_lit 48461101088400))]
theorem block023_data_flat036_step : block023_data_flat036 = (CoefficientMerge.fastMerge block023_data_flat030 block023_data_flat035) := by decide +kernel
theorem block023_data_flat036_original : block023_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded)))) := by
  rw [block023_data_flat036_step, block023_data_flat030_original, block023_data_flat035_original]
def block023_data_flat037 : CoefficientMerge.Poly := [(nat_lit 3670, Int.ofNat (nat_lit 175627001088000)), (nat_lit 3671, Int.ofNat (nat_lit 259831217923200)), (nat_lit 3681, Int.ofNat (nat_lit 31293969260400)), (nat_lit 3682, Int.ofNat (nat_lit 43670515451904)), (nat_lit 3683, Int.ofNat (nat_lit 22669871994000)), (nat_lit 3684, Int.ofNat (nat_lit 26794767661200)), (nat_lit 3685, Int.ofNat (nat_lit 29899070586000)), (nat_lit 3686, Int.ofNat (nat_lit 36086414086800)), (nat_lit 3687, Int.ofNat (nat_lit 42273757587600)), (nat_lit 3688, Int.ofNat (nat_lit 48461101088400))]
theorem block023_data_flat037_step : block023_data_flat037 = (CoefficientMerge.fastMerge block023_data_flat027 block023_data_flat036) := by decide +kernel
theorem block023_data_flat037_original : block023_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded))))) := by
  rw [block023_data_flat037_step, block023_data_flat027_original, block023_data_flat036_original]
def block023_data_flat038 : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 19897350303600)), (nat_lit 3661, Int.ofNat (nat_lit 5145488409600)), (nat_lit 3662, Int.ofNat (nat_lit 10290976819200)), (nat_lit 3663, Int.ofNat (nat_lit 15436465228800)), (nat_lit 3664, Int.ofNat (nat_lit 20581953638400)), (nat_lit 3665, Int.ofNat (nat_lit 25727442048000)), (nat_lit 3666, Int.ofNat (nat_lit 11587980096000)), (nat_lit 3667, Int.ofNat (nat_lit 19816509081600)), (nat_lit 3668, Int.ofNat (nat_lit 28045038067200)), (nat_lit 3669, Int.ofNat (nat_lit 101836019577600)), (nat_lit 3670, Int.ofNat (nat_lit 175627001088000)), (nat_lit 3671, Int.ofNat (nat_lit 259831217923200)), (nat_lit 3681, Int.ofNat (nat_lit 31293969260400)), (nat_lit 3682, Int.ofNat (nat_lit 43670515451904)), (nat_lit 3683, Int.ofNat (nat_lit 22669871994000)), (nat_lit 3684, Int.ofNat (nat_lit 26794767661200)), (nat_lit 3685, Int.ofNat (nat_lit 29899070586000)), (nat_lit 3686, Int.ofNat (nat_lit 36086414086800)), (nat_lit 3687, Int.ofNat (nat_lit 42273757587600)), (nat_lit 3688, Int.ofNat (nat_lit 48461101088400))]
theorem block023_data_flat038_step : block023_data_flat038 = (CoefficientMerge.fastMerge block023_data_flat018 block023_data_flat037) := by decide +kernel
theorem block023_data_flat038_original : block023_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded)))))) := by
  rw [block023_data_flat038_step, block023_data_flat018_original, block023_data_flat037_original]
def block023_data_flat039 : CoefficientMerge.Poly := [(nat_lit 3689, Int.ofNat (nat_lit 54648444589200))]
theorem block023_data_flat039_step : block023_data_flat039 = (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) := by decide +kernel
theorem block023_data_flat039_original : block023_data_flat039 = (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) := by
  rw [block023_data_flat039_step]
def block023_data_flat040 : CoefficientMerge.Poly := [(nat_lit 3690, Int.ofNat (nat_lit 47823313522248))]
theorem block023_data_flat040_step : block023_data_flat040 = (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded) := by decide +kernel
theorem block023_data_flat040_original : block023_data_flat040 = (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded) := by
  rw [block023_data_flat040_step]
def block023_data_flat041 : CoefficientMerge.Poly := [(nat_lit 3689, Int.ofNat (nat_lit 54648444589200)), (nat_lit 3690, Int.ofNat (nat_lit 47823313522248))]
theorem block023_data_flat041_step : block023_data_flat041 = (CoefficientMerge.fastMerge block023_data_flat039 block023_data_flat040) := by decide +kernel
theorem block023_data_flat041_original : block023_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded)) := by
  rw [block023_data_flat041_step, block023_data_flat039_original, block023_data_flat040_original]
def block023_data_flat042 : CoefficientMerge.Poly := [(nat_lit 3691, Int.ofNat (nat_lit 65569641223680))]
theorem block023_data_flat042_step : block023_data_flat042 = (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) := by decide +kernel
theorem block023_data_flat042_original : block023_data_flat042 = (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) := by
  rw [block023_data_flat042_step]
def block023_data_flat043 : CoefficientMerge.Poly := [(nat_lit 3692, Int.ofNat (nat_lit 83315968925112))]
theorem block023_data_flat043_step : block023_data_flat043 = (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) := by decide +kernel
theorem block023_data_flat043_original : block023_data_flat043 = (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) := by
  rw [block023_data_flat043_step]
def block023_data_flat044 : CoefficientMerge.Poly := [(nat_lit 3693, Int.ofNat (nat_lit 168997180831380))]
theorem block023_data_flat044_step : block023_data_flat044 = (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded) := by decide +kernel
theorem block023_data_flat044_original : block023_data_flat044 = (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded) := by
  rw [block023_data_flat044_step]
def block023_data_flat045 : CoefficientMerge.Poly := [(nat_lit 3692, Int.ofNat (nat_lit 83315968925112)), (nat_lit 3693, Int.ofNat (nat_lit 168997180831380))]
theorem block023_data_flat045_step : block023_data_flat045 = (CoefficientMerge.fastMerge block023_data_flat043 block023_data_flat044) := by decide +kernel
theorem block023_data_flat045_original : block023_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded)) := by
  rw [block023_data_flat045_step, block023_data_flat043_original, block023_data_flat044_original]
def block023_data_flat046 : CoefficientMerge.Poly := [(nat_lit 3691, Int.ofNat (nat_lit 65569641223680)), (nat_lit 3692, Int.ofNat (nat_lit 83315968925112)), (nat_lit 3693, Int.ofNat (nat_lit 168997180831380))]
theorem block023_data_flat046_step : block023_data_flat046 = (CoefficientMerge.fastMerge block023_data_flat042 block023_data_flat045) := by decide +kernel
theorem block023_data_flat046_original : block023_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded))) := by
  rw [block023_data_flat046_step, block023_data_flat042_original, block023_data_flat045_original]
def block023_data_flat047 : CoefficientMerge.Poly := [(nat_lit 3689, Int.ofNat (nat_lit 54648444589200)), (nat_lit 3690, Int.ofNat (nat_lit 47823313522248)), (nat_lit 3691, Int.ofNat (nat_lit 65569641223680)), (nat_lit 3692, Int.ofNat (nat_lit 83315968925112)), (nat_lit 3693, Int.ofNat (nat_lit 168997180831380))]
theorem block023_data_flat047_step : block023_data_flat047 = (CoefficientMerge.fastMerge block023_data_flat041 block023_data_flat046) := by decide +kernel
theorem block023_data_flat047_original : block023_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded)))) := by
  rw [block023_data_flat047_step, block023_data_flat041_original, block023_data_flat046_original]
def block023_data_flat048 : CoefficientMerge.Poly := [(nat_lit 3694, Int.ofNat (nat_lit 254678392737648))]
theorem block023_data_flat048_step : block023_data_flat048 = (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) := by decide +kernel
theorem block023_data_flat048_original : block023_data_flat048 = (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) := by
  rw [block023_data_flat048_step]
def block023_data_flat049 : CoefficientMerge.Poly := [(nat_lit 3695, Int.ofNat (nat_lit 349755587977950))]
theorem block023_data_flat049_step : block023_data_flat049 = (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded) := by decide +kernel
theorem block023_data_flat049_original : block023_data_flat049 = (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded) := by
  rw [block023_data_flat049_step]
def block023_data_flat050 : CoefficientMerge.Poly := [(nat_lit 3694, Int.ofNat (nat_lit 254678392737648)), (nat_lit 3695, Int.ofNat (nat_lit 349755587977950))]
theorem block023_data_flat050_step : block023_data_flat050 = (CoefficientMerge.fastMerge block023_data_flat048 block023_data_flat049) := by decide +kernel
theorem block023_data_flat050_original : block023_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded)) := by
  rw [block023_data_flat050_step, block023_data_flat048_original, block023_data_flat049_original]
def block023_data_flat051 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 41144504117904))]
theorem block023_data_flat051_step : block023_data_flat051 = (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) := by decide +kernel
theorem block023_data_flat051_original : block023_data_flat051 = (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) := by
  rw [block023_data_flat051_step]
def block023_data_flat052 : CoefficientMerge.Poly := [(nat_lit 3707, Int.ofNat (nat_lit 68517563369904))]
theorem block023_data_flat052_step : block023_data_flat052 = (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) := by decide +kernel
theorem block023_data_flat052_original : block023_data_flat052 = (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) := by
  rw [block023_data_flat052_step]
def block023_data_flat053 : CoefficientMerge.Poly := [(nat_lit 3708, Int.ofNat (nat_lit 69580680809904))]
theorem block023_data_flat053_step : block023_data_flat053 = (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded) := by decide +kernel
theorem block023_data_flat053_original : block023_data_flat053 = (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded) := by
  rw [block023_data_flat053_step]
def block023_data_flat054 : CoefficientMerge.Poly := [(nat_lit 3707, Int.ofNat (nat_lit 68517563369904)), (nat_lit 3708, Int.ofNat (nat_lit 69580680809904))]
theorem block023_data_flat054_step : block023_data_flat054 = (CoefficientMerge.fastMerge block023_data_flat052 block023_data_flat053) := by decide +kernel
theorem block023_data_flat054_original : block023_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded)) := by
  rw [block023_data_flat054_step, block023_data_flat052_original, block023_data_flat053_original]
def block023_data_flat055 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 41144504117904)), (nat_lit 3707, Int.ofNat (nat_lit 68517563369904)), (nat_lit 3708, Int.ofNat (nat_lit 69580680809904))]
theorem block023_data_flat055_step : block023_data_flat055 = (CoefficientMerge.fastMerge block023_data_flat051 block023_data_flat054) := by decide +kernel
theorem block023_data_flat055_original : block023_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded))) := by
  rw [block023_data_flat055_step, block023_data_flat051_original, block023_data_flat054_original]
def block023_data_flat056 : CoefficientMerge.Poly := [(nat_lit 3694, Int.ofNat (nat_lit 254678392737648)), (nat_lit 3695, Int.ofNat (nat_lit 349755587977950)), (nat_lit 3706, Int.ofNat (nat_lit 41144504117904)), (nat_lit 3707, Int.ofNat (nat_lit 68517563369904)), (nat_lit 3708, Int.ofNat (nat_lit 69580680809904))]
theorem block023_data_flat056_step : block023_data_flat056 = (CoefficientMerge.fastMerge block023_data_flat050 block023_data_flat055) := by decide +kernel
theorem block023_data_flat056_original : block023_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded)))) := by
  rw [block023_data_flat056_step, block023_data_flat050_original, block023_data_flat055_original]
def block023_data_flat057 : CoefficientMerge.Poly := [(nat_lit 3689, Int.ofNat (nat_lit 54648444589200)), (nat_lit 3690, Int.ofNat (nat_lit 47823313522248)), (nat_lit 3691, Int.ofNat (nat_lit 65569641223680)), (nat_lit 3692, Int.ofNat (nat_lit 83315968925112)), (nat_lit 3693, Int.ofNat (nat_lit 168997180831380)), (nat_lit 3694, Int.ofNat (nat_lit 254678392737648)), (nat_lit 3695, Int.ofNat (nat_lit 349755587977950)), (nat_lit 3706, Int.ofNat (nat_lit 41144504117904)), (nat_lit 3707, Int.ofNat (nat_lit 68517563369904)), (nat_lit 3708, Int.ofNat (nat_lit 69580680809904))]
theorem block023_data_flat057_step : block023_data_flat057 = (CoefficientMerge.fastMerge block023_data_flat047 block023_data_flat056) := by decide +kernel
theorem block023_data_flat057_original : block023_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded))))) := by
  rw [block023_data_flat057_step, block023_data_flat047_original, block023_data_flat056_original]
def block023_data_flat058 : CoefficientMerge.Poly := [(nat_lit 3709, Int.ofNat (nat_lit 75789286659504))]
theorem block023_data_flat058_step : block023_data_flat058 = (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) := by decide +kernel
theorem block023_data_flat058_original : block023_data_flat058 = (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) := by
  rw [block023_data_flat058_step]
def block023_data_flat059 : CoefficientMerge.Poly := [(nat_lit 3710, Int.ofNat (nat_lit 81997892509104))]
theorem block023_data_flat059_step : block023_data_flat059 = (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded) := by decide +kernel
theorem block023_data_flat059_original : block023_data_flat059 = (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded) := by
  rw [block023_data_flat059_step]
def block023_data_flat060 : CoefficientMerge.Poly := [(nat_lit 3709, Int.ofNat (nat_lit 75789286659504)), (nat_lit 3710, Int.ofNat (nat_lit 81997892509104))]
theorem block023_data_flat060_step : block023_data_flat060 = (CoefficientMerge.fastMerge block023_data_flat058 block023_data_flat059) := by decide +kernel
theorem block023_data_flat060_original : block023_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded)) := by
  rw [block023_data_flat060_step, block023_data_flat058_original, block023_data_flat059_original]
def block023_data_flat061 : CoefficientMerge.Poly := [(nat_lit 3711, Int.ofNat (nat_lit 88206498358704))]
theorem block023_data_flat061_step : block023_data_flat061 = (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) := by decide +kernel
theorem block023_data_flat061_original : block023_data_flat061 = (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) := by
  rw [block023_data_flat061_step]
def block023_data_flat062 : CoefficientMerge.Poly := [(nat_lit 3712, Int.ofNat (nat_lit 94415104208304))]
theorem block023_data_flat062_step : block023_data_flat062 = (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) := by decide +kernel
theorem block023_data_flat062_original : block023_data_flat062 = (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) := by
  rw [block023_data_flat062_step]
def block023_data_flat063 : CoefficientMerge.Poly := [(nat_lit 3713, Int.ofNat (nat_lit 100623710057904))]
theorem block023_data_flat063_step : block023_data_flat063 = (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded) := by decide +kernel
theorem block023_data_flat063_original : block023_data_flat063 = (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded) := by
  rw [block023_data_flat063_step]
def block023_data_flat064 : CoefficientMerge.Poly := [(nat_lit 3712, Int.ofNat (nat_lit 94415104208304)), (nat_lit 3713, Int.ofNat (nat_lit 100623710057904))]
theorem block023_data_flat064_step : block023_data_flat064 = (CoefficientMerge.fastMerge block023_data_flat062 block023_data_flat063) := by decide +kernel
theorem block023_data_flat064_original : block023_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded)) := by
  rw [block023_data_flat064_step, block023_data_flat062_original, block023_data_flat063_original]
def block023_data_flat065 : CoefficientMerge.Poly := [(nat_lit 3711, Int.ofNat (nat_lit 88206498358704)), (nat_lit 3712, Int.ofNat (nat_lit 94415104208304)), (nat_lit 3713, Int.ofNat (nat_lit 100623710057904))]
theorem block023_data_flat065_step : block023_data_flat065 = (CoefficientMerge.fastMerge block023_data_flat061 block023_data_flat064) := by decide +kernel
theorem block023_data_flat065_original : block023_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded))) := by
  rw [block023_data_flat065_step, block023_data_flat061_original, block023_data_flat064_original]
def block023_data_flat066 : CoefficientMerge.Poly := [(nat_lit 3709, Int.ofNat (nat_lit 75789286659504)), (nat_lit 3710, Int.ofNat (nat_lit 81997892509104)), (nat_lit 3711, Int.ofNat (nat_lit 88206498358704)), (nat_lit 3712, Int.ofNat (nat_lit 94415104208304)), (nat_lit 3713, Int.ofNat (nat_lit 100623710057904))]
theorem block023_data_flat066_step : block023_data_flat066 = (CoefficientMerge.fastMerge block023_data_flat060 block023_data_flat065) := by decide +kernel
theorem block023_data_flat066_original : block023_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded)))) := by
  rw [block023_data_flat066_step, block023_data_flat060_original, block023_data_flat065_original]
def block023_data_flat067 : CoefficientMerge.Poly := [(nat_lit 3714, Int.ofNat (nat_lit 99978636340440))]
theorem block023_data_flat067_step : block023_data_flat067 = (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) := by decide +kernel
theorem block023_data_flat067_original : block023_data_flat067 = (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) := by
  rw [block023_data_flat067_step]
def block023_data_flat068 : CoefficientMerge.Poly := [(nat_lit 3715, Int.ofNat (nat_lit 122637785402880))]
theorem block023_data_flat068_step : block023_data_flat068 = (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded) := by decide +kernel
theorem block023_data_flat068_original : block023_data_flat068 = (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded) := by
  rw [block023_data_flat068_step]
def block023_data_flat069 : CoefficientMerge.Poly := [(nat_lit 3714, Int.ofNat (nat_lit 99978636340440)), (nat_lit 3715, Int.ofNat (nat_lit 122637785402880))]
theorem block023_data_flat069_step : block023_data_flat069 = (CoefficientMerge.fastMerge block023_data_flat067 block023_data_flat068) := by decide +kernel
theorem block023_data_flat069_original : block023_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded)) := by
  rw [block023_data_flat069_step, block023_data_flat067_original, block023_data_flat068_original]
def block023_data_flat070 : CoefficientMerge.Poly := [(nat_lit 3716, Int.ofNat (nat_lit 145296934465320))]
theorem block023_data_flat070_step : block023_data_flat070 = (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) := by decide +kernel
theorem block023_data_flat070_original : block023_data_flat070 = (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) := by
  rw [block023_data_flat070_step]
def block023_data_flat071 : CoefficientMerge.Poly := [(nat_lit 3717, Int.ofNat (nat_lit 229643480261052))]
theorem block023_data_flat071_step : block023_data_flat071 = (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) := by decide +kernel
theorem block023_data_flat071_original : block023_data_flat071 = (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) := by
  rw [block023_data_flat071_step]
def block023_data_flat072 : CoefficientMerge.Poly := [(nat_lit 3718, Int.ofNat (nat_lit 313990026056784))]
theorem block023_data_flat072_step : block023_data_flat072 = (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded) := by decide +kernel
theorem block023_data_flat072_original : block023_data_flat072 = (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded) := by
  rw [block023_data_flat072_step]
def block023_data_flat073 : CoefficientMerge.Poly := [(nat_lit 3717, Int.ofNat (nat_lit 229643480261052)), (nat_lit 3718, Int.ofNat (nat_lit 313990026056784))]
theorem block023_data_flat073_step : block023_data_flat073 = (CoefficientMerge.fastMerge block023_data_flat071 block023_data_flat072) := by decide +kernel
theorem block023_data_flat073_original : block023_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded)) := by
  rw [block023_data_flat073_step, block023_data_flat071_original, block023_data_flat072_original]
def block023_data_flat074 : CoefficientMerge.Poly := [(nat_lit 3716, Int.ofNat (nat_lit 145296934465320)), (nat_lit 3717, Int.ofNat (nat_lit 229643480261052)), (nat_lit 3718, Int.ofNat (nat_lit 313990026056784))]
theorem block023_data_flat074_step : block023_data_flat074 = (CoefficientMerge.fastMerge block023_data_flat070 block023_data_flat073) := by decide +kernel
theorem block023_data_flat074_original : block023_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded))) := by
  rw [block023_data_flat074_step, block023_data_flat070_original, block023_data_flat073_original]
def block023_data_flat075 : CoefficientMerge.Poly := [(nat_lit 3714, Int.ofNat (nat_lit 99978636340440)), (nat_lit 3715, Int.ofNat (nat_lit 122637785402880)), (nat_lit 3716, Int.ofNat (nat_lit 145296934465320)), (nat_lit 3717, Int.ofNat (nat_lit 229643480261052)), (nat_lit 3718, Int.ofNat (nat_lit 313990026056784))]
theorem block023_data_flat075_step : block023_data_flat075 = (CoefficientMerge.fastMerge block023_data_flat069 block023_data_flat074) := by decide +kernel
theorem block023_data_flat075_original : block023_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded)))) := by
  rw [block023_data_flat075_step, block023_data_flat069_original, block023_data_flat074_original]
def block023_data_flat076 : CoefficientMerge.Poly := [(nat_lit 3709, Int.ofNat (nat_lit 75789286659504)), (nat_lit 3710, Int.ofNat (nat_lit 81997892509104)), (nat_lit 3711, Int.ofNat (nat_lit 88206498358704)), (nat_lit 3712, Int.ofNat (nat_lit 94415104208304)), (nat_lit 3713, Int.ofNat (nat_lit 100623710057904)), (nat_lit 3714, Int.ofNat (nat_lit 99978636340440)), (nat_lit 3715, Int.ofNat (nat_lit 122637785402880)), (nat_lit 3716, Int.ofNat (nat_lit 145296934465320)), (nat_lit 3717, Int.ofNat (nat_lit 229643480261052)), (nat_lit 3718, Int.ofNat (nat_lit 313990026056784))]
theorem block023_data_flat076_step : block023_data_flat076 = (CoefficientMerge.fastMerge block023_data_flat066 block023_data_flat075) := by decide +kernel
theorem block023_data_flat076_original : block023_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded))))) := by
  rw [block023_data_flat076_step, block023_data_flat066_original, block023_data_flat075_original]
def block023_data_flat077 : CoefficientMerge.Poly := [(nat_lit 3689, Int.ofNat (nat_lit 54648444589200)), (nat_lit 3690, Int.ofNat (nat_lit 47823313522248)), (nat_lit 3691, Int.ofNat (nat_lit 65569641223680)), (nat_lit 3692, Int.ofNat (nat_lit 83315968925112)), (nat_lit 3693, Int.ofNat (nat_lit 168997180831380)), (nat_lit 3694, Int.ofNat (nat_lit 254678392737648)), (nat_lit 3695, Int.ofNat (nat_lit 349755587977950)), (nat_lit 3706, Int.ofNat (nat_lit 41144504117904)), (nat_lit 3707, Int.ofNat (nat_lit 68517563369904)), (nat_lit 3708, Int.ofNat (nat_lit 69580680809904)), (nat_lit 3709, Int.ofNat (nat_lit 75789286659504)), (nat_lit 3710, Int.ofNat (nat_lit 81997892509104)), (nat_lit 3711, Int.ofNat (nat_lit 88206498358704)), (nat_lit 3712, Int.ofNat (nat_lit 94415104208304)), (nat_lit 3713, Int.ofNat (nat_lit 100623710057904)), (nat_lit 3714, Int.ofNat (nat_lit 99978636340440)), (nat_lit 3715, Int.ofNat (nat_lit 122637785402880)), (nat_lit 3716, Int.ofNat (nat_lit 145296934465320)), (nat_lit 3717, Int.ofNat (nat_lit 229643480261052)), (nat_lit 3718, Int.ofNat (nat_lit 313990026056784))]
theorem block023_data_flat077_step : block023_data_flat077 = (CoefficientMerge.fastMerge block023_data_flat057 block023_data_flat076) := by decide +kernel
theorem block023_data_flat077_original : block023_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded)))))) := by
  rw [block023_data_flat077_step, block023_data_flat057_original, block023_data_flat076_original]
def block023_data_flat078 : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 19897350303600)), (nat_lit 3661, Int.ofNat (nat_lit 5145488409600)), (nat_lit 3662, Int.ofNat (nat_lit 10290976819200)), (nat_lit 3663, Int.ofNat (nat_lit 15436465228800)), (nat_lit 3664, Int.ofNat (nat_lit 20581953638400)), (nat_lit 3665, Int.ofNat (nat_lit 25727442048000)), (nat_lit 3666, Int.ofNat (nat_lit 11587980096000)), (nat_lit 3667, Int.ofNat (nat_lit 19816509081600)), (nat_lit 3668, Int.ofNat (nat_lit 28045038067200)), (nat_lit 3669, Int.ofNat (nat_lit 101836019577600)), (nat_lit 3670, Int.ofNat (nat_lit 175627001088000)), (nat_lit 3671, Int.ofNat (nat_lit 259831217923200)), (nat_lit 3681, Int.ofNat (nat_lit 31293969260400)), (nat_lit 3682, Int.ofNat (nat_lit 43670515451904)), (nat_lit 3683, Int.ofNat (nat_lit 22669871994000)), (nat_lit 3684, Int.ofNat (nat_lit 26794767661200)), (nat_lit 3685, Int.ofNat (nat_lit 29899070586000)), (nat_lit 3686, Int.ofNat (nat_lit 36086414086800)), (nat_lit 3687, Int.ofNat (nat_lit 42273757587600)), (nat_lit 3688, Int.ofNat (nat_lit 48461101088400)), (nat_lit 3689, Int.ofNat (nat_lit 54648444589200)), (nat_lit 3690, Int.ofNat (nat_lit 47823313522248)), (nat_lit 3691, Int.ofNat (nat_lit 65569641223680)), (nat_lit 3692, Int.ofNat (nat_lit 83315968925112)), (nat_lit 3693, Int.ofNat (nat_lit 168997180831380)), (nat_lit 3694, Int.ofNat (nat_lit 254678392737648)), (nat_lit 3695, Int.ofNat (nat_lit 349755587977950)), (nat_lit 3706, Int.ofNat (nat_lit 41144504117904)), (nat_lit 3707, Int.ofNat (nat_lit 68517563369904)), (nat_lit 3708, Int.ofNat (nat_lit 69580680809904)), (nat_lit 3709, Int.ofNat (nat_lit 75789286659504)), (nat_lit 3710, Int.ofNat (nat_lit 81997892509104)), (nat_lit 3711, Int.ofNat (nat_lit 88206498358704)), (nat_lit 3712, Int.ofNat (nat_lit 94415104208304)), (nat_lit 3713, Int.ofNat (nat_lit 100623710057904)), (nat_lit 3714, Int.ofNat (nat_lit 99978636340440)), (nat_lit 3715, Int.ofNat (nat_lit 122637785402880)), (nat_lit 3716, Int.ofNat (nat_lit 145296934465320)), (nat_lit 3717, Int.ofNat (nat_lit 229643480261052)), (nat_lit 3718, Int.ofNat (nat_lit 313990026056784))]
theorem block023_data_flat078_step : block023_data_flat078 = (CoefficientMerge.fastMerge block023_data_flat038 block023_data_flat077) := by decide +kernel
theorem block023_data_flat078_original : block023_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded))))))) := by
  rw [block023_data_flat078_step, block023_data_flat038_original, block023_data_flat077_original]
def block023_data_flat079 : CoefficientMerge.Poly := [(nat_lit 3719, Int.ofNat (nat_lit 405876047439258))]
theorem block023_data_flat079_step : block023_data_flat079 = (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) := by decide +kernel
theorem block023_data_flat079_original : block023_data_flat079 = (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) := by
  rw [block023_data_flat079_step]
def block023_data_flat080 : CoefficientMerge.Poly := [(nat_lit 3731, Int.ofNat (nat_lit 62307098330400))]
theorem block023_data_flat080_step : block023_data_flat080 = (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded) := by decide +kernel
theorem block023_data_flat080_original : block023_data_flat080 = (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded) := by
  rw [block023_data_flat080_step]
def block023_data_flat081 : CoefficientMerge.Poly := [(nat_lit 3719, Int.ofNat (nat_lit 405876047439258)), (nat_lit 3731, Int.ofNat (nat_lit 62307098330400))]
theorem block023_data_flat081_step : block023_data_flat081 = (CoefficientMerge.fastMerge block023_data_flat079 block023_data_flat080) := by decide +kernel
theorem block023_data_flat081_original : block023_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded)) := by
  rw [block023_data_flat081_step, block023_data_flat079_original, block023_data_flat080_original]
def block023_data_flat082 : CoefficientMerge.Poly := [(nat_lit 3732, Int.ofNat (nat_lit 104900012632800))]
theorem block023_data_flat082_step : block023_data_flat082 = (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) := by decide +kernel
theorem block023_data_flat082_original : block023_data_flat082 = (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) := by
  rw [block023_data_flat082_step]
def block023_data_flat083 : CoefficientMerge.Poly := [(nat_lit 3733, Int.ofNat (nat_lit 107026247512800))]
theorem block023_data_flat083_step : block023_data_flat083 = (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) := by decide +kernel
theorem block023_data_flat083_original : block023_data_flat083 = (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) := by
  rw [block023_data_flat083_step]
def block023_data_flat084 : CoefficientMerge.Poly := [(nat_lit 3734, Int.ofNat (nat_lit 109152482392800))]
theorem block023_data_flat084_step : block023_data_flat084 = (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded) := by decide +kernel
theorem block023_data_flat084_original : block023_data_flat084 = (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded) := by
  rw [block023_data_flat084_step]
def block023_data_flat085 : CoefficientMerge.Poly := [(nat_lit 3733, Int.ofNat (nat_lit 107026247512800)), (nat_lit 3734, Int.ofNat (nat_lit 109152482392800))]
theorem block023_data_flat085_step : block023_data_flat085 = (CoefficientMerge.fastMerge block023_data_flat083 block023_data_flat084) := by decide +kernel
theorem block023_data_flat085_original : block023_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded)) := by
  rw [block023_data_flat085_step, block023_data_flat083_original, block023_data_flat084_original]
def block023_data_flat086 : CoefficientMerge.Poly := [(nat_lit 3732, Int.ofNat (nat_lit 104900012632800)), (nat_lit 3733, Int.ofNat (nat_lit 107026247512800)), (nat_lit 3734, Int.ofNat (nat_lit 109152482392800))]
theorem block023_data_flat086_step : block023_data_flat086 = (CoefficientMerge.fastMerge block023_data_flat082 block023_data_flat085) := by decide +kernel
theorem block023_data_flat086_original : block023_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded))) := by
  rw [block023_data_flat086_step, block023_data_flat082_original, block023_data_flat085_original]
def block023_data_flat087 : CoefficientMerge.Poly := [(nat_lit 3719, Int.ofNat (nat_lit 405876047439258)), (nat_lit 3731, Int.ofNat (nat_lit 62307098330400)), (nat_lit 3732, Int.ofNat (nat_lit 104900012632800)), (nat_lit 3733, Int.ofNat (nat_lit 107026247512800)), (nat_lit 3734, Int.ofNat (nat_lit 109152482392800))]
theorem block023_data_flat087_step : block023_data_flat087 = (CoefficientMerge.fastMerge block023_data_flat081 block023_data_flat086) := by decide +kernel
theorem block023_data_flat087_original : block023_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded)))) := by
  rw [block023_data_flat087_step, block023_data_flat081_original, block023_data_flat086_original]
def block023_data_flat088 : CoefficientMerge.Poly := [(nat_lit 3735, Int.ofNat (nat_lit 111278717272800))]
theorem block023_data_flat088_step : block023_data_flat088 = (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) := by decide +kernel
theorem block023_data_flat088_original : block023_data_flat088 = (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) := by
  rw [block023_data_flat088_step]
def block023_data_flat089 : CoefficientMerge.Poly := [(nat_lit 3736, Int.ofNat (nat_lit 116487992728800))]
theorem block023_data_flat089_step : block023_data_flat089 = (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded) := by decide +kernel
theorem block023_data_flat089_original : block023_data_flat089 = (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded) := by
  rw [block023_data_flat089_step]
def block023_data_flat090 : CoefficientMerge.Poly := [(nat_lit 3735, Int.ofNat (nat_lit 111278717272800)), (nat_lit 3736, Int.ofNat (nat_lit 116487992728800))]
theorem block023_data_flat090_step : block023_data_flat090 = (CoefficientMerge.fastMerge block023_data_flat088 block023_data_flat089) := by decide +kernel
theorem block023_data_flat090_original : block023_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded)) := by
  rw [block023_data_flat090_step, block023_data_flat088_original, block023_data_flat089_original]
def block023_data_flat091 : CoefficientMerge.Poly := [(nat_lit 3737, Int.ofNat (nat_lit 121697268184800))]
theorem block023_data_flat091_step : block023_data_flat091 = (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) := by decide +kernel
theorem block023_data_flat091_original : block023_data_flat091 = (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) := by
  rw [block023_data_flat091_step]
def block023_data_flat092 : CoefficientMerge.Poly := [(nat_lit 3738, Int.ofNat (nat_lit 142977134375856))]
theorem block023_data_flat092_step : block023_data_flat092 = (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) := by decide +kernel
theorem block023_data_flat092_original : block023_data_flat092 = (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) := by
  rw [block023_data_flat092_step]
def block023_data_flat093 : CoefficientMerge.Poly := [(nat_lit 3739, Int.ofNat (nat_lit 164808313021440))]
theorem block023_data_flat093_step : block023_data_flat093 = (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded) := by decide +kernel
theorem block023_data_flat093_original : block023_data_flat093 = (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded) := by
  rw [block023_data_flat093_step]
def block023_data_flat094 : CoefficientMerge.Poly := [(nat_lit 3738, Int.ofNat (nat_lit 142977134375856)), (nat_lit 3739, Int.ofNat (nat_lit 164808313021440))]
theorem block023_data_flat094_step : block023_data_flat094 = (CoefficientMerge.fastMerge block023_data_flat092 block023_data_flat093) := by decide +kernel
theorem block023_data_flat094_original : block023_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded)) := by
  rw [block023_data_flat094_step, block023_data_flat092_original, block023_data_flat093_original]
def block023_data_flat095 : CoefficientMerge.Poly := [(nat_lit 3737, Int.ofNat (nat_lit 121697268184800)), (nat_lit 3738, Int.ofNat (nat_lit 142977134375856)), (nat_lit 3739, Int.ofNat (nat_lit 164808313021440))]
theorem block023_data_flat095_step : block023_data_flat095 = (CoefficientMerge.fastMerge block023_data_flat091 block023_data_flat094) := by decide +kernel
theorem block023_data_flat095_original : block023_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded))) := by
  rw [block023_data_flat095_step, block023_data_flat091_original, block023_data_flat094_original]
def block023_data_flat096 : CoefficientMerge.Poly := [(nat_lit 3735, Int.ofNat (nat_lit 111278717272800)), (nat_lit 3736, Int.ofNat (nat_lit 116487992728800)), (nat_lit 3737, Int.ofNat (nat_lit 121697268184800)), (nat_lit 3738, Int.ofNat (nat_lit 142977134375856)), (nat_lit 3739, Int.ofNat (nat_lit 164808313021440))]
theorem block023_data_flat096_step : block023_data_flat096 = (CoefficientMerge.fastMerge block023_data_flat090 block023_data_flat095) := by decide +kernel
theorem block023_data_flat096_original : block023_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded)))) := by
  rw [block023_data_flat096_step, block023_data_flat090_original, block023_data_flat095_original]
def block023_data_flat097 : CoefficientMerge.Poly := [(nat_lit 3719, Int.ofNat (nat_lit 405876047439258)), (nat_lit 3731, Int.ofNat (nat_lit 62307098330400)), (nat_lit 3732, Int.ofNat (nat_lit 104900012632800)), (nat_lit 3733, Int.ofNat (nat_lit 107026247512800)), (nat_lit 3734, Int.ofNat (nat_lit 109152482392800)), (nat_lit 3735, Int.ofNat (nat_lit 111278717272800)), (nat_lit 3736, Int.ofNat (nat_lit 116487992728800)), (nat_lit 3737, Int.ofNat (nat_lit 121697268184800)), (nat_lit 3738, Int.ofNat (nat_lit 142977134375856)), (nat_lit 3739, Int.ofNat (nat_lit 164808313021440))]
theorem block023_data_flat097_step : block023_data_flat097 = (CoefficientMerge.fastMerge block023_data_flat087 block023_data_flat096) := by decide +kernel
theorem block023_data_flat097_original : block023_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded))))) := by
  rw [block023_data_flat097_step, block023_data_flat087_original, block023_data_flat096_original]
def block023_data_flat098 : CoefficientMerge.Poly := [(nat_lit 3740, Int.ofNat (nat_lit 208556285438160))]
theorem block023_data_flat098_step : block023_data_flat098 = (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) := by decide +kernel
theorem block023_data_flat098_original : block023_data_flat098 = (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) := by
  rw [block023_data_flat098_step]
def block023_data_flat099 : CoefficientMerge.Poly := [(nat_lit 3741, Int.ofNat (nat_lit 289029266970840))]
theorem block023_data_flat099_step : block023_data_flat099 = (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded) := by decide +kernel
theorem block023_data_flat099_original : block023_data_flat099 = (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded) := by
  rw [block023_data_flat099_step]
def block023_data_flat100 : CoefficientMerge.Poly := [(nat_lit 3740, Int.ofNat (nat_lit 208556285438160)), (nat_lit 3741, Int.ofNat (nat_lit 289029266970840))]
theorem block023_data_flat100_step : block023_data_flat100 = (CoefficientMerge.fastMerge block023_data_flat098 block023_data_flat099) := by decide +kernel
theorem block023_data_flat100_original : block023_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded)) := by
  rw [block023_data_flat100_step, block023_data_flat098_original, block023_data_flat099_original]
def block023_data_flat101 : CoefficientMerge.Poly := [(nat_lit 3742, Int.ofNat (nat_lit 379790294156064))]
theorem block023_data_flat101_step : block023_data_flat101 = (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) := by decide +kernel
theorem block023_data_flat101_original : block023_data_flat101 = (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) := by
  rw [block023_data_flat101_step]
def block023_data_flat102 : CoefficientMerge.Poly := [(nat_lit 3743, Int.ofNat (nat_lit 475393062860100))]
theorem block023_data_flat102_step : block023_data_flat102 = (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) := by decide +kernel
theorem block023_data_flat102_original : block023_data_flat102 = (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) := by
  rw [block023_data_flat102_step]
def block023_data_flat103 : CoefficientMerge.Poly := [(nat_lit 3756, Int.ofNat (nat_lit 77526953380800))]
theorem block023_data_flat103_step : block023_data_flat103 = (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded) := by decide +kernel
theorem block023_data_flat103_original : block023_data_flat103 = (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded) := by
  rw [block023_data_flat103_step]
def block023_data_flat104 : CoefficientMerge.Poly := [(nat_lit 3743, Int.ofNat (nat_lit 475393062860100)), (nat_lit 3756, Int.ofNat (nat_lit 77526953380800))]
theorem block023_data_flat104_step : block023_data_flat104 = (CoefficientMerge.fastMerge block023_data_flat102 block023_data_flat103) := by decide +kernel
theorem block023_data_flat104_original : block023_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded)) := by
  rw [block023_data_flat104_step, block023_data_flat102_original, block023_data_flat103_original]
def block023_data_flat105 : CoefficientMerge.Poly := [(nat_lit 3742, Int.ofNat (nat_lit 379790294156064)), (nat_lit 3743, Int.ofNat (nat_lit 475393062860100)), (nat_lit 3756, Int.ofNat (nat_lit 77526953380800))]
theorem block023_data_flat105_step : block023_data_flat105 = (CoefficientMerge.fastMerge block023_data_flat101 block023_data_flat104) := by decide +kernel
theorem block023_data_flat105_original : block023_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded))) := by
  rw [block023_data_flat105_step, block023_data_flat101_original, block023_data_flat104_original]
def block023_data_flat106 : CoefficientMerge.Poly := [(nat_lit 3740, Int.ofNat (nat_lit 208556285438160)), (nat_lit 3741, Int.ofNat (nat_lit 289029266970840)), (nat_lit 3742, Int.ofNat (nat_lit 379790294156064)), (nat_lit 3743, Int.ofNat (nat_lit 475393062860100)), (nat_lit 3756, Int.ofNat (nat_lit 77526953380800))]
theorem block023_data_flat106_step : block023_data_flat106 = (CoefficientMerge.fastMerge block023_data_flat100 block023_data_flat105) := by decide +kernel
theorem block023_data_flat106_original : block023_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded)))) := by
  rw [block023_data_flat106_step, block023_data_flat100_original, block023_data_flat105_original]
def block023_data_flat107 : CoefficientMerge.Poly := [(nat_lit 3757, Int.ofNat (nat_lit 146429366529600))]
theorem block023_data_flat107_step : block023_data_flat107 = (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) := by decide +kernel
theorem block023_data_flat107_original : block023_data_flat107 = (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) := by
  rw [block023_data_flat107_step]
def block023_data_flat108 : CoefficientMerge.Poly := [(nat_lit 3758, Int.ofNat (nat_lit 149618718849600))]
theorem block023_data_flat108_step : block023_data_flat108 = (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded) := by decide +kernel
theorem block023_data_flat108_original : block023_data_flat108 = (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded) := by
  rw [block023_data_flat108_step]
def block023_data_flat109 : CoefficientMerge.Poly := [(nat_lit 3757, Int.ofNat (nat_lit 146429366529600)), (nat_lit 3758, Int.ofNat (nat_lit 149618718849600))]
theorem block023_data_flat109_step : block023_data_flat109 = (CoefficientMerge.fastMerge block023_data_flat107 block023_data_flat108) := by decide +kernel
theorem block023_data_flat109_original : block023_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded)) := by
  rw [block023_data_flat109_step, block023_data_flat107_original, block023_data_flat108_original]
def block023_data_flat110 : CoefficientMerge.Poly := [(nat_lit 3759, Int.ofNat (nat_lit 152808071169600))]
theorem block023_data_flat110_step : block023_data_flat110 = (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) := by decide +kernel
theorem block023_data_flat110_original : block023_data_flat110 = (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) := by
  rw [block023_data_flat110_step]
def block023_data_flat111 : CoefficientMerge.Poly := [(nat_lit 3760, Int.ofNat (nat_lit 155997423489600))]
theorem block023_data_flat111_step : block023_data_flat111 = (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) := by decide +kernel
theorem block023_data_flat111_original : block023_data_flat111 = (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) := by
  rw [block023_data_flat111_step]
def block023_data_flat112 : CoefficientMerge.Poly := [(nat_lit 3761, Int.ofNat (nat_lit 159186775809600))]
theorem block023_data_flat112_step : block023_data_flat112 = (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded) := by decide +kernel
theorem block023_data_flat112_original : block023_data_flat112 = (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded) := by
  rw [block023_data_flat112_step]
def block023_data_flat113 : CoefficientMerge.Poly := [(nat_lit 3760, Int.ofNat (nat_lit 155997423489600)), (nat_lit 3761, Int.ofNat (nat_lit 159186775809600))]
theorem block023_data_flat113_step : block023_data_flat113 = (CoefficientMerge.fastMerge block023_data_flat111 block023_data_flat112) := by decide +kernel
theorem block023_data_flat113_original : block023_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded)) := by
  rw [block023_data_flat113_step, block023_data_flat111_original, block023_data_flat112_original]
def block023_data_flat114 : CoefficientMerge.Poly := [(nat_lit 3759, Int.ofNat (nat_lit 152808071169600)), (nat_lit 3760, Int.ofNat (nat_lit 155997423489600)), (nat_lit 3761, Int.ofNat (nat_lit 159186775809600))]
theorem block023_data_flat114_step : block023_data_flat114 = (CoefficientMerge.fastMerge block023_data_flat110 block023_data_flat113) := by decide +kernel
theorem block023_data_flat114_original : block023_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded))) := by
  rw [block023_data_flat114_step, block023_data_flat110_original, block023_data_flat113_original]
def block023_data_flat115 : CoefficientMerge.Poly := [(nat_lit 3757, Int.ofNat (nat_lit 146429366529600)), (nat_lit 3758, Int.ofNat (nat_lit 149618718849600)), (nat_lit 3759, Int.ofNat (nat_lit 152808071169600)), (nat_lit 3760, Int.ofNat (nat_lit 155997423489600)), (nat_lit 3761, Int.ofNat (nat_lit 159186775809600))]
theorem block023_data_flat115_step : block023_data_flat115 = (CoefficientMerge.fastMerge block023_data_flat109 block023_data_flat114) := by decide +kernel
theorem block023_data_flat115_original : block023_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded)))) := by
  rw [block023_data_flat115_step, block023_data_flat109_original, block023_data_flat114_original]
def block023_data_flat116 : CoefficientMerge.Poly := [(nat_lit 3740, Int.ofNat (nat_lit 208556285438160)), (nat_lit 3741, Int.ofNat (nat_lit 289029266970840)), (nat_lit 3742, Int.ofNat (nat_lit 379790294156064)), (nat_lit 3743, Int.ofNat (nat_lit 475393062860100)), (nat_lit 3756, Int.ofNat (nat_lit 77526953380800)), (nat_lit 3757, Int.ofNat (nat_lit 146429366529600)), (nat_lit 3758, Int.ofNat (nat_lit 149618718849600)), (nat_lit 3759, Int.ofNat (nat_lit 152808071169600)), (nat_lit 3760, Int.ofNat (nat_lit 155997423489600)), (nat_lit 3761, Int.ofNat (nat_lit 159186775809600))]
theorem block023_data_flat116_step : block023_data_flat116 = (CoefficientMerge.fastMerge block023_data_flat106 block023_data_flat115) := by decide +kernel
theorem block023_data_flat116_original : block023_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded))))) := by
  rw [block023_data_flat116_step, block023_data_flat106_original, block023_data_flat115_original]
def block023_data_flat117 : CoefficientMerge.Poly := [(nat_lit 3719, Int.ofNat (nat_lit 405876047439258)), (nat_lit 3731, Int.ofNat (nat_lit 62307098330400)), (nat_lit 3732, Int.ofNat (nat_lit 104900012632800)), (nat_lit 3733, Int.ofNat (nat_lit 107026247512800)), (nat_lit 3734, Int.ofNat (nat_lit 109152482392800)), (nat_lit 3735, Int.ofNat (nat_lit 111278717272800)), (nat_lit 3736, Int.ofNat (nat_lit 116487992728800)), (nat_lit 3737, Int.ofNat (nat_lit 121697268184800)), (nat_lit 3738, Int.ofNat (nat_lit 142977134375856)), (nat_lit 3739, Int.ofNat (nat_lit 164808313021440)), (nat_lit 3740, Int.ofNat (nat_lit 208556285438160)), (nat_lit 3741, Int.ofNat (nat_lit 289029266970840)), (nat_lit 3742, Int.ofNat (nat_lit 379790294156064)), (nat_lit 3743, Int.ofNat (nat_lit 475393062860100)), (nat_lit 3756, Int.ofNat (nat_lit 77526953380800)), (nat_lit 3757, Int.ofNat (nat_lit 146429366529600)), (nat_lit 3758, Int.ofNat (nat_lit 149618718849600)), (nat_lit 3759, Int.ofNat (nat_lit 152808071169600)), (nat_lit 3760, Int.ofNat (nat_lit 155997423489600)), (nat_lit 3761, Int.ofNat (nat_lit 159186775809600))]
theorem block023_data_flat117_step : block023_data_flat117 = (CoefficientMerge.fastMerge block023_data_flat097 block023_data_flat116) := by decide +kernel
theorem block023_data_flat117_original : block023_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded)))))) := by
  rw [block023_data_flat117_step, block023_data_flat097_original, block023_data_flat116_original]
def block023_data_flat118 : CoefficientMerge.Poly := [(nat_lit 3762, Int.ofNat (nat_lit 219028702232736))]
theorem block023_data_flat118_step : block023_data_flat118 = (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) := by decide +kernel
theorem block023_data_flat118_original : block023_data_flat118 = (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) := by
  rw [block023_data_flat118_step]
def block023_data_flat119 : CoefficientMerge.Poly := [(nat_lit 3763, Int.ofNat (nat_lit 218857203671040))]
theorem block023_data_flat119_step : block023_data_flat119 = (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded) := by decide +kernel
theorem block023_data_flat119_original : block023_data_flat119 = (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded) := by
  rw [block023_data_flat119_step]
def block023_data_flat120 : CoefficientMerge.Poly := [(nat_lit 3762, Int.ofNat (nat_lit 219028702232736)), (nat_lit 3763, Int.ofNat (nat_lit 218857203671040))]
theorem block023_data_flat120_step : block023_data_flat120 = (CoefficientMerge.fastMerge block023_data_flat118 block023_data_flat119) := by decide +kernel
theorem block023_data_flat120_original : block023_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded)) := by
  rw [block023_data_flat120_step, block023_data_flat118_original, block023_data_flat119_original]
def block023_data_flat121 : CoefficientMerge.Poly := [(nat_lit 3764, Int.ofNat (nat_lit 328731745304160))]
theorem block023_data_flat121_step : block023_data_flat121 = (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) := by decide +kernel
theorem block023_data_flat121_original : block023_data_flat121 = (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) := by
  rw [block023_data_flat121_step]
def block023_data_flat122 : CoefficientMerge.Poly := [(nat_lit 3765, Int.ofNat (nat_lit 342942277922640))]
theorem block023_data_flat122_step : block023_data_flat122 = (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) := by decide +kernel
theorem block023_data_flat122_original : block023_data_flat122 = (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) := by
  rw [block023_data_flat122_step]
def block023_data_flat123 : CoefficientMerge.Poly := [(nat_lit 3766, Int.ofNat (nat_lit 426827127950784))]
theorem block023_data_flat123_step : block023_data_flat123 = (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded) := by decide +kernel
theorem block023_data_flat123_original : block023_data_flat123 = (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded) := by
  rw [block023_data_flat123_step]
def block023_data_flat124 : CoefficientMerge.Poly := [(nat_lit 3765, Int.ofNat (nat_lit 342942277922640)), (nat_lit 3766, Int.ofNat (nat_lit 426827127950784))]
theorem block023_data_flat124_step : block023_data_flat124 = (CoefficientMerge.fastMerge block023_data_flat122 block023_data_flat123) := by decide +kernel
theorem block023_data_flat124_original : block023_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded)) := by
  rw [block023_data_flat124_step, block023_data_flat122_original, block023_data_flat123_original]
def block023_data_flat125 : CoefficientMerge.Poly := [(nat_lit 3764, Int.ofNat (nat_lit 328731745304160)), (nat_lit 3765, Int.ofNat (nat_lit 342942277922640)), (nat_lit 3766, Int.ofNat (nat_lit 426827127950784))]
theorem block023_data_flat125_step : block023_data_flat125 = (CoefficientMerge.fastMerge block023_data_flat121 block023_data_flat124) := by decide +kernel
theorem block023_data_flat125_original : block023_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded))) := by
  rw [block023_data_flat125_step, block023_data_flat121_original, block023_data_flat124_original]
def block023_data_flat126 : CoefficientMerge.Poly := [(nat_lit 3762, Int.ofNat (nat_lit 219028702232736)), (nat_lit 3763, Int.ofNat (nat_lit 218857203671040)), (nat_lit 3764, Int.ofNat (nat_lit 328731745304160)), (nat_lit 3765, Int.ofNat (nat_lit 342942277922640)), (nat_lit 3766, Int.ofNat (nat_lit 426827127950784))]
theorem block023_data_flat126_step : block023_data_flat126 = (CoefficientMerge.fastMerge block023_data_flat120 block023_data_flat125) := by decide +kernel
theorem block023_data_flat126_original : block023_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded)))) := by
  rw [block023_data_flat126_step, block023_data_flat120_original, block023_data_flat125_original]
def block023_data_flat127 : CoefficientMerge.Poly := [(nat_lit 3767, Int.ofNat (nat_lit 511824270295800))]
theorem block023_data_flat127_step : block023_data_flat127 = (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) := by decide +kernel
theorem block023_data_flat127_original : block023_data_flat127 = (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) := by
  rw [block023_data_flat127_step]
def block023_data_flat128 : CoefficientMerge.Poly := [(nat_lit 3781, Int.ofNat (nat_lit 103836452227200))]
theorem block023_data_flat128_step : block023_data_flat128 = (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded) := by decide +kernel
theorem block023_data_flat128_original : block023_data_flat128 = (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded) := by
  rw [block023_data_flat128_step]
def block023_data_flat129 : CoefficientMerge.Poly := [(nat_lit 3767, Int.ofNat (nat_lit 511824270295800)), (nat_lit 3781, Int.ofNat (nat_lit 103836452227200))]
theorem block023_data_flat129_step : block023_data_flat129 = (CoefficientMerge.fastMerge block023_data_flat127 block023_data_flat128) := by decide +kernel
theorem block023_data_flat129_original : block023_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded)) := by
  rw [block023_data_flat129_step, block023_data_flat127_original, block023_data_flat128_original]
def block023_data_flat130 : CoefficientMerge.Poly := [(nat_lit 3782, Int.ofNat (nat_lit 195494894179200))]
theorem block023_data_flat130_step : block023_data_flat130 = (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) := by decide +kernel
theorem block023_data_flat130_original : block023_data_flat130 = (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) := by
  rw [block023_data_flat130_step]
def block023_data_flat131 : CoefficientMerge.Poly := [(nat_lit 3783, Int.ofNat (nat_lit 192560690044800))]
theorem block023_data_flat131_step : block023_data_flat131 = (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) := by decide +kernel
theorem block023_data_flat131_original : block023_data_flat131 = (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) := by
  rw [block023_data_flat131_step]
def block023_data_flat132 : CoefficientMerge.Poly := [(nat_lit 3784, Int.ofNat (nat_lit 192709526486400))]
theorem block023_data_flat132_step : block023_data_flat132 = (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded) := by decide +kernel
theorem block023_data_flat132_original : block023_data_flat132 = (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded) := by
  rw [block023_data_flat132_step]
def block023_data_flat133 : CoefficientMerge.Poly := [(nat_lit 3783, Int.ofNat (nat_lit 192560690044800)), (nat_lit 3784, Int.ofNat (nat_lit 192709526486400))]
theorem block023_data_flat133_step : block023_data_flat133 = (CoefficientMerge.fastMerge block023_data_flat131 block023_data_flat132) := by decide +kernel
theorem block023_data_flat133_original : block023_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded)) := by
  rw [block023_data_flat133_step, block023_data_flat131_original, block023_data_flat132_original]
def block023_data_flat134 : CoefficientMerge.Poly := [(nat_lit 3782, Int.ofNat (nat_lit 195494894179200)), (nat_lit 3783, Int.ofNat (nat_lit 192560690044800)), (nat_lit 3784, Int.ofNat (nat_lit 192709526486400))]
theorem block023_data_flat134_step : block023_data_flat134 = (CoefficientMerge.fastMerge block023_data_flat130 block023_data_flat133) := by decide +kernel
theorem block023_data_flat134_original : block023_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded))) := by
  rw [block023_data_flat134_step, block023_data_flat130_original, block023_data_flat133_original]
def block023_data_flat135 : CoefficientMerge.Poly := [(nat_lit 3767, Int.ofNat (nat_lit 511824270295800)), (nat_lit 3781, Int.ofNat (nat_lit 103836452227200)), (nat_lit 3782, Int.ofNat (nat_lit 195494894179200)), (nat_lit 3783, Int.ofNat (nat_lit 192560690044800)), (nat_lit 3784, Int.ofNat (nat_lit 192709526486400))]
theorem block023_data_flat135_step : block023_data_flat135 = (CoefficientMerge.fastMerge block023_data_flat129 block023_data_flat134) := by decide +kernel
theorem block023_data_flat135_original : block023_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded)))) := by
  rw [block023_data_flat135_step, block023_data_flat129_original, block023_data_flat134_original]
def block023_data_flat136 : CoefficientMerge.Poly := [(nat_lit 3762, Int.ofNat (nat_lit 219028702232736)), (nat_lit 3763, Int.ofNat (nat_lit 218857203671040)), (nat_lit 3764, Int.ofNat (nat_lit 328731745304160)), (nat_lit 3765, Int.ofNat (nat_lit 342942277922640)), (nat_lit 3766, Int.ofNat (nat_lit 426827127950784)), (nat_lit 3767, Int.ofNat (nat_lit 511824270295800)), (nat_lit 3781, Int.ofNat (nat_lit 103836452227200)), (nat_lit 3782, Int.ofNat (nat_lit 195494894179200)), (nat_lit 3783, Int.ofNat (nat_lit 192560690044800)), (nat_lit 3784, Int.ofNat (nat_lit 192709526486400))]
theorem block023_data_flat136_step : block023_data_flat136 = (CoefficientMerge.fastMerge block023_data_flat126 block023_data_flat135) := by decide +kernel
theorem block023_data_flat136_original : block023_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded))))) := by
  rw [block023_data_flat136_step, block023_data_flat126_original, block023_data_flat135_original]
def block023_data_flat137 : CoefficientMerge.Poly := [(nat_lit 3785, Int.ofNat (nat_lit 192858362928000))]
theorem block023_data_flat137_step : block023_data_flat137 = (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) := by decide +kernel
theorem block023_data_flat137_original : block023_data_flat137 = (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) := by
  rw [block023_data_flat137_step]
def block023_data_flat138 : CoefficientMerge.Poly := [(nat_lit 3786, Int.ofNat (nat_lit 241236824875200))]
theorem block023_data_flat138_step : block023_data_flat138 = (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded) := by decide +kernel
theorem block023_data_flat138_original : block023_data_flat138 = (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded) := by
  rw [block023_data_flat138_step]
def block023_data_flat139 : CoefficientMerge.Poly := [(nat_lit 3785, Int.ofNat (nat_lit 192858362928000)), (nat_lit 3786, Int.ofNat (nat_lit 241236824875200))]
theorem block023_data_flat139_step : block023_data_flat139 = (CoefficientMerge.fastMerge block023_data_flat137 block023_data_flat138) := by decide +kernel
theorem block023_data_flat139_original : block023_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded)) := by
  rw [block023_data_flat139_step, block023_data_flat137_original, block023_data_flat138_original]
def block023_data_flat140 : CoefficientMerge.Poly := [(nat_lit 3787, Int.ofNat (nat_lit 242826237561600))]
theorem block023_data_flat140_step : block023_data_flat140 = (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) := by decide +kernel
theorem block023_data_flat140_original : block023_data_flat140 = (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) := by
  rw [block023_data_flat140_step]
def block023_data_flat141 : CoefficientMerge.Poly := [(nat_lit 3788, Int.ofNat (nat_lit 356418199368000))]
theorem block023_data_flat141_step : block023_data_flat141 = (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) := by decide +kernel
theorem block023_data_flat141_original : block023_data_flat141 = (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) := by
  rw [block023_data_flat141_step]
def block023_data_flat142 : CoefficientMerge.Poly := [(nat_lit 3789, Int.ofNat (nat_lit 364599695829600))]
theorem block023_data_flat142_step : block023_data_flat142 = (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded) := by decide +kernel
theorem block023_data_flat142_original : block023_data_flat142 = (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded) := by
  rw [block023_data_flat142_step]
def block023_data_flat143 : CoefficientMerge.Poly := [(nat_lit 3788, Int.ofNat (nat_lit 356418199368000)), (nat_lit 3789, Int.ofNat (nat_lit 364599695829600))]
theorem block023_data_flat143_step : block023_data_flat143 = (CoefficientMerge.fastMerge block023_data_flat141 block023_data_flat142) := by decide +kernel
theorem block023_data_flat143_original : block023_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded)) := by
  rw [block023_data_flat143_step, block023_data_flat141_original, block023_data_flat142_original]
def block023_data_flat144 : CoefficientMerge.Poly := [(nat_lit 3787, Int.ofNat (nat_lit 242826237561600)), (nat_lit 3788, Int.ofNat (nat_lit 356418199368000)), (nat_lit 3789, Int.ofNat (nat_lit 364599695829600))]
theorem block023_data_flat144_step : block023_data_flat144 = (CoefficientMerge.fastMerge block023_data_flat140 block023_data_flat143) := by decide +kernel
theorem block023_data_flat144_original : block023_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded))) := by
  rw [block023_data_flat144_step, block023_data_flat140_original, block023_data_flat143_original]
def block023_data_flat145 : CoefficientMerge.Poly := [(nat_lit 3785, Int.ofNat (nat_lit 192858362928000)), (nat_lit 3786, Int.ofNat (nat_lit 241236824875200)), (nat_lit 3787, Int.ofNat (nat_lit 242826237561600)), (nat_lit 3788, Int.ofNat (nat_lit 356418199368000)), (nat_lit 3789, Int.ofNat (nat_lit 364599695829600))]
theorem block023_data_flat145_step : block023_data_flat145 = (CoefficientMerge.fastMerge block023_data_flat139 block023_data_flat144) := by decide +kernel
theorem block023_data_flat145_original : block023_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded)))) := by
  rw [block023_data_flat145_step, block023_data_flat139_original, block023_data_flat144_original]
def block023_data_flat146 : CoefficientMerge.Poly := [(nat_lit 3790, Int.ofNat (nat_lit 450159465571200))]
theorem block023_data_flat146_step : block023_data_flat146 = (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) := by decide +kernel
theorem block023_data_flat146_original : block023_data_flat146 = (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) := by
  rw [block023_data_flat146_step]
def block023_data_flat147 : CoefficientMerge.Poly := [(nat_lit 3791, Int.ofNat (nat_lit 537932773501200))]
theorem block023_data_flat147_step : block023_data_flat147 = (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded) := by decide +kernel
theorem block023_data_flat147_original : block023_data_flat147 = (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded) := by
  rw [block023_data_flat147_step]
def block023_data_flat148 : CoefficientMerge.Poly := [(nat_lit 3790, Int.ofNat (nat_lit 450159465571200)), (nat_lit 3791, Int.ofNat (nat_lit 537932773501200))]
theorem block023_data_flat148_step : block023_data_flat148 = (CoefficientMerge.fastMerge block023_data_flat146 block023_data_flat147) := by decide +kernel
theorem block023_data_flat148_original : block023_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded)) := by
  rw [block023_data_flat148_step, block023_data_flat146_original, block023_data_flat147_original]
def block023_data_flat149 : CoefficientMerge.Poly := [(nat_lit 3806, Int.ofNat (nat_lit 126592481030400))]
theorem block023_data_flat149_step : block023_data_flat149 = (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) := by decide +kernel
theorem block023_data_flat149_original : block023_data_flat149 = (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) := by
  rw [block023_data_flat149_step]
def block023_data_flat150 : CoefficientMerge.Poly := [(nat_lit 3807, Int.ofNat (nat_lit 241054792070400))]
theorem block023_data_flat150_step : block023_data_flat150 = (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) := by decide +kernel
theorem block023_data_flat150_original : block023_data_flat150 = (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) := by
  rw [block023_data_flat150_step]
def block023_data_flat151 : CoefficientMerge.Poly := [(nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
theorem block023_data_flat151_step : block023_data_flat151 = (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded) := by decide +kernel
theorem block023_data_flat151_original : block023_data_flat151 = (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded) := by
  rw [block023_data_flat151_step]
def block023_data_flat152 : CoefficientMerge.Poly := [(nat_lit 3807, Int.ofNat (nat_lit 241054792070400)), (nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
theorem block023_data_flat152_step : block023_data_flat152 = (CoefficientMerge.fastMerge block023_data_flat150 block023_data_flat151) := by decide +kernel
theorem block023_data_flat152_original : block023_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded)) := by
  rw [block023_data_flat152_step, block023_data_flat150_original, block023_data_flat151_original]
def block023_data_flat153 : CoefficientMerge.Poly := [(nat_lit 3806, Int.ofNat (nat_lit 126592481030400)), (nat_lit 3807, Int.ofNat (nat_lit 241054792070400)), (nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
theorem block023_data_flat153_step : block023_data_flat153 = (CoefficientMerge.fastMerge block023_data_flat149 block023_data_flat152) := by decide +kernel
theorem block023_data_flat153_original : block023_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded))) := by
  rw [block023_data_flat153_step, block023_data_flat149_original, block023_data_flat152_original]
def block023_data_flat154 : CoefficientMerge.Poly := [(nat_lit 3790, Int.ofNat (nat_lit 450159465571200)), (nat_lit 3791, Int.ofNat (nat_lit 537932773501200)), (nat_lit 3806, Int.ofNat (nat_lit 126592481030400)), (nat_lit 3807, Int.ofNat (nat_lit 241054792070400)), (nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
theorem block023_data_flat154_step : block023_data_flat154 = (CoefficientMerge.fastMerge block023_data_flat148 block023_data_flat153) := by decide +kernel
theorem block023_data_flat154_original : block023_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded)))) := by
  rw [block023_data_flat154_step, block023_data_flat148_original, block023_data_flat153_original]
def block023_data_flat155 : CoefficientMerge.Poly := [(nat_lit 3785, Int.ofNat (nat_lit 192858362928000)), (nat_lit 3786, Int.ofNat (nat_lit 241236824875200)), (nat_lit 3787, Int.ofNat (nat_lit 242826237561600)), (nat_lit 3788, Int.ofNat (nat_lit 356418199368000)), (nat_lit 3789, Int.ofNat (nat_lit 364599695829600)), (nat_lit 3790, Int.ofNat (nat_lit 450159465571200)), (nat_lit 3791, Int.ofNat (nat_lit 537932773501200)), (nat_lit 3806, Int.ofNat (nat_lit 126592481030400)), (nat_lit 3807, Int.ofNat (nat_lit 241054792070400)), (nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
theorem block023_data_flat155_step : block023_data_flat155 = (CoefficientMerge.fastMerge block023_data_flat145 block023_data_flat154) := by decide +kernel
theorem block023_data_flat155_original : block023_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded))))) := by
  rw [block023_data_flat155_step, block023_data_flat145_original, block023_data_flat154_original]
def block023_data_flat156 : CoefficientMerge.Poly := [(nat_lit 3762, Int.ofNat (nat_lit 219028702232736)), (nat_lit 3763, Int.ofNat (nat_lit 218857203671040)), (nat_lit 3764, Int.ofNat (nat_lit 328731745304160)), (nat_lit 3765, Int.ofNat (nat_lit 342942277922640)), (nat_lit 3766, Int.ofNat (nat_lit 426827127950784)), (nat_lit 3767, Int.ofNat (nat_lit 511824270295800)), (nat_lit 3781, Int.ofNat (nat_lit 103836452227200)), (nat_lit 3782, Int.ofNat (nat_lit 195494894179200)), (nat_lit 3783, Int.ofNat (nat_lit 192560690044800)), (nat_lit 3784, Int.ofNat (nat_lit 192709526486400)), (nat_lit 3785, Int.ofNat (nat_lit 192858362928000)), (nat_lit 3786, Int.ofNat (nat_lit 241236824875200)), (nat_lit 3787, Int.ofNat (nat_lit 242826237561600)), (nat_lit 3788, Int.ofNat (nat_lit 356418199368000)), (nat_lit 3789, Int.ofNat (nat_lit 364599695829600)), (nat_lit 3790, Int.ofNat (nat_lit 450159465571200)), (nat_lit 3791, Int.ofNat (nat_lit 537932773501200)), (nat_lit 3806, Int.ofNat (nat_lit 126592481030400)), (nat_lit 3807, Int.ofNat (nat_lit 241054792070400)), (nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
theorem block023_data_flat156_step : block023_data_flat156 = (CoefficientMerge.fastMerge block023_data_flat136 block023_data_flat155) := by decide +kernel
theorem block023_data_flat156_original : block023_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded)))))) := by
  rw [block023_data_flat156_step, block023_data_flat136_original, block023_data_flat155_original]
def block023_data_flat157 : CoefficientMerge.Poly := [(nat_lit 3719, Int.ofNat (nat_lit 405876047439258)), (nat_lit 3731, Int.ofNat (nat_lit 62307098330400)), (nat_lit 3732, Int.ofNat (nat_lit 104900012632800)), (nat_lit 3733, Int.ofNat (nat_lit 107026247512800)), (nat_lit 3734, Int.ofNat (nat_lit 109152482392800)), (nat_lit 3735, Int.ofNat (nat_lit 111278717272800)), (nat_lit 3736, Int.ofNat (nat_lit 116487992728800)), (nat_lit 3737, Int.ofNat (nat_lit 121697268184800)), (nat_lit 3738, Int.ofNat (nat_lit 142977134375856)), (nat_lit 3739, Int.ofNat (nat_lit 164808313021440)), (nat_lit 3740, Int.ofNat (nat_lit 208556285438160)), (nat_lit 3741, Int.ofNat (nat_lit 289029266970840)), (nat_lit 3742, Int.ofNat (nat_lit 379790294156064)), (nat_lit 3743, Int.ofNat (nat_lit 475393062860100)), (nat_lit 3756, Int.ofNat (nat_lit 77526953380800)), (nat_lit 3757, Int.ofNat (nat_lit 146429366529600)), (nat_lit 3758, Int.ofNat (nat_lit 149618718849600)), (nat_lit 3759, Int.ofNat (nat_lit 152808071169600)), (nat_lit 3760, Int.ofNat (nat_lit 155997423489600)), (nat_lit 3761, Int.ofNat (nat_lit 159186775809600)), (nat_lit 3762, Int.ofNat (nat_lit 219028702232736)), (nat_lit 3763, Int.ofNat (nat_lit 218857203671040)), (nat_lit 3764, Int.ofNat (nat_lit 328731745304160)), (nat_lit 3765, Int.ofNat (nat_lit 342942277922640)), (nat_lit 3766, Int.ofNat (nat_lit 426827127950784)), (nat_lit 3767, Int.ofNat (nat_lit 511824270295800)), (nat_lit 3781, Int.ofNat (nat_lit 103836452227200)), (nat_lit 3782, Int.ofNat (nat_lit 195494894179200)), (nat_lit 3783, Int.ofNat (nat_lit 192560690044800)), (nat_lit 3784, Int.ofNat (nat_lit 192709526486400)), (nat_lit 3785, Int.ofNat (nat_lit 192858362928000)), (nat_lit 3786, Int.ofNat (nat_lit 241236824875200)), (nat_lit 3787, Int.ofNat (nat_lit 242826237561600)), (nat_lit 3788, Int.ofNat (nat_lit 356418199368000)), (nat_lit 3789, Int.ofNat (nat_lit 364599695829600)), (nat_lit 3790, Int.ofNat (nat_lit 450159465571200)), (nat_lit 3791, Int.ofNat (nat_lit 537932773501200)), (nat_lit 3806, Int.ofNat (nat_lit 126592481030400)), (nat_lit 3807, Int.ofNat (nat_lit 241054792070400)), (nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
theorem block023_data_flat157_step : block023_data_flat157 = (CoefficientMerge.fastMerge block023_data_flat117 block023_data_flat156) := by decide +kernel
theorem block023_data_flat157_original : block023_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded))))))) := by
  rw [block023_data_flat157_step, block023_data_flat117_original, block023_data_flat156_original]
def block023_data_flat158 : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 19897350303600)), (nat_lit 3661, Int.ofNat (nat_lit 5145488409600)), (nat_lit 3662, Int.ofNat (nat_lit 10290976819200)), (nat_lit 3663, Int.ofNat (nat_lit 15436465228800)), (nat_lit 3664, Int.ofNat (nat_lit 20581953638400)), (nat_lit 3665, Int.ofNat (nat_lit 25727442048000)), (nat_lit 3666, Int.ofNat (nat_lit 11587980096000)), (nat_lit 3667, Int.ofNat (nat_lit 19816509081600)), (nat_lit 3668, Int.ofNat (nat_lit 28045038067200)), (nat_lit 3669, Int.ofNat (nat_lit 101836019577600)), (nat_lit 3670, Int.ofNat (nat_lit 175627001088000)), (nat_lit 3671, Int.ofNat (nat_lit 259831217923200)), (nat_lit 3681, Int.ofNat (nat_lit 31293969260400)), (nat_lit 3682, Int.ofNat (nat_lit 43670515451904)), (nat_lit 3683, Int.ofNat (nat_lit 22669871994000)), (nat_lit 3684, Int.ofNat (nat_lit 26794767661200)), (nat_lit 3685, Int.ofNat (nat_lit 29899070586000)), (nat_lit 3686, Int.ofNat (nat_lit 36086414086800)), (nat_lit 3687, Int.ofNat (nat_lit 42273757587600)), (nat_lit 3688, Int.ofNat (nat_lit 48461101088400)), (nat_lit 3689, Int.ofNat (nat_lit 54648444589200)), (nat_lit 3690, Int.ofNat (nat_lit 47823313522248)), (nat_lit 3691, Int.ofNat (nat_lit 65569641223680)), (nat_lit 3692, Int.ofNat (nat_lit 83315968925112)), (nat_lit 3693, Int.ofNat (nat_lit 168997180831380)), (nat_lit 3694, Int.ofNat (nat_lit 254678392737648)), (nat_lit 3695, Int.ofNat (nat_lit 349755587977950)), (nat_lit 3706, Int.ofNat (nat_lit 41144504117904)), (nat_lit 3707, Int.ofNat (nat_lit 68517563369904)), (nat_lit 3708, Int.ofNat (nat_lit 69580680809904)), (nat_lit 3709, Int.ofNat (nat_lit 75789286659504)), (nat_lit 3710, Int.ofNat (nat_lit 81997892509104)), (nat_lit 3711, Int.ofNat (nat_lit 88206498358704)), (nat_lit 3712, Int.ofNat (nat_lit 94415104208304)), (nat_lit 3713, Int.ofNat (nat_lit 100623710057904)), (nat_lit 3714, Int.ofNat (nat_lit 99978636340440)), (nat_lit 3715, Int.ofNat (nat_lit 122637785402880)), (nat_lit 3716, Int.ofNat (nat_lit 145296934465320)), (nat_lit 3717, Int.ofNat (nat_lit 229643480261052)), (nat_lit 3718, Int.ofNat (nat_lit 313990026056784)), (nat_lit 3719, Int.ofNat (nat_lit 405876047439258)), (nat_lit 3731, Int.ofNat (nat_lit 62307098330400)), (nat_lit 3732, Int.ofNat (nat_lit 104900012632800)), (nat_lit 3733, Int.ofNat (nat_lit 107026247512800)), (nat_lit 3734, Int.ofNat (nat_lit 109152482392800)), (nat_lit 3735, Int.ofNat (nat_lit 111278717272800)), (nat_lit 3736, Int.ofNat (nat_lit 116487992728800)), (nat_lit 3737, Int.ofNat (nat_lit 121697268184800)), (nat_lit 3738, Int.ofNat (nat_lit 142977134375856)), (nat_lit 3739, Int.ofNat (nat_lit 164808313021440)), (nat_lit 3740, Int.ofNat (nat_lit 208556285438160)), (nat_lit 3741, Int.ofNat (nat_lit 289029266970840)), (nat_lit 3742, Int.ofNat (nat_lit 379790294156064)), (nat_lit 3743, Int.ofNat (nat_lit 475393062860100)), (nat_lit 3756, Int.ofNat (nat_lit 77526953380800)), (nat_lit 3757, Int.ofNat (nat_lit 146429366529600)), (nat_lit 3758, Int.ofNat (nat_lit 149618718849600)), (nat_lit 3759, Int.ofNat (nat_lit 152808071169600)), (nat_lit 3760, Int.ofNat (nat_lit 155997423489600)), (nat_lit 3761, Int.ofNat (nat_lit 159186775809600)), (nat_lit 3762, Int.ofNat (nat_lit 219028702232736)), (nat_lit 3763, Int.ofNat (nat_lit 218857203671040)), (nat_lit 3764, Int.ofNat (nat_lit 328731745304160)), (nat_lit 3765, Int.ofNat (nat_lit 342942277922640)), (nat_lit 3766, Int.ofNat (nat_lit 426827127950784)), (nat_lit 3767, Int.ofNat (nat_lit 511824270295800)), (nat_lit 3781, Int.ofNat (nat_lit 103836452227200)), (nat_lit 3782, Int.ofNat (nat_lit 195494894179200)), (nat_lit 3783, Int.ofNat (nat_lit 192560690044800)), (nat_lit 3784, Int.ofNat (nat_lit 192709526486400)), (nat_lit 3785, Int.ofNat (nat_lit 192858362928000)), (nat_lit 3786, Int.ofNat (nat_lit 241236824875200)), (nat_lit 3787, Int.ofNat (nat_lit 242826237561600)), (nat_lit 3788, Int.ofNat (nat_lit 356418199368000)), (nat_lit 3789, Int.ofNat (nat_lit 364599695829600)), (nat_lit 3790, Int.ofNat (nat_lit 450159465571200)), (nat_lit 3791, Int.ofNat (nat_lit 537932773501200)), (nat_lit 3806, Int.ofNat (nat_lit 126592481030400)), (nat_lit 3807, Int.ofNat (nat_lit 241054792070400)), (nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
theorem block023_data_flat158_step : block023_data_flat158 = (CoefficientMerge.fastMerge block023_data_flat078 block023_data_flat157) := by decide +kernel
theorem block023_data_flat158_original : block023_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded)))))))) := by
  rw [block023_data_flat158_step, block023_data_flat078_original, block023_data_flat157_original]
def block023_data_flat159 : CoefficientMerge.Poly := [(nat_lit 3657, Int.ofNat (nat_lit 19897350303600)), (nat_lit 3661, Int.ofNat (nat_lit 5145488409600)), (nat_lit 3662, Int.ofNat (nat_lit 10290976819200)), (nat_lit 3663, Int.ofNat (nat_lit 15436465228800)), (nat_lit 3664, Int.ofNat (nat_lit 20581953638400)), (nat_lit 3665, Int.ofNat (nat_lit 25727442048000)), (nat_lit 3666, Int.ofNat (nat_lit 11587980096000)), (nat_lit 3667, Int.ofNat (nat_lit 19816509081600)), (nat_lit 3668, Int.ofNat (nat_lit 28045038067200)), (nat_lit 3669, Int.ofNat (nat_lit 101836019577600)), (nat_lit 3670, Int.ofNat (nat_lit 175627001088000)), (nat_lit 3671, Int.ofNat (nat_lit 259831217923200)), (nat_lit 3681, Int.ofNat (nat_lit 31293969260400)), (nat_lit 3682, Int.ofNat (nat_lit 43670515451904)), (nat_lit 3683, Int.ofNat (nat_lit 22669871994000)), (nat_lit 3684, Int.ofNat (nat_lit 26794767661200)), (nat_lit 3685, Int.ofNat (nat_lit 29899070586000)), (nat_lit 3686, Int.ofNat (nat_lit 36086414086800)), (nat_lit 3687, Int.ofNat (nat_lit 42273757587600)), (nat_lit 3688, Int.ofNat (nat_lit 48461101088400)), (nat_lit 3689, Int.ofNat (nat_lit 54648444589200)), (nat_lit 3690, Int.ofNat (nat_lit 47823313522248)), (nat_lit 3691, Int.ofNat (nat_lit 65569641223680)), (nat_lit 3692, Int.ofNat (nat_lit 83315968925112)), (nat_lit 3693, Int.ofNat (nat_lit 168997180831380)), (nat_lit 3694, Int.ofNat (nat_lit 254678392737648)), (nat_lit 3695, Int.ofNat (nat_lit 349755587977950)), (nat_lit 3706, Int.ofNat (nat_lit 41144504117904)), (nat_lit 3707, Int.ofNat (nat_lit 68517563369904)), (nat_lit 3708, Int.ofNat (nat_lit 69580680809904)), (nat_lit 3709, Int.ofNat (nat_lit 75789286659504)), (nat_lit 3710, Int.ofNat (nat_lit 81997892509104)), (nat_lit 3711, Int.ofNat (nat_lit 88206498358704)), (nat_lit 3712, Int.ofNat (nat_lit 94415104208304)), (nat_lit 3713, Int.ofNat (nat_lit 100623710057904)), (nat_lit 3714, Int.ofNat (nat_lit 99978636340440)), (nat_lit 3715, Int.ofNat (nat_lit 122637785402880)), (nat_lit 3716, Int.ofNat (nat_lit 145296934465320)), (nat_lit 3717, Int.ofNat (nat_lit 229643480261052)), (nat_lit 3718, Int.ofNat (nat_lit 313990026056784)), (nat_lit 3719, Int.ofNat (nat_lit 405876047439258)), (nat_lit 3731, Int.ofNat (nat_lit 62307098330400)), (nat_lit 3732, Int.ofNat (nat_lit 104900012632800)), (nat_lit 3733, Int.ofNat (nat_lit 107026247512800)), (nat_lit 3734, Int.ofNat (nat_lit 109152482392800)), (nat_lit 3735, Int.ofNat (nat_lit 111278717272800)), (nat_lit 3736, Int.ofNat (nat_lit 116487992728800)), (nat_lit 3737, Int.ofNat (nat_lit 121697268184800)), (nat_lit 3738, Int.ofNat (nat_lit 142977134375856)), (nat_lit 3739, Int.ofNat (nat_lit 164808313021440)), (nat_lit 3740, Int.ofNat (nat_lit 208556285438160)), (nat_lit 3741, Int.ofNat (nat_lit 289029266970840)), (nat_lit 3742, Int.ofNat (nat_lit 379790294156064)), (nat_lit 3743, Int.ofNat (nat_lit 475393062860100)), (nat_lit 3756, Int.ofNat (nat_lit 77526953380800)), (nat_lit 3757, Int.ofNat (nat_lit 146429366529600)), (nat_lit 3758, Int.ofNat (nat_lit 149618718849600)), (nat_lit 3759, Int.ofNat (nat_lit 152808071169600)), (nat_lit 3760, Int.ofNat (nat_lit 155997423489600)), (nat_lit 3761, Int.ofNat (nat_lit 159186775809600)), (nat_lit 3762, Int.ofNat (nat_lit 219028702232736)), (nat_lit 3763, Int.ofNat (nat_lit 218857203671040)), (nat_lit 3764, Int.ofNat (nat_lit 328731745304160)), (nat_lit 3765, Int.ofNat (nat_lit 342942277922640)), (nat_lit 3766, Int.ofNat (nat_lit 426827127950784)), (nat_lit 3767, Int.ofNat (nat_lit 511824270295800)), (nat_lit 3781, Int.ofNat (nat_lit 103836452227200)), (nat_lit 3782, Int.ofNat (nat_lit 195494894179200)), (nat_lit 3783, Int.ofNat (nat_lit 192560690044800)), (nat_lit 3784, Int.ofNat (nat_lit 192709526486400)), (nat_lit 3785, Int.ofNat (nat_lit 192858362928000)), (nat_lit 3786, Int.ofNat (nat_lit 241236824875200)), (nat_lit 3787, Int.ofNat (nat_lit 242826237561600)), (nat_lit 3788, Int.ofNat (nat_lit 356418199368000)), (nat_lit 3789, Int.ofNat (nat_lit 364599695829600)), (nat_lit 3790, Int.ofNat (nat_lit 450159465571200)), (nat_lit 3791, Int.ofNat (nat_lit 537932773501200)), (nat_lit 3806, Int.ofNat (nat_lit 126592481030400)), (nat_lit 3807, Int.ofNat (nat_lit 241054792070400)), (nat_lit 3808, Int.ofNat (nat_lit 237142519891200))]
theorem block023_data_flat159_step : block023_data_flat159 = (CoefficientMerge.trim block023_data_flat158) := by decide +kernel
theorem block023_data_flat159_original : block023_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded))))))))) := by
  rw [block023_data_flat159_step, block023_data_flat158_original]
theorem block023_data : block023 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded)))))))) := by
  have h : block023 = block023_data_flat159 := by decide +kernel
  exact h.trans block023_data_flat159_original
theorem block023_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block023 := by
  rw [block023_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1649Coded_nonneg g hg hA hB) (atom1650Coded_nonneg g hg hA hB)) (add_nonneg (atom1651Coded_nonneg g hg hA hB) (add_nonneg (atom1652Coded_nonneg g hg hA hB) (atom1653Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1654Coded_nonneg g hg hA hB) (atom1655Coded_nonneg g hg hA hB)) (add_nonneg (atom1656Coded_nonneg g hg hA hB) (add_nonneg (atom1657Coded_nonneg g hg hA hB) (atom1658Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1659Coded_nonneg g hg hA hB) (atom1660Coded_nonneg g hg hA hB)) (add_nonneg (atom1661Coded_nonneg g hg hA hB) (add_nonneg (atom1662Coded_nonneg g hg hA hB) (atom1663Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1664Coded_nonneg g hg hA hB) (atom1665Coded_nonneg g hg hA hB)) (add_nonneg (atom1666Coded_nonneg g hg hA hB) (add_nonneg (atom1667Coded_nonneg g hg hA hB) (atom1668Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1669Coded_nonneg g hg hA hB) (atom1670Coded_nonneg g hg hA hB)) (add_nonneg (atom1671Coded_nonneg g hg hA hB) (add_nonneg (atom1672Coded_nonneg g hg hA hB) (atom1673Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1674Coded_nonneg g hg hA hB) (atom1675Coded_nonneg g hg hA hB)) (add_nonneg (atom1676Coded_nonneg g hg hA hB) (add_nonneg (atom1677Coded_nonneg g hg hA hB) (atom1678Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1679Coded_nonneg g hg hA hB) (atom1680Coded_nonneg g hg hA hB)) (add_nonneg (atom1681Coded_nonneg g hg hA hB) (add_nonneg (atom1682Coded_nonneg g hg hA hB) (atom1683Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1684Coded_nonneg g hg hA hB) (atom1685Coded_nonneg g hg hA hB)) (add_nonneg (atom1686Coded_nonneg g hg hA hB) (add_nonneg (atom1687Coded_nonneg g hg hA hB) (atom1688Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1689Coded_nonneg g hg hA hB) (atom1690Coded_nonneg g hg hA hB)) (add_nonneg (atom1691Coded_nonneg g hg hA hB) (add_nonneg (atom1692Coded_nonneg g hg hA hB) (atom1693Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1694Coded_nonneg g hg hA hB) (atom1695Coded_nonneg g hg hA hB)) (add_nonneg (atom1696Coded_nonneg g hg hA hB) (add_nonneg (atom1697Coded_nonneg g hg hA hB) (atom1698Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1699Coded_nonneg g hg hA hB) (atom1700Coded_nonneg g hg hA hB)) (add_nonneg (atom1701Coded_nonneg g hg hA hB) (add_nonneg (atom1702Coded_nonneg g hg hA hB) (atom1703Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1704Coded_nonneg g hg hA hB) (atom1705Coded_nonneg g hg hA hB)) (add_nonneg (atom1706Coded_nonneg g hg hA hB) (add_nonneg (atom1707Coded_nonneg g hg hA hB) (atom1708Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1709Coded_nonneg g hg hA hB) (atom1710Coded_nonneg g hg hA hB)) (add_nonneg (atom1711Coded_nonneg g hg hA hB) (add_nonneg (atom1712Coded_nonneg g hg hA hB) (atom1713Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1714Coded_nonneg g hg hA hB) (atom1715Coded_nonneg g hg hA hB)) (add_nonneg (atom1716Coded_nonneg g hg hA hB) (add_nonneg (atom1717Coded_nonneg g hg hA hB) (atom1718Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1719Coded_nonneg g hg hA hB) (atom1720Coded_nonneg g hg hA hB)) (add_nonneg (atom1721Coded_nonneg g hg hA hB) (add_nonneg (atom1722Coded_nonneg g hg hA hB) (atom1723Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1724Coded_nonneg g hg hA hB) (atom1725Coded_nonneg g hg hA hB)) (add_nonneg (atom1726Coded_nonneg g hg hA hB) (add_nonneg (atom1727Coded_nonneg g hg hA hB) (atom1728Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
