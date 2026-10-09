import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1649 : SparsePolynomial.Poly := [([6,8,9], 1)]
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
def atom1649Coded : CoefficientMerge.Poly := [(3657, 1)]
theorem atom1649Coded_decode : atom1649 = SparsePolynomial.decodeCubic 24 atom1649Coded := by decide +kernel
theorem atom1649Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) := by
  have h := atom1649_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1649Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1650 : SparsePolynomial.Poly := [([6,8,13], 1)]
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
def atom1650Coded : CoefficientMerge.Poly := [(3661, 1)]
theorem atom1650Coded_decode : atom1650 = SparsePolynomial.decodeCubic 24 atom1650Coded := by decide +kernel
theorem atom1650Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded) := by
  have h := atom1650_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1650Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1651 : SparsePolynomial.Poly := [([6,8,14], 1)]
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
def atom1651Coded : CoefficientMerge.Poly := [(3662, 1)]
theorem atom1651Coded_decode : atom1651 = SparsePolynomial.decodeCubic 24 atom1651Coded := by decide +kernel
theorem atom1651Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) := by
  have h := atom1651_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1651Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1652 : SparsePolynomial.Poly := [([6,8,15], 1)]
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
def atom1652Coded : CoefficientMerge.Poly := [(3663, 1)]
theorem atom1652Coded_decode : atom1652 = SparsePolynomial.decodeCubic 24 atom1652Coded := by decide +kernel
theorem atom1652Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) := by
  have h := atom1652_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1652Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1653 : SparsePolynomial.Poly := [([6,8,16], 1)]
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
def atom1653Coded : CoefficientMerge.Poly := [(3664, 1)]
theorem atom1653Coded_decode : atom1653 = SparsePolynomial.decodeCubic 24 atom1653Coded := by decide +kernel
theorem atom1653Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded) := by
  have h := atom1653_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1653Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1654 : SparsePolynomial.Poly := [([6,8,17], 1)]
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
def atom1654Coded : CoefficientMerge.Poly := [(3665, 1)]
theorem atom1654Coded_decode : atom1654 = SparsePolynomial.decodeCubic 24 atom1654Coded := by decide +kernel
theorem atom1654Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) := by
  have h := atom1654_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1654Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1655 : SparsePolynomial.Poly := [([6,8,18], 1)]
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
def atom1655Coded : CoefficientMerge.Poly := [(3666, 1)]
theorem atom1655Coded_decode : atom1655 = SparsePolynomial.decodeCubic 24 atom1655Coded := by decide +kernel
theorem atom1655Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded) := by
  have h := atom1655_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1655Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1656 : SparsePolynomial.Poly := [([6,8,19], 1)]
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
def atom1656Coded : CoefficientMerge.Poly := [(3667, 1)]
theorem atom1656Coded_decode : atom1656 = SparsePolynomial.decodeCubic 24 atom1656Coded := by decide +kernel
theorem atom1656Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) := by
  have h := atom1656_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1656Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1657 : SparsePolynomial.Poly := [([6,8,20], 1)]
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
def atom1657Coded : CoefficientMerge.Poly := [(3668, 1)]
theorem atom1657Coded_decode : atom1657 = SparsePolynomial.decodeCubic 24 atom1657Coded := by decide +kernel
theorem atom1657Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) := by
  have h := atom1657_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1657Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1658 : SparsePolynomial.Poly := [([6,8,21], 1)]
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
def atom1658Coded : CoefficientMerge.Poly := [(3669, 1)]
theorem atom1658Coded_decode : atom1658 = SparsePolynomial.decodeCubic 24 atom1658Coded := by decide +kernel
theorem atom1658Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded) := by
  have h := atom1658_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1658Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1659 : SparsePolynomial.Poly := [([6,8,22], 1)]
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
def atom1659Coded : CoefficientMerge.Poly := [(3670, 1)]
theorem atom1659Coded_decode : atom1659 = SparsePolynomial.decodeCubic 24 atom1659Coded := by decide +kernel
theorem atom1659Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) := by
  have h := atom1659_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1659Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1660 : SparsePolynomial.Poly := [([6,8,23], 1)]
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
def atom1660Coded : CoefficientMerge.Poly := [(3671, 1)]
theorem atom1660Coded_decode : atom1660 = SparsePolynomial.decodeCubic 24 atom1660Coded := by decide +kernel
theorem atom1660Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded) := by
  have h := atom1660_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1660Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1661 : SparsePolynomial.Poly := [([6,9,9], 1)]
theorem eval_atom1661 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1661 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom1661, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1661_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31293969260400 : Int) atom1661) := by
  rw [SparsePolynomial.eval_scale, eval_atom1661]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1661Coded : CoefficientMerge.Poly := [(3681, 1)]
theorem atom1661Coded_decode : atom1661 = SparsePolynomial.decodeCubic 24 atom1661Coded := by decide +kernel
theorem atom1661Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) := by
  have h := atom1661_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1661Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1662 : SparsePolynomial.Poly := [([6,9,10], 1)]
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
def atom1662Coded : CoefficientMerge.Poly := [(3682, 1)]
theorem atom1662Coded_decode : atom1662 = SparsePolynomial.decodeCubic 24 atom1662Coded := by decide +kernel
theorem atom1662Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) := by
  have h := atom1662_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1662Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1663 : SparsePolynomial.Poly := [([6,9,11], 1)]
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
def atom1663Coded : CoefficientMerge.Poly := [(3683, 1)]
theorem atom1663Coded_decode : atom1663 = SparsePolynomial.decodeCubic 24 atom1663Coded := by decide +kernel
theorem atom1663Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded) := by
  have h := atom1663_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1663Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1664 : SparsePolynomial.Poly := [([6,9,12], 1)]
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
def atom1664Coded : CoefficientMerge.Poly := [(3684, 1)]
theorem atom1664Coded_decode : atom1664 = SparsePolynomial.decodeCubic 24 atom1664Coded := by decide +kernel
theorem atom1664Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) := by
  have h := atom1664_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1664Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1665 : SparsePolynomial.Poly := [([6,9,13], 1)]
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
def atom1665Coded : CoefficientMerge.Poly := [(3685, 1)]
theorem atom1665Coded_decode : atom1665 = SparsePolynomial.decodeCubic 24 atom1665Coded := by decide +kernel
theorem atom1665Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded) := by
  have h := atom1665_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1665Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1666 : SparsePolynomial.Poly := [([6,9,14], 1)]
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
def atom1666Coded : CoefficientMerge.Poly := [(3686, 1)]
theorem atom1666Coded_decode : atom1666 = SparsePolynomial.decodeCubic 24 atom1666Coded := by decide +kernel
theorem atom1666Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) := by
  have h := atom1666_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1666Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1667 : SparsePolynomial.Poly := [([6,9,15], 1)]
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
def atom1667Coded : CoefficientMerge.Poly := [(3687, 1)]
theorem atom1667Coded_decode : atom1667 = SparsePolynomial.decodeCubic 24 atom1667Coded := by decide +kernel
theorem atom1667Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) := by
  have h := atom1667_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1667Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1668 : SparsePolynomial.Poly := [([6,9,16], 1)]
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
def atom1668Coded : CoefficientMerge.Poly := [(3688, 1)]
theorem atom1668Coded_decode : atom1668 = SparsePolynomial.decodeCubic 24 atom1668Coded := by decide +kernel
theorem atom1668Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded) := by
  have h := atom1668_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1668Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1669 : SparsePolynomial.Poly := [([6,9,17], 1)]
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
def atom1669Coded : CoefficientMerge.Poly := [(3689, 1)]
theorem atom1669Coded_decode : atom1669 = SparsePolynomial.decodeCubic 24 atom1669Coded := by decide +kernel
theorem atom1669Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) := by
  have h := atom1669_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1669Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1670 : SparsePolynomial.Poly := [([6,9,18], 1)]
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
def atom1670Coded : CoefficientMerge.Poly := [(3690, 1)]
theorem atom1670Coded_decode : atom1670 = SparsePolynomial.decodeCubic 24 atom1670Coded := by decide +kernel
theorem atom1670Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded) := by
  have h := atom1670_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1670Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1671 : SparsePolynomial.Poly := [([6,9,19], 1)]
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
def atom1671Coded : CoefficientMerge.Poly := [(3691, 1)]
theorem atom1671Coded_decode : atom1671 = SparsePolynomial.decodeCubic 24 atom1671Coded := by decide +kernel
theorem atom1671Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) := by
  have h := atom1671_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1671Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1672 : SparsePolynomial.Poly := [([6,9,20], 1)]
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
def atom1672Coded : CoefficientMerge.Poly := [(3692, 1)]
theorem atom1672Coded_decode : atom1672 = SparsePolynomial.decodeCubic 24 atom1672Coded := by decide +kernel
theorem atom1672Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) := by
  have h := atom1672_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1672Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1673 : SparsePolynomial.Poly := [([6,9,21], 1)]
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
def atom1673Coded : CoefficientMerge.Poly := [(3693, 1)]
theorem atom1673Coded_decode : atom1673 = SparsePolynomial.decodeCubic 24 atom1673Coded := by decide +kernel
theorem atom1673Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded) := by
  have h := atom1673_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1673Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1674 : SparsePolynomial.Poly := [([6,9,22], 1)]
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
def atom1674Coded : CoefficientMerge.Poly := [(3694, 1)]
theorem atom1674Coded_decode : atom1674 = SparsePolynomial.decodeCubic 24 atom1674Coded := by decide +kernel
theorem atom1674Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) := by
  have h := atom1674_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1674Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1675 : SparsePolynomial.Poly := [([6,9,23], 1)]
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
def atom1675Coded : CoefficientMerge.Poly := [(3695, 1)]
theorem atom1675Coded_decode : atom1675 = SparsePolynomial.decodeCubic 24 atom1675Coded := by decide +kernel
theorem atom1675Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded) := by
  have h := atom1675_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1675Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1676 : SparsePolynomial.Poly := [([6,10,10], 1)]
theorem eval_atom1676 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1676 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom1676, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1676_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41144504117904 : Int) atom1676) := by
  rw [SparsePolynomial.eval_scale, eval_atom1676]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1676Coded : CoefficientMerge.Poly := [(3706, 1)]
theorem atom1676Coded_decode : atom1676 = SparsePolynomial.decodeCubic 24 atom1676Coded := by decide +kernel
theorem atom1676Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) := by
  have h := atom1676_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1676Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1677 : SparsePolynomial.Poly := [([6,10,11], 1)]
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
def atom1677Coded : CoefficientMerge.Poly := [(3707, 1)]
theorem atom1677Coded_decode : atom1677 = SparsePolynomial.decodeCubic 24 atom1677Coded := by decide +kernel
theorem atom1677Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) := by
  have h := atom1677_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1677Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1678 : SparsePolynomial.Poly := [([6,10,12], 1)]
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
def atom1678Coded : CoefficientMerge.Poly := [(3708, 1)]
theorem atom1678Coded_decode : atom1678 = SparsePolynomial.decodeCubic 24 atom1678Coded := by decide +kernel
theorem atom1678Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded) := by
  have h := atom1678_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1678Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1679 : SparsePolynomial.Poly := [([6,10,13], 1)]
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
def atom1679Coded : CoefficientMerge.Poly := [(3709, 1)]
theorem atom1679Coded_decode : atom1679 = SparsePolynomial.decodeCubic 24 atom1679Coded := by decide +kernel
theorem atom1679Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) := by
  have h := atom1679_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1679Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1680 : SparsePolynomial.Poly := [([6,10,14], 1)]
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
def atom1680Coded : CoefficientMerge.Poly := [(3710, 1)]
theorem atom1680Coded_decode : atom1680 = SparsePolynomial.decodeCubic 24 atom1680Coded := by decide +kernel
theorem atom1680Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded) := by
  have h := atom1680_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1680Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1681 : SparsePolynomial.Poly := [([6,10,15], 1)]
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
def atom1681Coded : CoefficientMerge.Poly := [(3711, 1)]
theorem atom1681Coded_decode : atom1681 = SparsePolynomial.decodeCubic 24 atom1681Coded := by decide +kernel
theorem atom1681Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) := by
  have h := atom1681_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1681Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1682 : SparsePolynomial.Poly := [([6,10,16], 1)]
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
def atom1682Coded : CoefficientMerge.Poly := [(3712, 1)]
theorem atom1682Coded_decode : atom1682 = SparsePolynomial.decodeCubic 24 atom1682Coded := by decide +kernel
theorem atom1682Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) := by
  have h := atom1682_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1682Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1683 : SparsePolynomial.Poly := [([6,10,17], 1)]
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
def atom1683Coded : CoefficientMerge.Poly := [(3713, 1)]
theorem atom1683Coded_decode : atom1683 = SparsePolynomial.decodeCubic 24 atom1683Coded := by decide +kernel
theorem atom1683Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded) := by
  have h := atom1683_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1683Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1684 : SparsePolynomial.Poly := [([6,10,18], 1)]
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
def atom1684Coded : CoefficientMerge.Poly := [(3714, 1)]
theorem atom1684Coded_decode : atom1684 = SparsePolynomial.decodeCubic 24 atom1684Coded := by decide +kernel
theorem atom1684Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) := by
  have h := atom1684_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1684Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1685 : SparsePolynomial.Poly := [([6,10,19], 1)]
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
def atom1685Coded : CoefficientMerge.Poly := [(3715, 1)]
theorem atom1685Coded_decode : atom1685 = SparsePolynomial.decodeCubic 24 atom1685Coded := by decide +kernel
theorem atom1685Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded) := by
  have h := atom1685_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1685Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1686 : SparsePolynomial.Poly := [([6,10,20], 1)]
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
def atom1686Coded : CoefficientMerge.Poly := [(3716, 1)]
theorem atom1686Coded_decode : atom1686 = SparsePolynomial.decodeCubic 24 atom1686Coded := by decide +kernel
theorem atom1686Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) := by
  have h := atom1686_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1686Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1687 : SparsePolynomial.Poly := [([6,10,21], 1)]
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
def atom1687Coded : CoefficientMerge.Poly := [(3717, 1)]
theorem atom1687Coded_decode : atom1687 = SparsePolynomial.decodeCubic 24 atom1687Coded := by decide +kernel
theorem atom1687Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) := by
  have h := atom1687_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1687Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1688 : SparsePolynomial.Poly := [([6,10,22], 1)]
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
def atom1688Coded : CoefficientMerge.Poly := [(3718, 1)]
theorem atom1688Coded_decode : atom1688 = SparsePolynomial.decodeCubic 24 atom1688Coded := by decide +kernel
theorem atom1688Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded) := by
  have h := atom1688_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1688Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1689 : SparsePolynomial.Poly := [([6,10,23], 1)]
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
def atom1689Coded : CoefficientMerge.Poly := [(3719, 1)]
theorem atom1689Coded_decode : atom1689 = SparsePolynomial.decodeCubic 24 atom1689Coded := by decide +kernel
theorem atom1689Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) := by
  have h := atom1689_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1689Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1690 : SparsePolynomial.Poly := [([6,11,11], 1)]
theorem eval_atom1690 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1690 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom1690, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1690_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62307098330400 : Int) atom1690) := by
  rw [SparsePolynomial.eval_scale, eval_atom1690]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1690Coded : CoefficientMerge.Poly := [(3731, 1)]
theorem atom1690Coded_decode : atom1690 = SparsePolynomial.decodeCubic 24 atom1690Coded := by decide +kernel
theorem atom1690Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded) := by
  have h := atom1690_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1690Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1691 : SparsePolynomial.Poly := [([6,11,12], 1)]
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
def atom1691Coded : CoefficientMerge.Poly := [(3732, 1)]
theorem atom1691Coded_decode : atom1691 = SparsePolynomial.decodeCubic 24 atom1691Coded := by decide +kernel
theorem atom1691Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) := by
  have h := atom1691_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1691Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1692 : SparsePolynomial.Poly := [([6,11,13], 1)]
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
def atom1692Coded : CoefficientMerge.Poly := [(3733, 1)]
theorem atom1692Coded_decode : atom1692 = SparsePolynomial.decodeCubic 24 atom1692Coded := by decide +kernel
theorem atom1692Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) := by
  have h := atom1692_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1692Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1693 : SparsePolynomial.Poly := [([6,11,14], 1)]
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
def atom1693Coded : CoefficientMerge.Poly := [(3734, 1)]
theorem atom1693Coded_decode : atom1693 = SparsePolynomial.decodeCubic 24 atom1693Coded := by decide +kernel
theorem atom1693Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded) := by
  have h := atom1693_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1693Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1694 : SparsePolynomial.Poly := [([6,11,15], 1)]
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
def atom1694Coded : CoefficientMerge.Poly := [(3735, 1)]
theorem atom1694Coded_decode : atom1694 = SparsePolynomial.decodeCubic 24 atom1694Coded := by decide +kernel
theorem atom1694Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) := by
  have h := atom1694_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1694Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1695 : SparsePolynomial.Poly := [([6,11,16], 1)]
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
def atom1695Coded : CoefficientMerge.Poly := [(3736, 1)]
theorem atom1695Coded_decode : atom1695 = SparsePolynomial.decodeCubic 24 atom1695Coded := by decide +kernel
theorem atom1695Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded) := by
  have h := atom1695_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1695Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1696 : SparsePolynomial.Poly := [([6,11,17], 1)]
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
def atom1696Coded : CoefficientMerge.Poly := [(3737, 1)]
theorem atom1696Coded_decode : atom1696 = SparsePolynomial.decodeCubic 24 atom1696Coded := by decide +kernel
theorem atom1696Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) := by
  have h := atom1696_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1696Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1697 : SparsePolynomial.Poly := [([6,11,18], 1)]
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
def atom1697Coded : CoefficientMerge.Poly := [(3738, 1)]
theorem atom1697Coded_decode : atom1697 = SparsePolynomial.decodeCubic 24 atom1697Coded := by decide +kernel
theorem atom1697Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) := by
  have h := atom1697_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1697Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1698 : SparsePolynomial.Poly := [([6,11,19], 1)]
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
def atom1698Coded : CoefficientMerge.Poly := [(3739, 1)]
theorem atom1698Coded_decode : atom1698 = SparsePolynomial.decodeCubic 24 atom1698Coded := by decide +kernel
theorem atom1698Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded) := by
  have h := atom1698_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1698Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1699 : SparsePolynomial.Poly := [([6,11,20], 1)]
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
def atom1699Coded : CoefficientMerge.Poly := [(3740, 1)]
theorem atom1699Coded_decode : atom1699 = SparsePolynomial.decodeCubic 24 atom1699Coded := by decide +kernel
theorem atom1699Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) := by
  have h := atom1699_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1699Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1700 : SparsePolynomial.Poly := [([6,11,21], 1)]
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
def atom1700Coded : CoefficientMerge.Poly := [(3741, 1)]
theorem atom1700Coded_decode : atom1700 = SparsePolynomial.decodeCubic 24 atom1700Coded := by decide +kernel
theorem atom1700Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded) := by
  have h := atom1700_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1700Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1701 : SparsePolynomial.Poly := [([6,11,22], 1)]
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
def atom1701Coded : CoefficientMerge.Poly := [(3742, 1)]
theorem atom1701Coded_decode : atom1701 = SparsePolynomial.decodeCubic 24 atom1701Coded := by decide +kernel
theorem atom1701Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) := by
  have h := atom1701_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1701Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1702 : SparsePolynomial.Poly := [([6,11,23], 1)]
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
def atom1702Coded : CoefficientMerge.Poly := [(3743, 1)]
theorem atom1702Coded_decode : atom1702 = SparsePolynomial.decodeCubic 24 atom1702Coded := by decide +kernel
theorem atom1702Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) := by
  have h := atom1702_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1702Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1703 : SparsePolynomial.Poly := [([6,12,12], 1)]
theorem eval_atom1703 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1703 = ((g 6) * (g 12) * (g 12)) := by
  norm_num [atom1703, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1703_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77526953380800 : Int) atom1703) := by
  rw [SparsePolynomial.eval_scale, eval_atom1703]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1703Coded : CoefficientMerge.Poly := [(3756, 1)]
theorem atom1703Coded_decode : atom1703 = SparsePolynomial.decodeCubic 24 atom1703Coded := by decide +kernel
theorem atom1703Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded) := by
  have h := atom1703_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1703Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1704 : SparsePolynomial.Poly := [([6,12,13], 1)]
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
def atom1704Coded : CoefficientMerge.Poly := [(3757, 1)]
theorem atom1704Coded_decode : atom1704 = SparsePolynomial.decodeCubic 24 atom1704Coded := by decide +kernel
theorem atom1704Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) := by
  have h := atom1704_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1704Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1705 : SparsePolynomial.Poly := [([6,12,14], 1)]
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
def atom1705Coded : CoefficientMerge.Poly := [(3758, 1)]
theorem atom1705Coded_decode : atom1705 = SparsePolynomial.decodeCubic 24 atom1705Coded := by decide +kernel
theorem atom1705Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded) := by
  have h := atom1705_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1705Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1706 : SparsePolynomial.Poly := [([6,12,15], 1)]
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
def atom1706Coded : CoefficientMerge.Poly := [(3759, 1)]
theorem atom1706Coded_decode : atom1706 = SparsePolynomial.decodeCubic 24 atom1706Coded := by decide +kernel
theorem atom1706Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) := by
  have h := atom1706_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1706Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1707 : SparsePolynomial.Poly := [([6,12,16], 1)]
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
def atom1707Coded : CoefficientMerge.Poly := [(3760, 1)]
theorem atom1707Coded_decode : atom1707 = SparsePolynomial.decodeCubic 24 atom1707Coded := by decide +kernel
theorem atom1707Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) := by
  have h := atom1707_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1707Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1708 : SparsePolynomial.Poly := [([6,12,17], 1)]
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
def atom1708Coded : CoefficientMerge.Poly := [(3761, 1)]
theorem atom1708Coded_decode : atom1708 = SparsePolynomial.decodeCubic 24 atom1708Coded := by decide +kernel
theorem atom1708Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded) := by
  have h := atom1708_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1708Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1709 : SparsePolynomial.Poly := [([6,12,18], 1)]
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
def atom1709Coded : CoefficientMerge.Poly := [(3762, 1)]
theorem atom1709Coded_decode : atom1709 = SparsePolynomial.decodeCubic 24 atom1709Coded := by decide +kernel
theorem atom1709Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) := by
  have h := atom1709_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1709Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1710 : SparsePolynomial.Poly := [([6,12,19], 1)]
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
def atom1710Coded : CoefficientMerge.Poly := [(3763, 1)]
theorem atom1710Coded_decode : atom1710 = SparsePolynomial.decodeCubic 24 atom1710Coded := by decide +kernel
theorem atom1710Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded) := by
  have h := atom1710_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1710Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1711 : SparsePolynomial.Poly := [([6,12,20], 1)]
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
def atom1711Coded : CoefficientMerge.Poly := [(3764, 1)]
theorem atom1711Coded_decode : atom1711 = SparsePolynomial.decodeCubic 24 atom1711Coded := by decide +kernel
theorem atom1711Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) := by
  have h := atom1711_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1711Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1712 : SparsePolynomial.Poly := [([6,12,21], 1)]
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
def atom1712Coded : CoefficientMerge.Poly := [(3765, 1)]
theorem atom1712Coded_decode : atom1712 = SparsePolynomial.decodeCubic 24 atom1712Coded := by decide +kernel
theorem atom1712Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) := by
  have h := atom1712_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1712Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1713 : SparsePolynomial.Poly := [([6,12,22], 1)]
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
def atom1713Coded : CoefficientMerge.Poly := [(3766, 1)]
theorem atom1713Coded_decode : atom1713 = SparsePolynomial.decodeCubic 24 atom1713Coded := by decide +kernel
theorem atom1713Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded) := by
  have h := atom1713_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1713Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1714 : SparsePolynomial.Poly := [([6,12,23], 1)]
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
def atom1714Coded : CoefficientMerge.Poly := [(3767, 1)]
theorem atom1714Coded_decode : atom1714 = SparsePolynomial.decodeCubic 24 atom1714Coded := by decide +kernel
theorem atom1714Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) := by
  have h := atom1714_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1714Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1715 : SparsePolynomial.Poly := [([6,13,13], 1)]
theorem eval_atom1715 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1715 = ((g 6) * (g 13) * (g 13)) := by
  norm_num [atom1715, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1715_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103836452227200 : Int) atom1715) := by
  rw [SparsePolynomial.eval_scale, eval_atom1715]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1715Coded : CoefficientMerge.Poly := [(3781, 1)]
theorem atom1715Coded_decode : atom1715 = SparsePolynomial.decodeCubic 24 atom1715Coded := by decide +kernel
theorem atom1715Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded) := by
  have h := atom1715_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1715Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1716 : SparsePolynomial.Poly := [([6,13,14], 1)]
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
def atom1716Coded : CoefficientMerge.Poly := [(3782, 1)]
theorem atom1716Coded_decode : atom1716 = SparsePolynomial.decodeCubic 24 atom1716Coded := by decide +kernel
theorem atom1716Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) := by
  have h := atom1716_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1716Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1717 : SparsePolynomial.Poly := [([6,13,15], 1)]
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
def atom1717Coded : CoefficientMerge.Poly := [(3783, 1)]
theorem atom1717Coded_decode : atom1717 = SparsePolynomial.decodeCubic 24 atom1717Coded := by decide +kernel
theorem atom1717Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) := by
  have h := atom1717_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1717Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1718 : SparsePolynomial.Poly := [([6,13,16], 1)]
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
def atom1718Coded : CoefficientMerge.Poly := [(3784, 1)]
theorem atom1718Coded_decode : atom1718 = SparsePolynomial.decodeCubic 24 atom1718Coded := by decide +kernel
theorem atom1718Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded) := by
  have h := atom1718_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1718Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1719 : SparsePolynomial.Poly := [([6,13,17], 1)]
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
def atom1719Coded : CoefficientMerge.Poly := [(3785, 1)]
theorem atom1719Coded_decode : atom1719 = SparsePolynomial.decodeCubic 24 atom1719Coded := by decide +kernel
theorem atom1719Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) := by
  have h := atom1719_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1719Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1720 : SparsePolynomial.Poly := [([6,13,18], 1)]
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
def atom1720Coded : CoefficientMerge.Poly := [(3786, 1)]
theorem atom1720Coded_decode : atom1720 = SparsePolynomial.decodeCubic 24 atom1720Coded := by decide +kernel
theorem atom1720Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded) := by
  have h := atom1720_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1720Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1721 : SparsePolynomial.Poly := [([6,13,19], 1)]
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
def atom1721Coded : CoefficientMerge.Poly := [(3787, 1)]
theorem atom1721Coded_decode : atom1721 = SparsePolynomial.decodeCubic 24 atom1721Coded := by decide +kernel
theorem atom1721Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) := by
  have h := atom1721_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1721Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1722 : SparsePolynomial.Poly := [([6,13,20], 1)]
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
def atom1722Coded : CoefficientMerge.Poly := [(3788, 1)]
theorem atom1722Coded_decode : atom1722 = SparsePolynomial.decodeCubic 24 atom1722Coded := by decide +kernel
theorem atom1722Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) := by
  have h := atom1722_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1722Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1723 : SparsePolynomial.Poly := [([6,13,21], 1)]
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
def atom1723Coded : CoefficientMerge.Poly := [(3789, 1)]
theorem atom1723Coded_decode : atom1723 = SparsePolynomial.decodeCubic 24 atom1723Coded := by decide +kernel
theorem atom1723Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded) := by
  have h := atom1723_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1723Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1724 : SparsePolynomial.Poly := [([6,13,22], 1)]
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
def atom1724Coded : CoefficientMerge.Poly := [(3790, 1)]
theorem atom1724Coded_decode : atom1724 = SparsePolynomial.decodeCubic 24 atom1724Coded := by decide +kernel
theorem atom1724Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) := by
  have h := atom1724_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1724Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1725 : SparsePolynomial.Poly := [([6,13,23], 1)]
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
def atom1725Coded : CoefficientMerge.Poly := [(3791, 1)]
theorem atom1725Coded_decode : atom1725 = SparsePolynomial.decodeCubic 24 atom1725Coded := by decide +kernel
theorem atom1725Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded) := by
  have h := atom1725_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1725Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1726 : SparsePolynomial.Poly := [([6,14,14], 1)]
theorem eval_atom1726 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1726 = ((g 6) * (g 14) * (g 14)) := by
  norm_num [atom1726, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1726_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126592481030400 : Int) atom1726) := by
  rw [SparsePolynomial.eval_scale, eval_atom1726]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1726Coded : CoefficientMerge.Poly := [(3806, 1)]
theorem atom1726Coded_decode : atom1726 = SparsePolynomial.decodeCubic 24 atom1726Coded := by decide +kernel
theorem atom1726Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) := by
  have h := atom1726_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1726Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1727 : SparsePolynomial.Poly := [([6,14,15], 1)]
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
def atom1727Coded : CoefficientMerge.Poly := [(3807, 1)]
theorem atom1727Coded_decode : atom1727 = SparsePolynomial.decodeCubic 24 atom1727Coded := by decide +kernel
theorem atom1727Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) := by
  have h := atom1727_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1727Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1728 : SparsePolynomial.Poly := [([6,14,16], 1)]
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
def atom1728Coded : CoefficientMerge.Poly := [(3808, 1)]
theorem atom1728Coded_decode : atom1728 = SparsePolynomial.decodeCubic 24 atom1728Coded := by decide +kernel
theorem atom1728Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded) := by
  have h := atom1728_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1728Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block023 : CoefficientMerge.Poly := [(3657, 19897350303600), (3661, 5145488409600), (3662, 10290976819200), (3663, 15436465228800), (3664, 20581953638400), (3665, 25727442048000), (3666, 11587980096000), (3667, 19816509081600), (3668, 28045038067200), (3669, 101836019577600), (3670, 175627001088000), (3671, 259831217923200), (3681, 31293969260400), (3682, 43670515451904), (3683, 22669871994000), (3684, 26794767661200), (3685, 29899070586000), (3686, 36086414086800), (3687, 42273757587600), (3688, 48461101088400), (3689, 54648444589200), (3690, 47823313522248), (3691, 65569641223680), (3692, 83315968925112), (3693, 168997180831380), (3694, 254678392737648), (3695, 349755587977950), (3706, 41144504117904), (3707, 68517563369904), (3708, 69580680809904), (3709, 75789286659504), (3710, 81997892509104), (3711, 88206498358704), (3712, 94415104208304), (3713, 100623710057904), (3714, 99978636340440), (3715, 122637785402880), (3716, 145296934465320), (3717, 229643480261052), (3718, 313990026056784), (3719, 405876047439258), (3731, 62307098330400), (3732, 104900012632800), (3733, 107026247512800), (3734, 109152482392800), (3735, 111278717272800), (3736, 116487992728800), (3737, 121697268184800), (3738, 142977134375856), (3739, 164808313021440), (3740, 208556285438160), (3741, 289029266970840), (3742, 379790294156064), (3743, 475393062860100), (3756, 77526953380800), (3757, 146429366529600), (3758, 149618718849600), (3759, 152808071169600), (3760, 155997423489600), (3761, 159186775809600), (3762, 219028702232736), (3763, 218857203671040), (3764, 328731745304160), (3765, 342942277922640), (3766, 426827127950784), (3767, 511824270295800), (3781, 103836452227200), (3782, 195494894179200), (3783, 192560690044800), (3784, 192709526486400), (3785, 192858362928000), (3786, 241236824875200), (3787, 242826237561600), (3788, 356418199368000), (3789, 364599695829600), (3790, 450159465571200), (3791, 537932773501200), (3806, 126592481030400), (3807, 241054792070400), (3808, 237142519891200)]
theorem block023_data : block023 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19897350303600 : Int) atom1649Coded) (CoefficientMerge.scale (5145488409600 : Int) atom1650Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10290976819200 : Int) atom1651Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15436465228800 : Int) atom1652Coded) (CoefficientMerge.scale (20581953638400 : Int) atom1653Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25727442048000 : Int) atom1654Coded) (CoefficientMerge.scale (11587980096000 : Int) atom1655Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19816509081600 : Int) atom1656Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28045038067200 : Int) atom1657Coded) (CoefficientMerge.scale (101836019577600 : Int) atom1658Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (175627001088000 : Int) atom1659Coded) (CoefficientMerge.scale (259831217923200 : Int) atom1660Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31293969260400 : Int) atom1661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43670515451904 : Int) atom1662Coded) (CoefficientMerge.scale (22669871994000 : Int) atom1663Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26794767661200 : Int) atom1664Coded) (CoefficientMerge.scale (29899070586000 : Int) atom1665Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36086414086800 : Int) atom1666Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42273757587600 : Int) atom1667Coded) (CoefficientMerge.scale (48461101088400 : Int) atom1668Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (54648444589200 : Int) atom1669Coded) (CoefficientMerge.scale (47823313522248 : Int) atom1670Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65569641223680 : Int) atom1671Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83315968925112 : Int) atom1672Coded) (CoefficientMerge.scale (168997180831380 : Int) atom1673Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (254678392737648 : Int) atom1674Coded) (CoefficientMerge.scale (349755587977950 : Int) atom1675Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41144504117904 : Int) atom1676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517563369904 : Int) atom1677Coded) (CoefficientMerge.scale (69580680809904 : Int) atom1678Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75789286659504 : Int) atom1679Coded) (CoefficientMerge.scale (81997892509104 : Int) atom1680Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (88206498358704 : Int) atom1681Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94415104208304 : Int) atom1682Coded) (CoefficientMerge.scale (100623710057904 : Int) atom1683Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (99978636340440 : Int) atom1684Coded) (CoefficientMerge.scale (122637785402880 : Int) atom1685Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145296934465320 : Int) atom1686Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (229643480261052 : Int) atom1687Coded) (CoefficientMerge.scale (313990026056784 : Int) atom1688Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (405876047439258 : Int) atom1689Coded) (CoefficientMerge.scale (62307098330400 : Int) atom1690Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104900012632800 : Int) atom1691Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107026247512800 : Int) atom1692Coded) (CoefficientMerge.scale (109152482392800 : Int) atom1693Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (111278717272800 : Int) atom1694Coded) (CoefficientMerge.scale (116487992728800 : Int) atom1695Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121697268184800 : Int) atom1696Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142977134375856 : Int) atom1697Coded) (CoefficientMerge.scale (164808313021440 : Int) atom1698Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (208556285438160 : Int) atom1699Coded) (CoefficientMerge.scale (289029266970840 : Int) atom1700Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (379790294156064 : Int) atom1701Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475393062860100 : Int) atom1702Coded) (CoefficientMerge.scale (77526953380800 : Int) atom1703Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (146429366529600 : Int) atom1704Coded) (CoefficientMerge.scale (149618718849600 : Int) atom1705Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152808071169600 : Int) atom1706Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (155997423489600 : Int) atom1707Coded) (CoefficientMerge.scale (159186775809600 : Int) atom1708Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (219028702232736 : Int) atom1709Coded) (CoefficientMerge.scale (218857203671040 : Int) atom1710Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (328731745304160 : Int) atom1711Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (342942277922640 : Int) atom1712Coded) (CoefficientMerge.scale (426827127950784 : Int) atom1713Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (511824270295800 : Int) atom1714Coded) (CoefficientMerge.scale (103836452227200 : Int) atom1715Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195494894179200 : Int) atom1716Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (192560690044800 : Int) atom1717Coded) (CoefficientMerge.scale (192709526486400 : Int) atom1718Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (192858362928000 : Int) atom1719Coded) (CoefficientMerge.scale (241236824875200 : Int) atom1720Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (242826237561600 : Int) atom1721Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (356418199368000 : Int) atom1722Coded) (CoefficientMerge.scale (364599695829600 : Int) atom1723Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (450159465571200 : Int) atom1724Coded) (CoefficientMerge.scale (537932773501200 : Int) atom1725Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (126592481030400 : Int) atom1726Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241054792070400 : Int) atom1727Coded) (CoefficientMerge.scale (237142519891200 : Int) atom1728Coded)))))))) := by decide +kernel
theorem block023_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block023 := by
  rw [block023_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1649Coded_nonneg g hg hA hB) (atom1650Coded_nonneg g hg hA hB)) (add_nonneg (atom1651Coded_nonneg g hg hA hB) (add_nonneg (atom1652Coded_nonneg g hg hA hB) (atom1653Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1654Coded_nonneg g hg hA hB) (atom1655Coded_nonneg g hg hA hB)) (add_nonneg (atom1656Coded_nonneg g hg hA hB) (add_nonneg (atom1657Coded_nonneg g hg hA hB) (atom1658Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1659Coded_nonneg g hg hA hB) (atom1660Coded_nonneg g hg hA hB)) (add_nonneg (atom1661Coded_nonneg g hg hA hB) (add_nonneg (atom1662Coded_nonneg g hg hA hB) (atom1663Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1664Coded_nonneg g hg hA hB) (atom1665Coded_nonneg g hg hA hB)) (add_nonneg (atom1666Coded_nonneg g hg hA hB) (add_nonneg (atom1667Coded_nonneg g hg hA hB) (atom1668Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1669Coded_nonneg g hg hA hB) (atom1670Coded_nonneg g hg hA hB)) (add_nonneg (atom1671Coded_nonneg g hg hA hB) (add_nonneg (atom1672Coded_nonneg g hg hA hB) (atom1673Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1674Coded_nonneg g hg hA hB) (atom1675Coded_nonneg g hg hA hB)) (add_nonneg (atom1676Coded_nonneg g hg hA hB) (add_nonneg (atom1677Coded_nonneg g hg hA hB) (atom1678Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1679Coded_nonneg g hg hA hB) (atom1680Coded_nonneg g hg hA hB)) (add_nonneg (atom1681Coded_nonneg g hg hA hB) (add_nonneg (atom1682Coded_nonneg g hg hA hB) (atom1683Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1684Coded_nonneg g hg hA hB) (atom1685Coded_nonneg g hg hA hB)) (add_nonneg (atom1686Coded_nonneg g hg hA hB) (add_nonneg (atom1687Coded_nonneg g hg hA hB) (atom1688Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1689Coded_nonneg g hg hA hB) (atom1690Coded_nonneg g hg hA hB)) (add_nonneg (atom1691Coded_nonneg g hg hA hB) (add_nonneg (atom1692Coded_nonneg g hg hA hB) (atom1693Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1694Coded_nonneg g hg hA hB) (atom1695Coded_nonneg g hg hA hB)) (add_nonneg (atom1696Coded_nonneg g hg hA hB) (add_nonneg (atom1697Coded_nonneg g hg hA hB) (atom1698Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1699Coded_nonneg g hg hA hB) (atom1700Coded_nonneg g hg hA hB)) (add_nonneg (atom1701Coded_nonneg g hg hA hB) (add_nonneg (atom1702Coded_nonneg g hg hA hB) (atom1703Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1704Coded_nonneg g hg hA hB) (atom1705Coded_nonneg g hg hA hB)) (add_nonneg (atom1706Coded_nonneg g hg hA hB) (add_nonneg (atom1707Coded_nonneg g hg hA hB) (atom1708Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1709Coded_nonneg g hg hA hB) (atom1710Coded_nonneg g hg hA hB)) (add_nonneg (atom1711Coded_nonneg g hg hA hB) (add_nonneg (atom1712Coded_nonneg g hg hA hB) (atom1713Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1714Coded_nonneg g hg hA hB) (atom1715Coded_nonneg g hg hA hB)) (add_nonneg (atom1716Coded_nonneg g hg hA hB) (add_nonneg (atom1717Coded_nonneg g hg hA hB) (atom1718Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1719Coded_nonneg g hg hA hB) (atom1720Coded_nonneg g hg hA hB)) (add_nonneg (atom1721Coded_nonneg g hg hA hB) (add_nonneg (atom1722Coded_nonneg g hg hA hB) (atom1723Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1724Coded_nonneg g hg hA hB) (atom1725Coded_nonneg g hg hA hB)) (add_nonneg (atom1726Coded_nonneg g hg hA hB) (add_nonneg (atom1727Coded_nonneg g hg hA hB) (atom1728Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
