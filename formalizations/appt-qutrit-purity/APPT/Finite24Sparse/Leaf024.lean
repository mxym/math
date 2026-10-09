import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1729 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1729 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1729 = ((g 6) * (g 14) * (g 17)) := by
  norm_num [atom1729, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1729_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (233230247712000 : Int) atom1729) := by
  rw [SparsePolynomial.eval_scale, eval_atom1729]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1729Coded : CoefficientMerge.Poly := [(nat_lit 3809, Int.ofNat (nat_lit 1))]
theorem atom1729Coded_decode : atom1729 = SparsePolynomial.decodeCubic 24 atom1729Coded := by decide +kernel
theorem atom1729Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (233230247712000 : Int) atom1729Coded) := by
  have h := atom1729_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1729Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1730 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1730 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1730 = ((g 6) * (g 14) * (g 18)) := by
  norm_num [atom1730, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1730_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (257933553292800 : Int) atom1730) := by
  rw [SparsePolynomial.eval_scale, eval_atom1730]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1730Coded : CoefficientMerge.Poly := [(nat_lit 3810, Int.ofNat (nat_lit 1))]
theorem atom1730Coded_decode : atom1730 = SparsePolynomial.decodeCubic 24 atom1730Coded := by decide +kernel
theorem atom1730Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (257933553292800 : Int) atom1730Coded) := by
  have h := atom1730_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1730Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1731 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1731 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1731 = ((g 6) * (g 14) * (g 19)) := by
  norm_num [atom1731, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1731_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (265146362157600 : Int) atom1731) := by
  rw [SparsePolynomial.eval_scale, eval_atom1731]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1731Coded : CoefficientMerge.Poly := [(nat_lit 3811, Int.ofNat (nat_lit 1))]
theorem atom1731Coded_decode : atom1731 = SparsePolynomial.decodeCubic 24 atom1731Coded := by decide +kernel
theorem atom1731Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (265146362157600 : Int) atom1731Coded) := by
  have h := atom1731_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1731Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1732 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1732 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1732 = ((g 6) * (g 14) * (g 20)) := by
  norm_num [atom1732, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1732_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (374918996390400 : Int) atom1732) := by
  rw [SparsePolynomial.eval_scale, eval_atom1732]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1732Coded : CoefficientMerge.Poly := [(nat_lit 3812, Int.ofNat (nat_lit 1))]
theorem atom1732Coded_decode : atom1732 = SparsePolynomial.decodeCubic 24 atom1732Coded := by decide +kernel
theorem atom1732Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (374918996390400 : Int) atom1732Coded) := by
  have h := atom1732_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1732Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1733 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1733 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1733 = ((g 6) * (g 14) * (g 21)) := by
  norm_num [atom1733, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1733_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (387123584601600 : Int) atom1733) := by
  rw [SparsePolynomial.eval_scale, eval_atom1733]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1733Coded : CoefficientMerge.Poly := [(nat_lit 3813, Int.ofNat (nat_lit 1))]
theorem atom1733Coded_decode : atom1733 = SparsePolynomial.decodeCubic 24 atom1733Coded := by decide +kernel
theorem atom1733Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (387123584601600 : Int) atom1733Coded) := by
  have h := atom1733_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1733Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1734 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1734 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1734 = ((g 6) * (g 14) * (g 22)) := by
  norm_num [atom1734, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1734_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (456327657324000 : Int) atom1734) := by
  rw [SparsePolynomial.eval_scale, eval_atom1734]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1734Coded : CoefficientMerge.Poly := [(nat_lit 3814, Int.ofNat (nat_lit 1))]
theorem atom1734Coded_decode : atom1734 = SparsePolynomial.decodeCubic 24 atom1734Coded := by decide +kernel
theorem atom1734Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (456327657324000 : Int) atom1734Coded) := by
  have h := atom1734_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1734Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1735 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1735 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1735 = ((g 6) * (g 14) * (g 23)) := by
  norm_num [atom1735, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1735_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (541885577032800 : Int) atom1735) := by
  rw [SparsePolynomial.eval_scale, eval_atom1735]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1735Coded : CoefficientMerge.Poly := [(nat_lit 3815, Int.ofNat (nat_lit 1))]
theorem atom1735Coded_decode : atom1735 = SparsePolynomial.decodeCubic 24 atom1735Coded := by decide +kernel
theorem atom1735Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (541885577032800 : Int) atom1735Coded) := by
  have h := atom1735_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1735Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1736 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1736 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1736 = ((g 6) * (g 15) * (g 15)) := by
  norm_num [atom1736, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1736_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152479390694400 : Int) atom1736) := by
  rw [SparsePolynomial.eval_scale, eval_atom1736]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1736Coded : CoefficientMerge.Poly := [(nat_lit 3831, Int.ofNat (nat_lit 1))]
theorem atom1736Coded_decode : atom1736 = SparsePolynomial.decodeCubic 24 atom1736Coded := by decide +kernel
theorem atom1736Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (152479390694400 : Int) atom1736Coded) := by
  have h := atom1736_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1736Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1737 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1737 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1737 = ((g 6) * (g 15) * (g 16)) := by
  norm_num [atom1737, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1737_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (282612052800000 : Int) atom1737) := by
  rw [SparsePolynomial.eval_scale, eval_atom1737]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1737Coded : CoefficientMerge.Poly := [(nat_lit 3832, Int.ofNat (nat_lit 1))]
theorem atom1737Coded_decode : atom1737 = SparsePolynomial.decodeCubic 24 atom1737Coded := by decide +kernel
theorem atom1737Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (282612052800000 : Int) atom1737Coded) := by
  have h := atom1737_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1737Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1738 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1738 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1738 = ((g 6) * (g 15) * (g 17)) := by
  norm_num [atom1738, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1738_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (273618079257600 : Int) atom1738) := by
  rw [SparsePolynomial.eval_scale, eval_atom1738]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1738Coded : CoefficientMerge.Poly := [(nat_lit 3833, Int.ofNat (nat_lit 1))]
theorem atom1738Coded_decode : atom1738 = SparsePolynomial.decodeCubic 24 atom1738Coded := by decide +kernel
theorem atom1738Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (273618079257600 : Int) atom1738Coded) := by
  have h := atom1738_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1738Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1739 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1739 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1739 = ((g 6) * (g 15) * (g 18)) := by
  norm_num [atom1739, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1739_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (296810791603200 : Int) atom1739) := by
  rw [SparsePolynomial.eval_scale, eval_atom1739]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1739Coded : CoefficientMerge.Poly := [(nat_lit 3834, Int.ofNat (nat_lit 1))]
theorem atom1739Coded_decode : atom1739 = SparsePolynomial.decodeCubic 24 atom1739Coded := by decide +kernel
theorem atom1739Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (296810791603200 : Int) atom1739Coded) := by
  have h := atom1739_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1739Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1740 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1740 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1740 = ((g 6) * (g 15) * (g 19)) := by
  norm_num [atom1740, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1740_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (293178151526400 : Int) atom1740) := by
  rw [SparsePolynomial.eval_scale, eval_atom1740]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1740Coded : CoefficientMerge.Poly := [(nat_lit 3835, Int.ofNat (nat_lit 1))]
theorem atom1740Coded_decode : atom1740 = SparsePolynomial.decodeCubic 24 atom1740Coded := by decide +kernel
theorem atom1740Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (293178151526400 : Int) atom1740Coded) := by
  have h := atom1740_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1740Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1741 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1741 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1741 = ((g 6) * (g 15) * (g 20)) := by
  norm_num [atom1741, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1741_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (430387309900800 : Int) atom1741) := by
  rw [SparsePolynomial.eval_scale, eval_atom1741]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1741Coded : CoefficientMerge.Poly := [(nat_lit 3836, Int.ofNat (nat_lit 1))]
theorem atom1741Coded_decode : atom1741 = SparsePolynomial.decodeCubic 24 atom1741Coded := by decide +kernel
theorem atom1741Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (430387309900800 : Int) atom1741Coded) := by
  have h := atom1741_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1741Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1742 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1742 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1742 = ((g 6) * (g 15) * (g 21)) := by
  norm_num [atom1742, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1742_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (450311741510400 : Int) atom1742) := by
  rw [SparsePolynomial.eval_scale, eval_atom1742]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1742Coded : CoefficientMerge.Poly := [(nat_lit 3837, Int.ofNat (nat_lit 1))]
theorem atom1742Coded_decode : atom1742 = SparsePolynomial.decodeCubic 24 atom1742Coded := by decide +kernel
theorem atom1742Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (450311741510400 : Int) atom1742Coded) := by
  have h := atom1742_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1742Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1743 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1743 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1743 = ((g 6) * (g 15) * (g 22)) := by
  norm_num [atom1743, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1743_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (456432398553600 : Int) atom1743) := by
  rw [SparsePolynomial.eval_scale, eval_atom1743]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1743Coded : CoefficientMerge.Poly := [(nat_lit 3838, Int.ofNat (nat_lit 1))]
theorem atom1743Coded_decode : atom1743 = SparsePolynomial.decodeCubic 24 atom1743Coded := by decide +kernel
theorem atom1743Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (456432398553600 : Int) atom1743Coded) := by
  have h := atom1743_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1743Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1744 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1744 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1744 = ((g 6) * (g 15) * (g 23)) := by
  norm_num [atom1744, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1744_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (536413784054400 : Int) atom1744) := by
  rw [SparsePolynomial.eval_scale, eval_atom1744]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1744Coded : CoefficientMerge.Poly := [(nat_lit 3839, Int.ofNat (nat_lit 1))]
theorem atom1744Coded_decode : atom1744 = SparsePolynomial.decodeCubic 24 atom1744Coded := by decide +kernel
theorem atom1744Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (536413784054400 : Int) atom1744Coded) := by
  have h := atom1744_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1744Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1745 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1745 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1745 = ((g 6) * (g 16) * (g 16)) := by
  norm_num [atom1745, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1745_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171232782336000 : Int) atom1745) := by
  rw [SparsePolynomial.eval_scale, eval_atom1745]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1745Coded : CoefficientMerge.Poly := [(nat_lit 3856, Int.ofNat (nat_lit 1))]
theorem atom1745Coded_decode : atom1745 = SparsePolynomial.decodeCubic 24 atom1745Coded := by decide +kernel
theorem atom1745Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (171232782336000 : Int) atom1745Coded) := by
  have h := atom1745_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1745Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1746 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1746 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1746 = ((g 6) * (g 16) * (g 17)) := by
  norm_num [atom1746, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1746_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (324286256448000 : Int) atom1746) := by
  rw [SparsePolynomial.eval_scale, eval_atom1746]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1746Coded : CoefficientMerge.Poly := [(nat_lit 3857, Int.ofNat (nat_lit 1))]
theorem atom1746Coded_decode : atom1746 = SparsePolynomial.decodeCubic 24 atom1746Coded := by decide +kernel
theorem atom1746Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (324286256448000 : Int) atom1746Coded) := by
  have h := atom1746_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1746Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1747 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1747 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1747 = ((g 6) * (g 16) * (g 18)) := by
  norm_num [atom1747, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1747_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (317954264544000 : Int) atom1747) := by
  rw [SparsePolynomial.eval_scale, eval_atom1747]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1747Coded : CoefficientMerge.Poly := [(nat_lit 3858, Int.ofNat (nat_lit 1))]
theorem atom1747Coded_decode : atom1747 = SparsePolynomial.decodeCubic 24 atom1747Coded := by decide +kernel
theorem atom1747Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (317954264544000 : Int) atom1747Coded) := by
  have h := atom1747_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1747Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1748 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1748 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1748 = ((g 6) * (g 16) * (g 19)) := by
  norm_num [atom1748, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1748_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (316705906944000 : Int) atom1748) := by
  rw [SparsePolynomial.eval_scale, eval_atom1748]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1748Coded : CoefficientMerge.Poly := [(nat_lit 3859, Int.ofNat (nat_lit 1))]
theorem atom1748Coded_decode : atom1748 = SparsePolynomial.decodeCubic 24 atom1748Coded := by decide +kernel
theorem atom1748Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (316705906944000 : Int) atom1748Coded) := by
  have h := atom1748_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1748Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1749 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1749 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1749 = ((g 6) * (g 16) * (g 20)) := by
  norm_num [atom1749, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1749_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (456299347795200 : Int) atom1749) := by
  rw [SparsePolynomial.eval_scale, eval_atom1749]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1749Coded : CoefficientMerge.Poly := [(nat_lit 3860, Int.ofNat (nat_lit 1))]
theorem atom1749Coded_decode : atom1749 = SparsePolynomial.decodeCubic 24 atom1749Coded := by decide +kernel
theorem atom1749Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (456299347795200 : Int) atom1749Coded) := by
  have h := atom1749_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1749Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1750 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1750 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1750 = ((g 6) * (g 16) * (g 21)) := by
  norm_num [atom1750, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1750_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (480987995241600 : Int) atom1750) := by
  rw [SparsePolynomial.eval_scale, eval_atom1750]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1750Coded : CoefficientMerge.Poly := [(nat_lit 3861, Int.ofNat (nat_lit 1))]
theorem atom1750Coded_decode : atom1750 = SparsePolynomial.decodeCubic 24 atom1750Coded := by decide +kernel
theorem atom1750Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (480987995241600 : Int) atom1750Coded) := by
  have h := atom1750_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1750Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1751 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1751 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1751 = ((g 6) * (g 16) * (g 22)) := by
  norm_num [atom1751, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1751_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (434079871142400 : Int) atom1751) := by
  rw [SparsePolynomial.eval_scale, eval_atom1751]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1751Coded : CoefficientMerge.Poly := [(nat_lit 3862, Int.ofNat (nat_lit 1))]
theorem atom1751Coded_decode : atom1751 = SparsePolynomial.decodeCubic 24 atom1751Coded := by decide +kernel
theorem atom1751Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (434079871142400 : Int) atom1751Coded) := by
  have h := atom1751_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1751Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1752 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1752 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1752 = ((g 6) * (g 16) * (g 23)) := by
  norm_num [atom1752, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1752_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (596550230136000 : Int) atom1752) := by
  rw [SparsePolynomial.eval_scale, eval_atom1752]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1752Coded : CoefficientMerge.Poly := [(nat_lit 3863, Int.ofNat (nat_lit 1))]
theorem atom1752Coded_decode : atom1752 = SparsePolynomial.decodeCubic 24 atom1752Coded := by decide +kernel
theorem atom1752Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (596550230136000 : Int) atom1752Coded) := by
  have h := atom1752_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1752Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1753 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1753 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1753 = ((g 6) * (g 17) * (g 17)) := by
  norm_num [atom1753, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1753_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189362478412800 : Int) atom1753) := by
  rw [SparsePolynomial.eval_scale, eval_atom1753]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1753Coded : CoefficientMerge.Poly := [(nat_lit 3881, Int.ofNat (nat_lit 1))]
theorem atom1753Coded_decode : atom1753 = SparsePolynomial.decodeCubic 24 atom1753Coded := by decide +kernel
theorem atom1753Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (189362478412800 : Int) atom1753Coded) := by
  have h := atom1753_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1753Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1754 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1754 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1754 = ((g 6) * (g 17) * (g 18)) := by
  norm_num [atom1754, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1754_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353996845171200 : Int) atom1754) := by
  rw [SparsePolynomial.eval_scale, eval_atom1754]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1754Coded : CoefficientMerge.Poly := [(nat_lit 3882, Int.ofNat (nat_lit 1))]
theorem atom1754Coded_decode : atom1754 = SparsePolynomial.decodeCubic 24 atom1754Coded := by decide +kernel
theorem atom1754Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (353996845171200 : Int) atom1754Coded) := by
  have h := atom1754_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1754Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1755 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1755 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1755 = ((g 6) * (g 17) * (g 19)) := by
  norm_num [atom1755, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1755_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360099139276800 : Int) atom1755) := by
  rw [SparsePolynomial.eval_scale, eval_atom1755]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1755Coded : CoefficientMerge.Poly := [(nat_lit 3883, Int.ofNat (nat_lit 1))]
theorem atom1755Coded_decode : atom1755 = SparsePolynomial.decodeCubic 24 atom1755Coded := by decide +kernel
theorem atom1755Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (360099139276800 : Int) atom1755Coded) := by
  have h := atom1755_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1755Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1756 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1756 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1756 = ((g 6) * (g 17) * (g 20)) := by
  norm_num [atom1756, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1756_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (507043231833600 : Int) atom1756) := by
  rw [SparsePolynomial.eval_scale, eval_atom1756]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1756Coded : CoefficientMerge.Poly := [(nat_lit 3884, Int.ofNat (nat_lit 1))]
theorem atom1756Coded_decode : atom1756 = SparsePolynomial.decodeCubic 24 atom1756Coded := by decide +kernel
theorem atom1756Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (507043231833600 : Int) atom1756Coded) := by
  have h := atom1756_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1756Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1757 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1757 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1757 = ((g 6) * (g 17) * (g 21)) := by
  norm_num [atom1757, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1757_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (538979279731200 : Int) atom1757) := by
  rw [SparsePolynomial.eval_scale, eval_atom1757]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1757Coded : CoefficientMerge.Poly := [(nat_lit 3885, Int.ofNat (nat_lit 1))]
theorem atom1757Coded_decode : atom1757 = SparsePolynomial.decodeCubic 24 atom1757Coded := by decide +kernel
theorem atom1757Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (538979279731200 : Int) atom1757Coded) := by
  have h := atom1757_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1757Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1758 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1758 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1758 = ((g 6) * (g 17) * (g 22)) := by
  norm_num [atom1758, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1758_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (498194873164800 : Int) atom1758) := by
  rw [SparsePolynomial.eval_scale, eval_atom1758]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1758Coded : CoefficientMerge.Poly := [(nat_lit 3886, Int.ofNat (nat_lit 1))]
theorem atom1758Coded_decode : atom1758 = SparsePolynomial.decodeCubic 24 atom1758Coded := by decide +kernel
theorem atom1758Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (498194873164800 : Int) atom1758Coded) := by
  have h := atom1758_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1758Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1759 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1759 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1759 = ((g 6) * (g 17) * (g 23)) := by
  norm_num [atom1759, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1759_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (667861006982400 : Int) atom1759) := by
  rw [SparsePolynomial.eval_scale, eval_atom1759]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1759Coded : CoefficientMerge.Poly := [(nat_lit 3887, Int.ofNat (nat_lit 1))]
theorem atom1759Coded_decode : atom1759 = SparsePolynomial.decodeCubic 24 atom1759Coded := by decide +kernel
theorem atom1759Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (667861006982400 : Int) atom1759Coded) := by
  have h := atom1759_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1759Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1760 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1760 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1760 = ((g 6) * (g 18) * (g 18)) := by
  norm_num [atom1760, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1760_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (215504536262400 : Int) atom1760) := by
  rw [SparsePolynomial.eval_scale, eval_atom1760]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1760Coded : CoefficientMerge.Poly := [(nat_lit 3906, Int.ofNat (nat_lit 1))]
theorem atom1760Coded_decode : atom1760 = SparsePolynomial.decodeCubic 24 atom1760Coded := by decide +kernel
theorem atom1760Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (215504536262400 : Int) atom1760Coded) := by
  have h := atom1760_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1760Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1761 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1761 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1761 = ((g 6) * (g 18) * (g 19)) := by
  norm_num [atom1761, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1761_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411554023372800 : Int) atom1761) := by
  rw [SparsePolynomial.eval_scale, eval_atom1761]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1761Coded : CoefficientMerge.Poly := [(nat_lit 3907, Int.ofNat (nat_lit 1))]
theorem atom1761Coded_decode : atom1761 = SparsePolynomial.decodeCubic 24 atom1761Coded := by decide +kernel
theorem atom1761Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (411554023372800 : Int) atom1761Coded) := by
  have h := atom1761_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1761Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1762 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1762 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1762 = ((g 6) * (g 18) * (g 20)) := by
  norm_num [atom1762, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1762_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (603361671897600 : Int) atom1762) := by
  rw [SparsePolynomial.eval_scale, eval_atom1762]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1762Coded : CoefficientMerge.Poly := [(nat_lit 3908, Int.ofNat (nat_lit 1))]
theorem atom1762Coded_decode : atom1762 = SparsePolynomial.decodeCubic 24 atom1762Coded := by decide +kernel
theorem atom1762Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (603361671897600 : Int) atom1762Coded) := by
  have h := atom1762_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1762Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1763 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1763 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1763 = ((g 6) * (g 18) * (g 21)) := by
  norm_num [atom1763, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1763_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (596010214800000 : Int) atom1763) := by
  rw [SparsePolynomial.eval_scale, eval_atom1763]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1763Coded : CoefficientMerge.Poly := [(nat_lit 3909, Int.ofNat (nat_lit 1))]
theorem atom1763Coded_decode : atom1763 = SparsePolynomial.decodeCubic 24 atom1763Coded := by decide +kernel
theorem atom1763Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (596010214800000 : Int) atom1763Coded) := by
  have h := atom1763_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1763Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1764 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1764 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1764 = ((g 6) * (g 18) * (g 22)) := by
  norm_num [atom1764, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1764_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (459421369344000 : Int) atom1764) := by
  rw [SparsePolynomial.eval_scale, eval_atom1764]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1764Coded : CoefficientMerge.Poly := [(nat_lit 3910, Int.ofNat (nat_lit 1))]
theorem atom1764Coded_decode : atom1764 = SparsePolynomial.decodeCubic 24 atom1764Coded := by decide +kernel
theorem atom1764Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (459421369344000 : Int) atom1764Coded) := by
  have h := atom1764_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1764Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1765 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1765 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1765 = ((g 6) * (g 18) * (g 23)) := by
  norm_num [atom1765, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1765_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (653633837841600 : Int) atom1765) := by
  rw [SparsePolynomial.eval_scale, eval_atom1765]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1765Coded : CoefficientMerge.Poly := [(nat_lit 3911, Int.ofNat (nat_lit 1))]
theorem atom1765Coded_decode : atom1765 = SparsePolynomial.decodeCubic 24 atom1765Coded := by decide +kernel
theorem atom1765Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (653633837841600 : Int) atom1765Coded) := by
  have h := atom1765_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1765Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1766 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1766 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1766 = ((g 6) * (g 19) * (g 19)) := by
  norm_num [atom1766, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1766_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140688709539840 : Int) atom1766) := by
  rw [SparsePolynomial.eval_scale, eval_atom1766]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1766Coded : CoefficientMerge.Poly := [(nat_lit 3931, Int.ofNat (nat_lit 1))]
theorem atom1766Coded_decode : atom1766 = SparsePolynomial.decodeCubic 24 atom1766Coded := by decide +kernel
theorem atom1766Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (140688709539840 : Int) atom1766Coded) := by
  have h := atom1766_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1766Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1767 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1767 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1767 = ((g 6) * (g 19) * (g 20)) := by
  norm_num [atom1767, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1767_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (444000367641600 : Int) atom1767) := by
  rw [SparsePolynomial.eval_scale, eval_atom1767]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1767Coded : CoefficientMerge.Poly := [(nat_lit 3932, Int.ofNat (nat_lit 1))]
theorem atom1767Coded_decode : atom1767 = SparsePolynomial.decodeCubic 24 atom1767Coded := by decide +kernel
theorem atom1767Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (444000367641600 : Int) atom1767Coded) := by
  have h := atom1767_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1767Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1768 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1768 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1768 = ((g 6) * (g 19) * (g 21)) := by
  norm_num [atom1768, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1768_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440555867136000 : Int) atom1768) := by
  rw [SparsePolynomial.eval_scale, eval_atom1768]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1768Coded : CoefficientMerge.Poly := [(nat_lit 3933, Int.ofNat (nat_lit 1))]
theorem atom1768Coded_decode : atom1768 = SparsePolynomial.decodeCubic 24 atom1768Coded := by decide +kernel
theorem atom1768Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (440555867136000 : Int) atom1768Coded) := by
  have h := atom1768_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1768Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1769 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1769 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1769 = ((g 6) * (g 19) * (g 22)) := by
  norm_num [atom1769, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1769_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (373855556793600 : Int) atom1769) := by
  rw [SparsePolynomial.eval_scale, eval_atom1769]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1769Coded : CoefficientMerge.Poly := [(nat_lit 3934, Int.ofNat (nat_lit 1))]
theorem atom1769Coded_decode : atom1769 = SparsePolynomial.decodeCubic 24 atom1769Coded := by decide +kernel
theorem atom1769Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (373855556793600 : Int) atom1769Coded) := by
  have h := atom1769_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1769Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1770 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1770 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1770 = ((g 6) * (g 19) * (g 23)) := by
  norm_num [atom1770, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1770_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427044288787200 : Int) atom1770) := by
  rw [SparsePolynomial.eval_scale, eval_atom1770]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1770Coded : CoefficientMerge.Poly := [(nat_lit 3935, Int.ofNat (nat_lit 1))]
theorem atom1770Coded_decode : atom1770 = SparsePolynomial.decodeCubic 24 atom1770Coded := by decide +kernel
theorem atom1770Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (427044288787200 : Int) atom1770Coded) := by
  have h := atom1770_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1770Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1771 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1771 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1771 = ((g 6) * (g 20) * (g 20)) := by
  norm_num [atom1771, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1771_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (318371779756800 : Int) atom1771) := by
  rw [SparsePolynomial.eval_scale, eval_atom1771]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1771Coded : CoefficientMerge.Poly := [(nat_lit 3956, Int.ofNat (nat_lit 1))]
theorem atom1771Coded_decode : atom1771 = SparsePolynomial.decodeCubic 24 atom1771Coded := by decide +kernel
theorem atom1771Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (318371779756800 : Int) atom1771Coded) := by
  have h := atom1771_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1771Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1772 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1772 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1772 = ((g 6) * (g 20) * (g 21)) := by
  norm_num [atom1772, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1772_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (461153767536000 : Int) atom1772) := by
  rw [SparsePolynomial.eval_scale, eval_atom1772]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1772Coded : CoefficientMerge.Poly := [(nat_lit 3957, Int.ofNat (nat_lit 1))]
theorem atom1772Coded_decode : atom1772 = SparsePolynomial.decodeCubic 24 atom1772Coded := by decide +kernel
theorem atom1772Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (461153767536000 : Int) atom1772Coded) := by
  have h := atom1772_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1772Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1773 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1773 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1773 = ((g 6) * (g 20) * (g 22)) := by
  norm_num [atom1773, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1773_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (366896969913600 : Int) atom1773) := by
  rw [SparsePolynomial.eval_scale, eval_atom1773]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1773Coded : CoefficientMerge.Poly := [(nat_lit 3958, Int.ofNat (nat_lit 1))]
theorem atom1773Coded_decode : atom1773 = SparsePolynomial.decodeCubic 24 atom1773Coded := by decide +kernel
theorem atom1773Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (366896969913600 : Int) atom1773Coded) := by
  have h := atom1773_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1773Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1774 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1774 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1774 = ((g 6) * (g 20) * (g 23)) := by
  norm_num [atom1774, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1774_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (448745173531200 : Int) atom1774) := by
  rw [SparsePolynomial.eval_scale, eval_atom1774]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1774Coded : CoefficientMerge.Poly := [(nat_lit 3959, Int.ofNat (nat_lit 1))]
theorem atom1774Coded_decode : atom1774 = SparsePolynomial.decodeCubic 24 atom1774Coded := by decide +kernel
theorem atom1774Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (448745173531200 : Int) atom1774Coded) := by
  have h := atom1774_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1774Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1775 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1775 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1775 = ((g 6) * (g 21) * (g 21)) := by
  norm_num [atom1775, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1775_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95265953798400 : Int) atom1775) := by
  rw [SparsePolynomial.eval_scale, eval_atom1775]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 6) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1775Coded : CoefficientMerge.Poly := [(nat_lit 3981, Int.ofNat (nat_lit 1))]
theorem atom1775Coded_decode : atom1775 = SparsePolynomial.decodeCubic 24 atom1775Coded := by decide +kernel
theorem atom1775Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (95265953798400 : Int) atom1775Coded) := by
  have h := atom1775_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1775Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1776 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1776 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1776 = ((g 6) * (g 21) * (g 22)) := by
  norm_num [atom1776, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1776_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154961447760000 : Int) atom1776) := by
  rw [SparsePolynomial.eval_scale, eval_atom1776]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 6) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1776Coded : CoefficientMerge.Poly := [(nat_lit 3982, Int.ofNat (nat_lit 1))]
theorem atom1776Coded_decode : atom1776 = SparsePolynomial.decodeCubic 24 atom1776Coded := by decide +kernel
theorem atom1776Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (154961447760000 : Int) atom1776Coded) := by
  have h := atom1776_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1776Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1777 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1777 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1777 = ((g 6) * (g 21) * (g 23)) := by
  norm_num [atom1777, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1777_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (232770529958400 : Int) atom1777) := by
  rw [SparsePolynomial.eval_scale, eval_atom1777]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 6) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1777Coded : CoefficientMerge.Poly := [(nat_lit 3983, Int.ofNat (nat_lit 1))]
theorem atom1777Coded_decode : atom1777 = SparsePolynomial.decodeCubic 24 atom1777Coded := by decide +kernel
theorem atom1777Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (232770529958400 : Int) atom1777Coded) := by
  have h := atom1777_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1777Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1778 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1778 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1778 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom1778, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1778_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12511711027200 : Int) atom1778) := by
  rw [SparsePolynomial.eval_scale, eval_atom1778]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1778Coded : CoefficientMerge.Poly := [(nat_lit 4207, Int.ofNat (nat_lit 1))]
theorem atom1778Coded_decode : atom1778 = SparsePolynomial.decodeCubic 24 atom1778Coded := by decide +kernel
theorem atom1778Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12511711027200 : Int) atom1778Coded) := by
  have h := atom1778_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1778Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1779 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1779 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1779 = ((g 7) * (g 7) * (g 8)) := by
  norm_num [atom1779, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1779_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21812807385600 : Int) atom1779) := by
  rw [SparsePolynomial.eval_scale, eval_atom1779]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1779Coded : CoefficientMerge.Poly := [(nat_lit 4208, Int.ofNat (nat_lit 1))]
theorem atom1779Coded_decode : atom1779 = SparsePolynomial.decodeCubic 24 atom1779Coded := by decide +kernel
theorem atom1779Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (21812807385600 : Int) atom1779Coded) := by
  have h := atom1779_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1779Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1780 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1780 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1780 = ((g 7) * (g 7) * (g 9)) := by
  norm_num [atom1780, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1780_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom1780) := by
  rw [SparsePolynomial.eval_scale, eval_atom1780]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1780Coded : CoefficientMerge.Poly := [(nat_lit 4209, Int.ofNat (nat_lit 1))]
theorem atom1780Coded_decode : atom1780 = SparsePolynomial.decodeCubic 24 atom1780Coded := by decide +kernel
theorem atom1780Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom1780Coded) := by
  have h := atom1780_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1780Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1781 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1781 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1781 = ((g 7) * (g 7) * (g 10)) := by
  norm_num [atom1781, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1781_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3663191356704 : Int) atom1781) := by
  rw [SparsePolynomial.eval_scale, eval_atom1781]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1781Coded : CoefficientMerge.Poly := [(nat_lit 4210, Int.ofNat (nat_lit 1))]
theorem atom1781Coded_decode : atom1781 = SparsePolynomial.decodeCubic 24 atom1781Coded := by decide +kernel
theorem atom1781Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3663191356704 : Int) atom1781Coded) := by
  have h := atom1781_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1781Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1782 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1782 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1782 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom1782, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1782_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28692358464000 : Int) atom1782) := by
  rw [SparsePolynomial.eval_scale, eval_atom1782]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1782Coded : CoefficientMerge.Poly := [(nat_lit 4232, Int.ofNat (nat_lit 1))]
theorem atom1782Coded_decode : atom1782 = SparsePolynomial.decodeCubic 24 atom1782Coded := by decide +kernel
theorem atom1782Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (28692358464000 : Int) atom1782Coded) := by
  have h := atom1782_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1782Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1783 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1783 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1783 = ((g 7) * (g 8) * (g 9)) := by
  norm_num [atom1783, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1783_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24022245970800 : Int) atom1783) := by
  rw [SparsePolynomial.eval_scale, eval_atom1783]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1783Coded : CoefficientMerge.Poly := [(nat_lit 4233, Int.ofNat (nat_lit 1))]
theorem atom1783Coded_decode : atom1783 = SparsePolynomial.decodeCubic 24 atom1783Coded := by decide +kernel
theorem atom1783Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24022245970800 : Int) atom1783Coded) := by
  have h := atom1783_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1783Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1784 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1784 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1784 = ((g 7) * (g 8) * (g 13)) := by
  norm_num [atom1784, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1784_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3083040576000 : Int) atom1784) := by
  rw [SparsePolynomial.eval_scale, eval_atom1784]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1784Coded : CoefficientMerge.Poly := [(nat_lit 4237, Int.ofNat (nat_lit 1))]
theorem atom1784Coded_decode : atom1784 = SparsePolynomial.decodeCubic 24 atom1784Coded := by decide +kernel
theorem atom1784Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (3083040576000 : Int) atom1784Coded) := by
  have h := atom1784_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1784Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1785 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1785 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1785 = ((g 7) * (g 8) * (g 14)) := by
  norm_num [atom1785, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1785_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6166081152000 : Int) atom1785) := by
  rw [SparsePolynomial.eval_scale, eval_atom1785]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1785Coded : CoefficientMerge.Poly := [(nat_lit 4238, Int.ofNat (nat_lit 1))]
theorem atom1785Coded_decode : atom1785 = SparsePolynomial.decodeCubic 24 atom1785Coded := by decide +kernel
theorem atom1785Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (6166081152000 : Int) atom1785Coded) := by
  have h := atom1785_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1785Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1786 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1786 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1786 = ((g 7) * (g 8) * (g 15)) := by
  norm_num [atom1786, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1786_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9249121728000 : Int) atom1786) := by
  rw [SparsePolynomial.eval_scale, eval_atom1786]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1786Coded : CoefficientMerge.Poly := [(nat_lit 4239, Int.ofNat (nat_lit 1))]
theorem atom1786Coded_decode : atom1786 = SparsePolynomial.decodeCubic 24 atom1786Coded := by decide +kernel
theorem atom1786Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (9249121728000 : Int) atom1786Coded) := by
  have h := atom1786_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1786Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1787 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1787 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1787 = ((g 7) * (g 8) * (g 16)) := by
  norm_num [atom1787, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1787_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12332162304000 : Int) atom1787) := by
  rw [SparsePolynomial.eval_scale, eval_atom1787]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1787Coded : CoefficientMerge.Poly := [(nat_lit 4240, Int.ofNat (nat_lit 1))]
theorem atom1787Coded_decode : atom1787 = SparsePolynomial.decodeCubic 24 atom1787Coded := by decide +kernel
theorem atom1787Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12332162304000 : Int) atom1787Coded) := by
  have h := atom1787_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1787Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1788 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1788 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1788 = ((g 7) * (g 8) * (g 17)) := by
  norm_num [atom1788, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1788_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15415202880000 : Int) atom1788) := by
  rw [SparsePolynomial.eval_scale, eval_atom1788]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1788Coded : CoefficientMerge.Poly := [(nat_lit 4241, Int.ofNat (nat_lit 1))]
theorem atom1788Coded_decode : atom1788 = SparsePolynomial.decodeCubic 24 atom1788Coded := by decide +kernel
theorem atom1788Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (15415202880000 : Int) atom1788Coded) := by
  have h := atom1788_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1788Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1789 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1789 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1789 = ((g 7) * (g 8) * (g 18)) := by
  norm_num [atom1789, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1789_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (822852898560 : Int) atom1789) := by
  rw [SparsePolynomial.eval_scale, eval_atom1789]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1789Coded : CoefficientMerge.Poly := [(nat_lit 4242, Int.ofNat (nat_lit 1))]
theorem atom1789Coded_decode : atom1789 = SparsePolynomial.decodeCubic 24 atom1789Coded := by decide +kernel
theorem atom1789Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (822852898560 : Int) atom1789Coded) := by
  have h := atom1789_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1789Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1790 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1790 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1790 = ((g 7) * (g 8) * (g 21)) := by
  norm_num [atom1790, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1790_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41615732188800 : Int) atom1790) := by
  rw [SparsePolynomial.eval_scale, eval_atom1790]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1790Coded : CoefficientMerge.Poly := [(nat_lit 4245, Int.ofNat (nat_lit 1))]
theorem atom1790Coded_decode : atom1790 = SparsePolynomial.decodeCubic 24 atom1790Coded := by decide +kernel
theorem atom1790Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (41615732188800 : Int) atom1790Coded) := by
  have h := atom1790_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1790Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1791 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1791 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1791 = ((g 7) * (g 8) * (g 22)) := by
  norm_num [atom1791, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1791_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84054317276160 : Int) atom1791) := by
  rw [SparsePolynomial.eval_scale, eval_atom1791]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1791Coded : CoefficientMerge.Poly := [(nat_lit 4246, Int.ofNat (nat_lit 1))]
theorem atom1791Coded_decode : atom1791 = SparsePolynomial.decodeCubic 24 atom1791Coded := by decide +kernel
theorem atom1791Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (84054317276160 : Int) atom1791Coded) := by
  have h := atom1791_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1791Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1792 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1792 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1792 = ((g 7) * (g 8) * (g 23)) := by
  norm_num [atom1792, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1792_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134354124273600 : Int) atom1792) := by
  rw [SparsePolynomial.eval_scale, eval_atom1792]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1792Coded : CoefficientMerge.Poly := [(nat_lit 4247, Int.ofNat (nat_lit 1))]
theorem atom1792Coded_decode : atom1792 = SparsePolynomial.decodeCubic 24 atom1792Coded := by decide +kernel
theorem atom1792Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134354124273600 : Int) atom1792Coded) := by
  have h := atom1792_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1792Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1793 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1793 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1793 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom1793, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1793_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21014804857200 : Int) atom1793) := by
  rw [SparsePolynomial.eval_scale, eval_atom1793]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1793Coded : CoefficientMerge.Poly := [(nat_lit 4257, Int.ofNat (nat_lit 1))]
theorem atom1793Coded_decode : atom1793 = SparsePolynomial.decodeCubic 24 atom1793Coded := by decide +kernel
theorem atom1793Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (21014804857200 : Int) atom1793Coded) := by
  have h := atom1793_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1793Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1794 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1794 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1794 = ((g 7) * (g 9) * (g 10)) := by
  norm_num [atom1794, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1794_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20007883720704 : Int) atom1794) := by
  rw [SparsePolynomial.eval_scale, eval_atom1794]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1794Coded : CoefficientMerge.Poly := [(nat_lit 4258, Int.ofNat (nat_lit 1))]
theorem atom1794Coded_decode : atom1794 = SparsePolynomial.decodeCubic 24 atom1794Coded := by decide +kernel
theorem atom1794Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (20007883720704 : Int) atom1794Coded) := by
  have h := atom1794_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1794Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1795 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1795 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1795 = ((g 7) * (g 9) * (g 11)) := by
  norm_num [atom1795, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1795_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27833005200 : Int) atom1795) := by
  rw [SparsePolynomial.eval_scale, eval_atom1795]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1795Coded : CoefficientMerge.Poly := [(nat_lit 4259, Int.ofNat (nat_lit 1))]
theorem atom1795Coded_decode : atom1795 = SparsePolynomial.decodeCubic 24 atom1795Coded := by decide +kernel
theorem atom1795Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27833005200 : Int) atom1795Coded) := by
  have h := atom1795_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1795Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1796 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1796 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1796 = ((g 7) * (g 9) * (g 12)) := by
  norm_num [atom1796, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1796_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5173321414800 : Int) atom1796) := by
  rw [SparsePolynomial.eval_scale, eval_atom1796]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1796Coded : CoefficientMerge.Poly := [(nat_lit 4260, Int.ofNat (nat_lit 1))]
theorem atom1796Coded_decode : atom1796 = SparsePolynomial.decodeCubic 24 atom1796Coded := by decide +kernel
theorem atom1796Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (5173321414800 : Int) atom1796Coded) := by
  have h := atom1796_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1796Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1797 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1797 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1797 = ((g 7) * (g 9) * (g 13)) := by
  norm_num [atom1797, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1797_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7235769248400 : Int) atom1797) := by
  rw [SparsePolynomial.eval_scale, eval_atom1797]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1797Coded : CoefficientMerge.Poly := [(nat_lit 4261, Int.ofNat (nat_lit 1))]
theorem atom1797Coded_decode : atom1797 = SparsePolynomial.decodeCubic 24 atom1797Coded := by decide +kernel
theorem atom1797Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (7235769248400 : Int) atom1797Coded) := by
  have h := atom1797_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1797Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1798 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1798 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1798 = ((g 7) * (g 9) * (g 14)) := by
  norm_num [atom1798, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1798_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12381257658000 : Int) atom1798) := by
  rw [SparsePolynomial.eval_scale, eval_atom1798]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1798Coded : CoefficientMerge.Poly := [(nat_lit 4262, Int.ofNat (nat_lit 1))]
theorem atom1798Coded_decode : atom1798 = SparsePolynomial.decodeCubic 24 atom1798Coded := by decide +kernel
theorem atom1798Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (12381257658000 : Int) atom1798Coded) := by
  have h := atom1798_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1798Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1799 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1799 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1799 = ((g 7) * (g 9) * (g 15)) := by
  norm_num [atom1799, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1799_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17526746067600 : Int) atom1799) := by
  rw [SparsePolynomial.eval_scale, eval_atom1799]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1799Coded : CoefficientMerge.Poly := [(nat_lit 4263, Int.ofNat (nat_lit 1))]
theorem atom1799Coded_decode : atom1799 = SparsePolynomial.decodeCubic 24 atom1799Coded := by decide +kernel
theorem atom1799Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (17526746067600 : Int) atom1799Coded) := by
  have h := atom1799_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1799Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1800 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1800 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1800 = ((g 7) * (g 9) * (g 16)) := by
  norm_num [atom1800, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1800_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22672234477200 : Int) atom1800) := by
  rw [SparsePolynomial.eval_scale, eval_atom1800]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1800Coded : CoefficientMerge.Poly := [(nat_lit 4264, Int.ofNat (nat_lit 1))]
theorem atom1800Coded_decode : atom1800 = SparsePolynomial.decodeCubic 24 atom1800Coded := by decide +kernel
theorem atom1800Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (22672234477200 : Int) atom1800Coded) := by
  have h := atom1800_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1800Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1801 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1801 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1801 = ((g 7) * (g 9) * (g 17)) := by
  norm_num [atom1801, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1801_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27817722886800 : Int) atom1801) := by
  rw [SparsePolynomial.eval_scale, eval_atom1801]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1801Coded : CoefficientMerge.Poly := [(nat_lit 4265, Int.ofNat (nat_lit 1))]
theorem atom1801Coded_decode : atom1801 = SparsePolynomial.decodeCubic 24 atom1801Coded := by decide +kernel
theorem atom1801Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (27817722886800 : Int) atom1801Coded) := by
  have h := atom1801_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1801Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1802 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1802 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1802 = ((g 7) * (g 9) * (g 18)) := by
  norm_num [atom1802, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1802_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (743215066440 : Int) atom1802) := by
  rw [SparsePolynomial.eval_scale, eval_atom1802]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1802Coded : CoefficientMerge.Poly := [(nat_lit 4266, Int.ofNat (nat_lit 1))]
theorem atom1802Coded_decode : atom1802 = SparsePolynomial.decodeCubic 24 atom1802Coded := by decide +kernel
theorem atom1802Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (743215066440 : Int) atom1802Coded) := by
  have h := atom1802_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1802Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1803 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1803 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1803 = ((g 7) * (g 9) * (g 21)) := by
  norm_num [atom1803, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1803_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80451799866900 : Int) atom1803) := by
  rw [SparsePolynomial.eval_scale, eval_atom1803]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 7) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1803Coded : CoefficientMerge.Poly := [(nat_lit 4269, Int.ofNat (nat_lit 1))]
theorem atom1803Coded_decode : atom1803 = SparsePolynomial.decodeCubic 24 atom1803Coded := by decide +kernel
theorem atom1803Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (80451799866900 : Int) atom1803Coded) := by
  have h := atom1803_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1803Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1804 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1804 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1804 = ((g 7) * (g 9) * (g 22)) := by
  norm_num [atom1804, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1804_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161646814800240 : Int) atom1804) := by
  rw [SparsePolynomial.eval_scale, eval_atom1804]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 7) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1804Coded : CoefficientMerge.Poly := [(nat_lit 4270, Int.ofNat (nat_lit 1))]
theorem atom1804Coded_decode : atom1804 = SparsePolynomial.decodeCubic 24 atom1804Coded := by decide +kernel
theorem atom1804Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (161646814800240 : Int) atom1804Coded) := by
  have h := atom1804_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1804Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1805 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1805 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1805 = ((g 7) * (g 9) * (g 23)) := by
  norm_num [atom1805, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1805_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (257479651979550 : Int) atom1805) := by
  rw [SparsePolynomial.eval_scale, eval_atom1805]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 7) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1805Coded : CoefficientMerge.Poly := [(nat_lit 4271, Int.ofNat (nat_lit 1))]
theorem atom1805Coded_decode : atom1805 = SparsePolynomial.decodeCubic 24 atom1805Coded := by decide +kernel
theorem atom1805Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (257479651979550 : Int) atom1805Coded) := by
  have h := atom1805_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1805Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1806 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1806 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1806 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom1806, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1806_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24677996213904 : Int) atom1806) := by
  rw [SparsePolynomial.eval_scale, eval_atom1806]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1806Coded : CoefficientMerge.Poly := [(nat_lit 4282, Int.ofNat (nat_lit 1))]
theorem atom1806Coded_decode : atom1806 = SparsePolynomial.decodeCubic 24 atom1806Coded := by decide +kernel
theorem atom1806Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (24677996213904 : Int) atom1806Coded) := by
  have h := atom1806_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1806Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1807 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1807 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1807 = ((g 7) * (g 10) * (g 11)) := by
  norm_num [atom1807, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1807_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37625733046704 : Int) atom1807) := by
  rw [SparsePolynomial.eval_scale, eval_atom1807]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1807Coded : CoefficientMerge.Poly := [(nat_lit 4283, Int.ofNat (nat_lit 1))]
theorem atom1807Coded_decode : atom1807 = SparsePolynomial.decodeCubic 24 atom1807Coded := by decide +kernel
theorem atom1807Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (37625733046704 : Int) atom1807Coded) := by
  have h := atom1807_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1807Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1808 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1808 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1808 = ((g 7) * (g 10) * (g 12)) := by
  norm_num [atom1808, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1808_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40730035971504 : Int) atom1808) := by
  rw [SparsePolynomial.eval_scale, eval_atom1808]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1808Coded : CoefficientMerge.Poly := [(nat_lit 4284, Int.ofNat (nat_lit 1))]
theorem atom1808Coded_decode : atom1808 = SparsePolynomial.decodeCubic 24 atom1808Coded := by decide +kernel
theorem atom1808Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (40730035971504 : Int) atom1808Coded) := by
  have h := atom1808_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1808Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block024 : CoefficientMerge.Poly := [(nat_lit 3809, Int.ofNat (nat_lit 233230247712000)), (nat_lit 3810, Int.ofNat (nat_lit 257933553292800)), (nat_lit 3811, Int.ofNat (nat_lit 265146362157600)), (nat_lit 3812, Int.ofNat (nat_lit 374918996390400)), (nat_lit 3813, Int.ofNat (nat_lit 387123584601600)), (nat_lit 3814, Int.ofNat (nat_lit 456327657324000)), (nat_lit 3815, Int.ofNat (nat_lit 541885577032800)), (nat_lit 3831, Int.ofNat (nat_lit 152479390694400)), (nat_lit 3832, Int.ofNat (nat_lit 282612052800000)), (nat_lit 3833, Int.ofNat (nat_lit 273618079257600)), (nat_lit 3834, Int.ofNat (nat_lit 296810791603200)), (nat_lit 3835, Int.ofNat (nat_lit 293178151526400)), (nat_lit 3836, Int.ofNat (nat_lit 430387309900800)), (nat_lit 3837, Int.ofNat (nat_lit 450311741510400)), (nat_lit 3838, Int.ofNat (nat_lit 456432398553600)), (nat_lit 3839, Int.ofNat (nat_lit 536413784054400)), (nat_lit 3856, Int.ofNat (nat_lit 171232782336000)), (nat_lit 3857, Int.ofNat (nat_lit 324286256448000)), (nat_lit 3858, Int.ofNat (nat_lit 317954264544000)), (nat_lit 3859, Int.ofNat (nat_lit 316705906944000)), (nat_lit 3860, Int.ofNat (nat_lit 456299347795200)), (nat_lit 3861, Int.ofNat (nat_lit 480987995241600)), (nat_lit 3862, Int.ofNat (nat_lit 434079871142400)), (nat_lit 3863, Int.ofNat (nat_lit 596550230136000)), (nat_lit 3881, Int.ofNat (nat_lit 189362478412800)), (nat_lit 3882, Int.ofNat (nat_lit 353996845171200)), (nat_lit 3883, Int.ofNat (nat_lit 360099139276800)), (nat_lit 3884, Int.ofNat (nat_lit 507043231833600)), (nat_lit 3885, Int.ofNat (nat_lit 538979279731200)), (nat_lit 3886, Int.ofNat (nat_lit 498194873164800)), (nat_lit 3887, Int.ofNat (nat_lit 667861006982400)), (nat_lit 3906, Int.ofNat (nat_lit 215504536262400)), (nat_lit 3907, Int.ofNat (nat_lit 411554023372800)), (nat_lit 3908, Int.ofNat (nat_lit 603361671897600)), (nat_lit 3909, Int.ofNat (nat_lit 596010214800000)), (nat_lit 3910, Int.ofNat (nat_lit 459421369344000)), (nat_lit 3911, Int.ofNat (nat_lit 653633837841600)), (nat_lit 3931, Int.ofNat (nat_lit 140688709539840)), (nat_lit 3932, Int.ofNat (nat_lit 444000367641600)), (nat_lit 3933, Int.ofNat (nat_lit 440555867136000)), (nat_lit 3934, Int.ofNat (nat_lit 373855556793600)), (nat_lit 3935, Int.ofNat (nat_lit 427044288787200)), (nat_lit 3956, Int.ofNat (nat_lit 318371779756800)), (nat_lit 3957, Int.ofNat (nat_lit 461153767536000)), (nat_lit 3958, Int.ofNat (nat_lit 366896969913600)), (nat_lit 3959, Int.ofNat (nat_lit 448745173531200)), (nat_lit 3981, Int.ofNat (nat_lit 95265953798400)), (nat_lit 3982, Int.ofNat (nat_lit 154961447760000)), (nat_lit 3983, Int.ofNat (nat_lit 232770529958400)), (nat_lit 4207, Int.ofNat (nat_lit 12511711027200)), (nat_lit 4208, Int.ofNat (nat_lit 21812807385600)), (nat_lit 4209, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4210, Int.ofNat (nat_lit 3663191356704)), (nat_lit 4232, Int.ofNat (nat_lit 28692358464000)), (nat_lit 4233, Int.ofNat (nat_lit 24022245970800)), (nat_lit 4237, Int.ofNat (nat_lit 3083040576000)), (nat_lit 4238, Int.ofNat (nat_lit 6166081152000)), (nat_lit 4239, Int.ofNat (nat_lit 9249121728000)), (nat_lit 4240, Int.ofNat (nat_lit 12332162304000)), (nat_lit 4241, Int.ofNat (nat_lit 15415202880000)), (nat_lit 4242, Int.ofNat (nat_lit 822852898560)), (nat_lit 4245, Int.ofNat (nat_lit 41615732188800)), (nat_lit 4246, Int.ofNat (nat_lit 84054317276160)), (nat_lit 4247, Int.ofNat (nat_lit 134354124273600)), (nat_lit 4257, Int.ofNat (nat_lit 21014804857200)), (nat_lit 4258, Int.ofNat (nat_lit 20007883720704)), (nat_lit 4259, Int.ofNat (nat_lit 27833005200)), (nat_lit 4260, Int.ofNat (nat_lit 5173321414800)), (nat_lit 4261, Int.ofNat (nat_lit 7235769248400)), (nat_lit 4262, Int.ofNat (nat_lit 12381257658000)), (nat_lit 4263, Int.ofNat (nat_lit 17526746067600)), (nat_lit 4264, Int.ofNat (nat_lit 22672234477200)), (nat_lit 4265, Int.ofNat (nat_lit 27817722886800)), (nat_lit 4266, Int.ofNat (nat_lit 743215066440)), (nat_lit 4269, Int.ofNat (nat_lit 80451799866900)), (nat_lit 4270, Int.ofNat (nat_lit 161646814800240)), (nat_lit 4271, Int.ofNat (nat_lit 257479651979550)), (nat_lit 4282, Int.ofNat (nat_lit 24677996213904)), (nat_lit 4283, Int.ofNat (nat_lit 37625733046704)), (nat_lit 4284, Int.ofNat (nat_lit 40730035971504))]
theorem block024_data : block024 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (233230247712000 : Int) atom1729Coded) (CoefficientMerge.scale (257933553292800 : Int) atom1730Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (265146362157600 : Int) atom1731Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374918996390400 : Int) atom1732Coded) (CoefficientMerge.scale (387123584601600 : Int) atom1733Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (456327657324000 : Int) atom1734Coded) (CoefficientMerge.scale (541885577032800 : Int) atom1735Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152479390694400 : Int) atom1736Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (282612052800000 : Int) atom1737Coded) (CoefficientMerge.scale (273618079257600 : Int) atom1738Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (296810791603200 : Int) atom1739Coded) (CoefficientMerge.scale (293178151526400 : Int) atom1740Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (430387309900800 : Int) atom1741Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450311741510400 : Int) atom1742Coded) (CoefficientMerge.scale (456432398553600 : Int) atom1743Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (536413784054400 : Int) atom1744Coded) (CoefficientMerge.scale (171232782336000 : Int) atom1745Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (324286256448000 : Int) atom1746Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (317954264544000 : Int) atom1747Coded) (CoefficientMerge.scale (316705906944000 : Int) atom1748Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (456299347795200 : Int) atom1749Coded) (CoefficientMerge.scale (480987995241600 : Int) atom1750Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (434079871142400 : Int) atom1751Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (596550230136000 : Int) atom1752Coded) (CoefficientMerge.scale (189362478412800 : Int) atom1753Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (353996845171200 : Int) atom1754Coded) (CoefficientMerge.scale (360099139276800 : Int) atom1755Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (507043231833600 : Int) atom1756Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (538979279731200 : Int) atom1757Coded) (CoefficientMerge.scale (498194873164800 : Int) atom1758Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (667861006982400 : Int) atom1759Coded) (CoefficientMerge.scale (215504536262400 : Int) atom1760Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411554023372800 : Int) atom1761Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (603361671897600 : Int) atom1762Coded) (CoefficientMerge.scale (596010214800000 : Int) atom1763Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (459421369344000 : Int) atom1764Coded) (CoefficientMerge.scale (653633837841600 : Int) atom1765Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140688709539840 : Int) atom1766Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (444000367641600 : Int) atom1767Coded) (CoefficientMerge.scale (440555867136000 : Int) atom1768Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (373855556793600 : Int) atom1769Coded) (CoefficientMerge.scale (427044288787200 : Int) atom1770Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (318371779756800 : Int) atom1771Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (461153767536000 : Int) atom1772Coded) (CoefficientMerge.scale (366896969913600 : Int) atom1773Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (448745173531200 : Int) atom1774Coded) (CoefficientMerge.scale (95265953798400 : Int) atom1775Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154961447760000 : Int) atom1776Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (232770529958400 : Int) atom1777Coded) (CoefficientMerge.scale (12511711027200 : Int) atom1778Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21812807385600 : Int) atom1779Coded) (CoefficientMerge.scale (3083040576000 : Int) atom1780Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3663191356704 : Int) atom1781Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28692358464000 : Int) atom1782Coded) (CoefficientMerge.scale (24022245970800 : Int) atom1783Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3083040576000 : Int) atom1784Coded) (CoefficientMerge.scale (6166081152000 : Int) atom1785Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9249121728000 : Int) atom1786Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12332162304000 : Int) atom1787Coded) (CoefficientMerge.scale (15415202880000 : Int) atom1788Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (822852898560 : Int) atom1789Coded) (CoefficientMerge.scale (41615732188800 : Int) atom1790Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84054317276160 : Int) atom1791Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (134354124273600 : Int) atom1792Coded) (CoefficientMerge.scale (21014804857200 : Int) atom1793Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20007883720704 : Int) atom1794Coded) (CoefficientMerge.scale (27833005200 : Int) atom1795Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5173321414800 : Int) atom1796Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7235769248400 : Int) atom1797Coded) (CoefficientMerge.scale (12381257658000 : Int) atom1798Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17526746067600 : Int) atom1799Coded) (CoefficientMerge.scale (22672234477200 : Int) atom1800Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27817722886800 : Int) atom1801Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (743215066440 : Int) atom1802Coded) (CoefficientMerge.scale (80451799866900 : Int) atom1803Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (161646814800240 : Int) atom1804Coded) (CoefficientMerge.scale (257479651979550 : Int) atom1805Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24677996213904 : Int) atom1806Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37625733046704 : Int) atom1807Coded) (CoefficientMerge.scale (40730035971504 : Int) atom1808Coded)))))))) := by decide +kernel
theorem block024_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block024 := by
  rw [block024_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1729Coded_nonneg g hg hA hB) (atom1730Coded_nonneg g hg hA hB)) (add_nonneg (atom1731Coded_nonneg g hg hA hB) (add_nonneg (atom1732Coded_nonneg g hg hA hB) (atom1733Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1734Coded_nonneg g hg hA hB) (atom1735Coded_nonneg g hg hA hB)) (add_nonneg (atom1736Coded_nonneg g hg hA hB) (add_nonneg (atom1737Coded_nonneg g hg hA hB) (atom1738Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1739Coded_nonneg g hg hA hB) (atom1740Coded_nonneg g hg hA hB)) (add_nonneg (atom1741Coded_nonneg g hg hA hB) (add_nonneg (atom1742Coded_nonneg g hg hA hB) (atom1743Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1744Coded_nonneg g hg hA hB) (atom1745Coded_nonneg g hg hA hB)) (add_nonneg (atom1746Coded_nonneg g hg hA hB) (add_nonneg (atom1747Coded_nonneg g hg hA hB) (atom1748Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1749Coded_nonneg g hg hA hB) (atom1750Coded_nonneg g hg hA hB)) (add_nonneg (atom1751Coded_nonneg g hg hA hB) (add_nonneg (atom1752Coded_nonneg g hg hA hB) (atom1753Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1754Coded_nonneg g hg hA hB) (atom1755Coded_nonneg g hg hA hB)) (add_nonneg (atom1756Coded_nonneg g hg hA hB) (add_nonneg (atom1757Coded_nonneg g hg hA hB) (atom1758Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1759Coded_nonneg g hg hA hB) (atom1760Coded_nonneg g hg hA hB)) (add_nonneg (atom1761Coded_nonneg g hg hA hB) (add_nonneg (atom1762Coded_nonneg g hg hA hB) (atom1763Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1764Coded_nonneg g hg hA hB) (atom1765Coded_nonneg g hg hA hB)) (add_nonneg (atom1766Coded_nonneg g hg hA hB) (add_nonneg (atom1767Coded_nonneg g hg hA hB) (atom1768Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1769Coded_nonneg g hg hA hB) (atom1770Coded_nonneg g hg hA hB)) (add_nonneg (atom1771Coded_nonneg g hg hA hB) (add_nonneg (atom1772Coded_nonneg g hg hA hB) (atom1773Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1774Coded_nonneg g hg hA hB) (atom1775Coded_nonneg g hg hA hB)) (add_nonneg (atom1776Coded_nonneg g hg hA hB) (add_nonneg (atom1777Coded_nonneg g hg hA hB) (atom1778Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1779Coded_nonneg g hg hA hB) (atom1780Coded_nonneg g hg hA hB)) (add_nonneg (atom1781Coded_nonneg g hg hA hB) (add_nonneg (atom1782Coded_nonneg g hg hA hB) (atom1783Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1784Coded_nonneg g hg hA hB) (atom1785Coded_nonneg g hg hA hB)) (add_nonneg (atom1786Coded_nonneg g hg hA hB) (add_nonneg (atom1787Coded_nonneg g hg hA hB) (atom1788Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1789Coded_nonneg g hg hA hB) (atom1790Coded_nonneg g hg hA hB)) (add_nonneg (atom1791Coded_nonneg g hg hA hB) (add_nonneg (atom1792Coded_nonneg g hg hA hB) (atom1793Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1794Coded_nonneg g hg hA hB) (atom1795Coded_nonneg g hg hA hB)) (add_nonneg (atom1796Coded_nonneg g hg hA hB) (add_nonneg (atom1797Coded_nonneg g hg hA hB) (atom1798Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1799Coded_nonneg g hg hA hB) (atom1800Coded_nonneg g hg hA hB)) (add_nonneg (atom1801Coded_nonneg g hg hA hB) (add_nonneg (atom1802Coded_nonneg g hg hA hB) (atom1803Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1804Coded_nonneg g hg hA hB) (atom1805Coded_nonneg g hg hA hB)) (add_nonneg (atom1806Coded_nonneg g hg hA hB) (add_nonneg (atom1807Coded_nonneg g hg hA hB) (atom1808Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
